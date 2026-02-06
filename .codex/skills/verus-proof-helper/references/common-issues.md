# Common issues and fixes

## “Expected Interp(Array), got Interp(FreeVar)”

Extract array elements to locals *before* entering `proof { ... }` blocks.

```rust
let byte31 = bytes[31];
proof {
    assert(byte31 < 128);
}
```

## “Cannot call function with mode exec”

Call exec functions outside `proof` blocks, bind the result, and reason about the value in `proof`.

```rust
let result = exec_function();
proof {
    // use `result`
}
```

## Less common / tool-specific issues

These are rarer, but can show up in verified-crypto codebases depending on Verus/vstd versions and
how specs are structured.

### Verus interpreter crash when using `by (compute)` over exec-derived values

Symptom: verifier crashes (e.g., interpreter panic / internal error) when `by (compute)` tries to
evaluate expressions that depend on exec variables or exec function calls (common in crypto code:
`invert()`, `sqrt_ratio_i`, `spec_field_element(&x)` where `x` is exec).

Fixes:

- Avoid `by (compute)` on expressions involving exec variables.
- Move exec calls outside proofs (bind to locals), then reason about *postconditions* / bounds.
- Prefer `bit_vector`, targeted lemmas, or small `assert forall` blocks instead of `compute`.

### Verus internal error / rust_to_vir panic on unary `-` for some types

Symptom: Verus panics (internal compiler error) when using unary negation `-x` on certain
wrapper types (seen with field element newtypes in verified crypto).

Workarounds:

- Use an explicit “conditional negate” wrapper (e.g., `conditional_negate_field_element(&mut x, Choice::from(1u8))`)
  instead of `-x`.
- Or rewrite as `0 - x` if `Sub` is verified and does not trigger the same issue.

## “Nested proof blocks not supported”

Flatten proof structure. Do not nest `proof { proof { ... } }`.

## Assertion fails “without details”

Add intermediate assertions to narrow the failing sub-goal.

```rust
assert(step_1);
assert(step_2);
assert(step_3);
assert(complex_property);
```

## `vstd` imports fail in regular `cargo build` / `clippy`

Guard ghost-only imports with `#[cfg(verus_keep_ghost)]`:

```rust
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{lemma2_to64, lemma_pow2_adds, pow2};
```

## Imports from `common_lemmas::*` fail in non-Verus builds

Many items are generated inside `verus!` blocks and do not exist in non-Verus builds. Prefer wildcard imports and allow unused imports:

```rust
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::div_mod_lemmas::*;
```

## Redundant imports inside proof blocks

If the module already has top-level wildcard imports, do not add specific imports inside `proof` blocks; just call the lemma by its short name.

## Quantifiers do not instantiate (“forall ensures …” not used)

Add a small, explicit `assert(...)` with the right trigger shape right before the statement that needs it. Often extracting expressions to locals helps match triggers.

## SMT `rlimit` / timeouts

Common mitigations:

- Keep loop invariants small; avoid unfolding big `&&&`-heavy specs in invariants.
- Mark expensive `spec fn` predicates `#[verifier::opaque]` and `reveal(...)` only locally in helper lemmas.
- Prefer adding a targeted helper lemma that extracts the single conjunct/fact you need, rather than revealing a whole predicate at the call site.

### `Option::expect` / `unwrap` requires `is_some()` (vstd spec friction)

Sometimes the vstd spec for `expect`/`unwrap` forces a precondition like `opt.is_some()`, which
turns into an `assume(...)` in application code.

Workaround: avoid calling `expect` in verified code; do an explicit `match` and preserve exec
behavior (panic) with `#[cfg(not(verus_keep_ghost))]`, while using a well-formed placeholder value
under `#[cfg(verus_keep_ghost)]`. Keep the original code in a `/* ORIGINAL CODE: ... */` comment.
