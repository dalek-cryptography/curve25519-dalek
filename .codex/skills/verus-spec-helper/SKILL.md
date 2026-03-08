---
name: verus-spec-helper
description: Write, review, and tighten Verus specifications in verified Rust codebases. Use when drafting `spec fn`/`proof fn` specs, strengthening `requires`/`ensures`, connecting exec code to reference mathematical specs, minimizing refactors while preserving clear original-to-refactored correspondence, or managing ghost imports/cfg so `cargo build` and `cargo verus verify` both work.
---

# Verus Spec Helper

## Overview

Write reference-style (math-level) specifications and connect executable Rust code to those specs with tight, readable `requires`/`ensures` — without doing the full proofs yet (use `admit()` where needed).

A specification is formed of:
- `verus! { ... }` blocks wrapping spec and proof code
- `ensures` and `requires` clauses on exec functions
- Abstract `spec fn` definitions used in those clauses
- Making sure the code builds (`cargo build`) and verifies (`cargo verus verify`) with proof bypasses (`admit()`)

## Quick start

1. **Intent first**: what mathematical object/function does this code implement?
2. **Reuse existing vocab**: search the project's spec modules and external-modeling files before inventing new spec functions.
3. **Reference spec first**: add math definitions + key properties in a spec module, then attach exec code to it with `ensures`.
4. **Preserve correspondence**: small refactor blocks, `/* ORIGINAL CODE: ... */` nearby, function order preserved.
5. **Build hygiene**: isolate ghost code inside `verus! { ... }` blocks; avoid import/cfg churn.

## Spec writing goals (what "good" looks like)

- **Declarative** specs: relate inputs/outputs to reference spec functions (don't re-implement the algorithm in `ensures`).
- **Precise domain**: well-formedness, representation bounds, algebraic structure membership, length constraints.
- **Explicit intended property**: soundness, roundtrip, uniqueness, invariants preserved.
- **Readable doc comments** matching the style of existing spec modules.

## Spec function naming convention

| Category | Prefix | When to use | Examples |
|----------|--------|-------------|---------|
| **Exec-correspondence** | `spec_` | `ensures` target of an exec function | `spec_encrypt`, `spec_from_bytes` |
| **Pure math** | (none) | Math definitions, no direct exec counterpart | `group_add`, `field_mul`, `hash_digest` |
| **Validity predicates** | `is_` | Boolean well-formedness / membership tests | `is_valid_state`, `is_in_range`, `is_canonical` |
| **Axioms (admitted)** | `axiom_` | Proof functions with `admit()` body | `axiom_hash_injective` |
| **Lemmas (proved)** | `lemma_` | Fully proved proof functions | `lemma_decode_sound`, `lemma_roundtrip` |

## Spec function visibility rules

| Kind | When to use |
|------|-------------|
| `open spec fn` | Default. Body visible everywhere. |
| `closed spec fn` | Accesses `pub(crate)` fields, or uses `choose` that shouldn't expand |
| `uninterp spec fn` | External/opaque behavior with no formal definition |

When using `uninterp`, always pair with admitted axioms that state essential properties.

## Preconditions: `recommends` vs `requires`

| Clause | Meaning | Where used |
|--------|---------|------------|
| `requires` | Strict: violation = verification error | `proof fn`, `#[verifier::external_body]` exec fns |
| `recommends` | Soft: spec returns arbitrary value outside precondition | `spec fn` with optional well-definedness |

## Exec-to-spec bridging

Put exec correctness in one or two "load-bearing" postconditions. Keep algorithmic details out:

```rust
pub fn foo(x: Foo) -> (out: Bar)
    requires is_valid(x),
    ensures out@ == spec_foo(x@),
{
    /* ORIGINAL CODE: original_impl(x) */
    let result = verus_friendly_impl(x);
    proof { assert(out@ == spec_foo(x@)) by { admit() }; }
    result
}
```

### Proof bypass patterns

| Pattern | When to use |
|---------|-------------|
| `proof { admit(); }` | Defer entire function proof |
| `assert(...) by { admit() };` | Defer specific bridging assertion |
| `proof { assume(false); }` | Postpone loop body or complex block |
| `// PROOF BYPASS` comment | Always annotate admits — bare tag, no explanation |

### `external_body` patterns

| Pattern | When to use |
|---------|-------------|
| `#[verifier::external_body]` | Trusted functions: constants, iterators, external crates |
| `#[cfg_attr(verus_keep_ghost, verifier::external_body)]` | Generic/trait APIs; provide verified variant alongside |

## Correspondence rules (minimize refactors)

- Put the refactored/Verus-friendly version immediately after the original, one function at a time.
- If repetition appears in `ensures`, extract a small helper `spec fn`.

### When to add `/* ORIGINAL CODE: ... */` comments

Add an ORIGINAL CODE comment **only when the line was actually changed**.
The absence of a comment signals "unchanged".

### Common refactors that need tracking

| Original | Verus-friendly | Why |
|----------|---------------|-----|
| `Default::default()` | `[0u8; N]` or literal | Verus doesn't support `Default` trait |
| `for (i, x) in v.iter().enumerate()` | `for i in 0..v.len()` | Verus doesn't support iterators |
| `-x` (operator overload) | `negate_wrapper(&x)` | Operator overloading unsupported |
| `x.trait_method(args)` | `wrapper_fn(&mut x, args)` | Trait method calls unsupported |
| `dst[a..b].copy_from_slice(src)` | `write_range_wrapper(&mut dst, src)` | Slice range ops unsupported |
| `T::generic_call(args)` | `concrete_call(args)` | Generic trait calls unsupported |
| `x += expr` (compound assign) | `let tmp = expr; x = x + tmp;` | Split for overflow proof |
| Compound expression | Split with intermediate `let` | Needed to insert proof blocks |

## Doc comment conventions

### Module-level docs

Use `//!` (inner doc comments) with structured sections:
Mathematical objects, algorithm summary, what we specify, references.

### Function-level docs

- `///` consistently. First line: brief mathematical description.
- Body: numbered steps for algorithms, math formulas, RFC references.
- Don't cross-reference exec function names in spec docs.
- Don't describe exec algorithm strategy — keep it mathematical.

### Proof function naming

`axiom_` prefix for `admit()` bodies; `lemma_` for fully proved.

## Proof techniques

### `reveal` + `choose` for `closed spec fn`

When a `closed spec fn` uses `choose`, revealing it exposes the body to the SMT solver.
Use for soundness proofs (choose satisfies its predicate) and roundtrip proofs
(uniqueness forces choose to return the known value).

**Promoting axiom -> lemma**: when an `axiom_` turns out to be provable
via `reveal` or other techniques, rename to `lemma_` and replace `admit()` with the proof.

### Conditional `ensures` with `==>`

When a property depends on a structural possibility (e.g., collision-freedom),
make the `ensures` conditional rather than assuming it always holds.

### Compositional pipeline typing

Make function signatures compose directly — the output type of step N should be the
input type of step N+1.

## Ghost/import hygiene

- `use vstd::prelude::*;` goes **outside** `verus!` blocks at file top.
- Spec-only imports: guard with `#[cfg(verus_keep_ghost)]`.
- Prefer wildcard imports over specific named imports for spec modules.
- Always `#[allow(unused_imports)]` on spec imports.

## Requires/ensures checklist

### Preconditions

- Representation bounds + type invariants
- Algebraic structure membership
- Nonzero/invertible elements
- Valid encodings, permitted bit ranges
- Array lengths, indices in range
- Feature guards

### Postconditions

- Result matches reference spec operation
- Invariants preserved (well-formed, bounded, in valid domain)
- Encoding/decoding: soundness, roundtrip, uniqueness
- Length/shape constraints
- Avoid procedural ensures that restate the implementation

## Spec correctness pitfalls

### Quotient-level specs (equivalence classes)

When a map has a non-trivial kernel, inversion returns representatives from the
*equivalence class*, not the original element. Postconditions must allow any class
member, not assert equality with the input.

### Edge case separation in ensures

When a function has degenerate inputs (e.g., zero coordinates, identity element),
split the postcondition: exact guarantees for the generic case, weaker (but still
correct) guarantees for edge cases.

### Don't spec unverified failure behaviour

Only add a postcondition you are confident is correct. "Obvious" failure clauses
can be wrong when the implementation has early-exit branches that set the output
before the failure flag.

### `recommends` for partial functions

Spec functions with partial domains (division, square root, inversion) must guard
undefined inputs with `recommends`.

### Frame conditions on `external_body`

`external_body` specs must state what is *preserved*, not just what changes.
Missing frame conditions silently allow the verifier to assume arbitrary
modifications to unmentioned state.

## Validation

1. **Rust build**: `cargo build -p <crate>`
2. **Verus verify**: `cargo verus verify -p <crate>`
3. **Targeted verify**: `cargo verus verify -p <crate> -- --verify-module <module>`
4. **Error extraction**: `cargo verus verify -p <crate> 2>&1 | grep -E "^error|verification results:|^   --> |failed this" | head -30`

## Discovering project layout

When working on a new crate, search for these common directories and files:
- **Spec modules**: `specs/`, `*_specs.rs` — math-level definitions
- **External modeling**: `*_assumes.rs`, `core_assumes.rs` — uninterpreted functions and axioms
- **Lemma libraries**: `lemmas/` — proved and admitted proof functions
- **Constants**: `constants.rs`, `*_constants.rs` — domain-specific constants with type invariants
