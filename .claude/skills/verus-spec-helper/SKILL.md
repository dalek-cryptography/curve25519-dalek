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

1. **Intent first**: what mathematical object/function does this code implement (arithmetic, group law, encoding/decoding, hash, data structure invariant)?
2. **Reuse existing vocab**: search the project's spec modules and external-modeling files before inventing new spec functions.
3. **Reference spec first**: add math definitions + key properties in a spec module, then attach exec code to it with `ensures`.
4. **Preserve correspondence**: small refactor blocks, `/* ORIGINAL CODE: ... */` nearby, function order preserved.
5. **Build hygiene**: isolate ghost code inside `verus! { ... }` blocks; avoid import/cfg churn.

## Spec writing goals (what "good" looks like)

- **Declarative** specs: relate inputs/outputs to reference spec functions (don't re-implement the algorithm in `ensures`).
- **Precise domain**: well-formedness, representation bounds, algebraic structure membership, invertibility/nonzero denominators, length constraints.
- **Explicit intended property**: soundness, roundtrip, uniqueness, invariants preserved.
- **Readable doc comments** matching the style of existing spec modules.

## Reference spec module structure

Co-locate math definitions in dedicated spec modules (e.g., `src/specs/<topic>_specs.rs`). Structure:

```rust
//! Specifications for <topic>.
//!
//! ## Mathematical objects and notation
//!
//! - describe domain objects, notation, representations
//!
//! ## <Pipeline / Algorithm summary>
//!
//! brief overview of the composition chain
//!
//! ## What we specify here
//!
//! - list of what is spec'd and what is deferred
//!
//! ## References
//!
//! - citations to papers, RFCs, executable code modules

#[allow(unused_imports)]
use super::<domain>_specs::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// Section Title
// =============================================================================

/// Top-level spec for `exec_encode`.
pub open spec fn spec_encode(data: Seq<u8>) -> (nat, nat) { /* math */ }

/// Pure math helper — no `spec_` prefix (not an exec-correspondence).
pub open spec fn intermediate_step(data: Seq<u8>) -> nat { /* math */ }

/// Validity predicate for domain object.
pub open spec fn is_valid(x: AbstractType) -> bool { /* invariants */ }

} // verus!
```

## Spec function naming convention

| Category | Prefix | When to use | Examples |
|----------|--------|-------------|---------|
| **Exec-correspondence** | `spec_` | Function whose primary role is the `ensures` target of an exec function | `spec_encrypt`, `spec_from_bytes`, `spec_compress` |
| **Pure math** | (none) | Mathematical definitions, pipeline intermediates, predicates — no direct exec counterpart | `group_add`, `field_mul`, `hash_digest`, `pipeline_step_a` |
| **Validity predicates** | `is_` | Boolean well-formedness / membership tests | `is_valid_state`, `is_in_range`, `is_on_curve`, `is_canonical` |
| **Axioms (admitted)** | `axiom_` | Proof functions with `admit()` body | `axiom_hash_injective`, `axiom_add_complete` |
| **Lemmas (proved)** | `lemma_` | Fully proved proof functions | `lemma_decode_sound`, `lemma_roundtrip`, `lemma_from_bytes_as_nat` |

## Spec function visibility rules

| Kind | When to use | Examples |
|------|-------------|---------|
| `open spec fn` | Default. Body visible everywhere. | `group_add`, `field_mul`, `spec_encrypt` |
| `closed spec fn` | Encapsulation needed: accesses `pub(crate)` fields, or uses `choose` that shouldn't expand | struct accessors, `spec_decode` |
| `uninterp spec fn` | External/opaque behavior with no formal definition | `spec_sha256`, `spec_aes_encrypt` |

When using `uninterp`, always pair with admitted axioms that state essential properties:

```rust
pub uninterp spec fn spec_hash(input: Seq<u8>) -> Seq<u8>;

pub proof fn axiom_hash_output_length(input: Seq<u8>)
    ensures spec_hash(input).len() == 32,
{ admit(); }
```

## Preconditions: `recommends` vs `requires`

| Clause | Meaning | Where used |
|--------|---------|------------|
| `requires` | Strict: violation = verification error | `proof fn`, `#[verifier::external_body]` exec fns |
| `recommends` | Soft: spec may return arbitrary value outside precondition | `spec fn` with optional well-definedness |

Use `recommends` on spec functions when the precondition is always true in practice but not structurally enforced:

```rust
pub open spec fn decode_step(data: Seq<u8>) -> nat
    recommends data.len() == 32,
```

## Exec-to-spec bridging

Put exec correctness in one or two "load-bearing" postconditions. Keep algorithmic details out:

```rust
pub fn foo(x: Foo) -> (out: Bar)
    requires
        is_valid(x),
    ensures
        out@ == spec_foo(x@),
{
    /* ORIGINAL CODE: original_impl(x) */
    let result = verus_friendly_impl(x);
    proof {
        assert(out@ == spec_foo(x@)) by { admit() };  // PROOF BYPASS
    }
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

Style: use just `// PROOF BYPASS` (no trailing explanation). The `assert(...)` it precedes
is self-documenting. Consolidate multiple asserts into a single `match` when they share
the same discriminant (mirrors the `ensures` structure).

### `external_body` patterns

| Pattern | When to use |
|---------|-------------|
| `#[verifier::external_body]` | Trusted functions: constants, iterators, external crates |
| `#[cfg_attr(verus_keep_ghost, verifier::external_body)]` | Generic/trait APIs; provide verified variant alongside |

```rust
// Generic version: trusted (Verus can't handle the trait bound)
#[cfg_attr(verus_keep_ghost, verifier::external_body)]
pub fn transform<D: SomeTrait>(data: &[u8; 16]) -> Output { ... }

// Concrete version: verified
pub fn transform_verus(data: &[u8; 16]) -> (result: Output)
    ensures result@ == spec_transform(data@),
{ ... }
```

## Correspondence rules (minimize refactors)

- Put the refactored/Verus-friendly version immediately after the original, one function at a time.
- If repetition appears in `ensures`, extract a small helper `spec fn`.

### When to add `/* ORIGINAL CODE: ... */` comments

Add an ORIGINAL CODE comment **only when the line was actually changed**.
Lines that are identical to the original get no comment — the absence of a
comment signals "unchanged".

```rust
// Changed: iterator → index loop
/* ORIGINAL CODE: for (j, item) in items.iter().enumerate() { */
for j in 0..8 {
    // Unchanged — no comment needed
    let mut ok = check(j);
    // Changed: iterator binding replaced by direct indexing
    /* ORIGINAL CODE: let val = item.process(); */
    let val = items[j].process();
```

Keep comments to ~1 line showing the original expression. Avoid pasting
multi-line blocks — just show the changed expression.

### Common refactors that need tracking

| Original | Verus-friendly | Why |
|----------|---------------|-----|
| `Default::default()` | `[0u8; N]` or literal | Verus doesn't support `Default` trait |
| `for (i, x) in v.iter().enumerate()` | `for i in 0..v.len()` | Verus doesn't support iterators |
| Iterator binding (`item`) | Direct indexing (`items[j]`) | Consequence of iterator removal |
| `-x` (operator overload) | `negate_wrapper(&x)` | Operator overloading unsupported in `verus!` |
| `a \| b` (trait-based ops) | `or_wrapper(a, b)` | Operator overloading unsupported |
| `x.trait_method(args)` | `wrapper_fn(&mut x, args)` | Trait method calls unsupported |
| `dst[a..b].copy_from_slice(src)` | `write_range_wrapper(&mut dst, src)` | Slice range ops unsupported |
| `T::generic_call(args)` | `concrete_call(args)` | Generic trait calls unsupported |
| `x += expr` (compound assign) | `let tmp = expr; x = x + tmp;` | Needed to insert proof blocks or type coercions |
| Compound expression | Split with intermediate `let` | Needed to insert proof blocks |

## Doc comment conventions

### Module-level docs

Use `//!` (inner doc comments) with structured sections:

```rust
//! Specifications for <topic>.
//!
//! ## Mathematical objects and notation
//! - describe objects, domains, representations
//!
//! ## <Algorithm / Pipeline summary>
//! brief composition chain or key formulas
//!
//! ## What we specify here
//! - list of specs provided and deferred work
//!
//! ## References
//! - papers, RFCs, links to exec code
```

### Function-level docs

- Use `///` consistently.
- First line: brief mathematical description (what, not how).
- Body: numbered steps for algorithms, math formulas, RFC references.
- Don't cross-reference exec function names in spec docs (those belong on the exec function or module overview).
- Don't describe exec algorithm strategy in spec docs — keep it mathematical.

```rust
/// The intermediate digest `b(m)` — first stage of the pipeline.
///
/// ```text
/// m ──► [b(m)] ──► r(m) ──► P(m)
///        ^^^^
/// ```
///
/// 1. `digest = H(m)` (32 bytes)
/// 2. Overwrite `digest[8..24]` with `m` — embeds the recoverable payload
/// 3. Mask high/low bits for canonical range
```

### Inline body comments

Terse mathematical annotations, not narration:

```rust
let digest = spec_hash(data);                           // H(m), 32 bytes
let s = s.update(0, s[0] & 254u8);                     // clear low bit
```

### Section separators

```rust
// =============================================================================
// Section Title
// =============================================================================
```

### Proof function docs

```rust
/// **Soundness**: `decode(P) == Some(m)  ==>  encode(m) == P`.
pub proof fn lemma_decode_sound(...)

/// **Roundtrip**: `decode(encode(m)) == Some(m)` when no collision.
pub proof fn lemma_roundtrip(...)
```

Naming: `axiom_` prefix for `admit()` bodies; `lemma_` for fully proved.
See naming convention table above for full prefix rules.

## Proof techniques

### `reveal` + `choose` for `closed spec fn`

When a `closed spec fn` uses `choose`, revealing it exposes the body to the SMT solver.
The solver can then exploit the `choose` axiom: if `exists|x| P(x)` then `P(choose|x| P(x))`.

If the predicate `P` includes a uniqueness clause (`forall|y| Q(y) ==> y == x`), the solver
can conclude `choose == known_value` when you assert the known value satisfies the predicate.

**Pattern — soundness** (choose satisfies its predicate):
```rust
pub proof fn lemma_decode_sound(point: AbstractPoint, data: Seq<u8>)
    ensures
        spec_decode(point) == Some(data) ==> spec_encode(data) == point,
{
    reveal(spec_decode);
    // Solver sees: data = choose|d| is_preimage(d, point) && ...
    // choose axiom: is_preimage(data, point), i.e. encode(data) == point
}
```

**Pattern — roundtrip** (uniqueness forces choose to return the known value):
```rust
pub proof fn lemma_roundtrip(data: Seq<u8>)
    requires data.len() == 16,
    ensures
        has_unique_preimage(spec_encode(data))
            ==> spec_decode(spec_encode(data)) == Some(data),
{
    reveal(spec_decode);
    assert(is_preimage(data, spec_encode(data)));
    // Solver: data satisfies predicate, uniqueness clause forces choose == data
}
```

**Promoting axiom -> lemma**: when an `axiom_` (with `admit()`) turns out to be provable
via `reveal` or other techniques, rename to `lemma_` and replace `admit()` with the proof.

**Proof reuse across duplicate functions**: when a wrapper/variant does the same exec steps
as an already-proved function, copy the proof block rather than using `admit()`.

### Conditional `ensures` with `==>`

When a property depends on a structural possibility (e.g., collision-freedom, unique preimage),
make the `ensures` conditional rather than assuming it always holds:

```rust
ensures
    has_unique_preimage(spec_encode(data))
        ==> spec_decode(spec_encode(data)) == Some(data),
```

This is stronger than requiring `has_unique_preimage` as a precondition: the lemma
is universally quantified, and the caller decides when the antecedent holds.

### Compositional pipeline typing

Make function signatures compose directly — the output type of step N should be the
input type of step N+1:

```rust
pub open spec fn step_bytes(data: Seq<u8>) -> [u8; 32] { ... }
pub open spec fn step_nat(bytes: &[u8; 32]) -> nat { ... }
pub open spec fn spec_encode(data: Seq<u8>) -> (nat, nat) {
    final_map(step_nat(&step_bytes(data)))   // direct composition
}
```

## Ghost/import hygiene

- `use vstd::prelude::*;` goes **outside** `verus!` blocks at file top.
- Spec-only imports from `vstd::` or internal spec modules: guard with `#[cfg(verus_keep_ghost)]`.
- Prefer wildcard imports (`use crate::specs::<module>::*;`) over specific named imports for spec modules — wildcards compile even when the module is empty in non-Verus builds.
- Always `#[allow(unused_imports)]` on spec imports.
- Imports used only inside `verus! { ... }` can go inside the block.

```rust
#[allow(unused_imports)]
use crate::specs::domain_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

verus! {
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::core_specs::{bytes_as_nat, seq_as_nat};

// ... specs ...
} // verus!
```

## Requires/ensures checklist

### Preconditions

- Representation bounds + type invariants (e.g., limb bounds, canonicality)
- Algebraic structure membership (e.g., on-curve, in-subgroup)
- Nonzero/invertible elements for divisions
- Valid encodings, permitted bit ranges
- Array lengths, indices in range
- Feature guards (`cfg(feature = "...")`)

### Postconditions

- Result matches reference spec operation
- Invariants preserved (well-formed, bounded, in valid domain)
- Encoding/decoding: **soundness** (`decode(bytes) == Some(m)` implies preimage), **roundtrip** (`decode(encode(m)) == Some(m)`), uniqueness
- Length/shape constraints on outputs
- Avoid procedural ensures that restate the implementation
- Annotate postcondition groups inline with short comments:
  ```rust
  ensures
      match result {
          Some(p) =>
              // Well-formedness
              is_valid(p)
              // Correctness
              && to_abstract(p) == spec_fn(...),
          None => ...,
      },
  ```

## Spec correctness pitfalls

### Quotient-level specs (equivalence classes)

When a map has a non-trivial kernel (e.g., group quotients, cosets, equivalence classes),
inversion returns representatives from the *equivalence class*, not the original element.
Postconditions must allow any class member, not assert equality with the input:

```rust
// WRONG: claims inverse maps back to the original
ensures inverse(result) == self,

// CORRECT: claims inverse maps to some member of the equivalence class
ensures exists_in_class(inverse(result), equivalence_class(self)),
```

### Edge case separation in ensures

When a function has degenerate inputs (e.g., zero coordinates, identity element),
split the postcondition: exact guarantees for the generic case, weaker (but still
correct) guarantees for edge cases:

```rust
ensures
    // Generic: exact bijection
    generic_condition ==> exact_correspondence(input, result),
    // Degenerate: weaker membership guarantee
    !generic_condition ==> result_in_valid_set(result),
```

### Don't spec unverified failure behaviour

Only add a postcondition you are confident is correct. "Obvious" failure clauses
(e.g., `failed ==> output == default_value`) can be wrong when the implementation
has early-exit branches that set the output before the failure flag.

### `recommends` for partial functions

Spec functions with partial domains (division, square root, inversion) must guard
undefined inputs with `recommends`:

```rust
pub open spec fn affine_from_projective(x: nat, z: nat) -> nat
    recommends z != 0,
```

### Frame conditions on `external_body`

`external_body` specs must state what is *preserved*, not just what changes.
Missing frame conditions silently allow the verifier to assume arbitrary
modifications to unmentioned state:

```rust
// INCOMPLETE: only says what's written — verifier can assume other bytes are anything
ensures forall|i: int| 0 <= i < n ==> dst[(off+i) as int] == src[i],

// COMPLETE: also constrains unchanged bytes
ensures
    forall|i: int| 0 <= i < n ==> dst[(off+i) as int] == src[i],
    forall|i: int| (0 <= i < off || off+n <= i < len) ==> dst[i] == old(dst)[i],
```

## Validation

1. **Rust build**: `cargo build -p <crate>`
2. **Verus verify**: `cargo verus verify -p <crate>`
3. **Targeted verify** (faster): `cargo verus verify -p <crate> -- --verify-module <module>`
4. **Error extraction**: `cargo verus verify -p <crate> 2>&1 | grep -E "^error|verification results:|^   --> |failed this" | head -30`

Run both build and verify after spec changes. When verification succeeds, `cargo verus verify ... 2>&1 | tail -5` suffices.

## Discovering project layout

When working on a new crate, search for these common directories and files:
- **Spec modules**: `specs/`, `*_specs.rs` — math-level definitions
- **External modeling**: `*_assumes.rs`, `core_assumes.rs` — uninterpreted functions and axioms
- **Lemma libraries**: `lemmas/` — proved and admitted proof functions
- **Constants**: `constants.rs`, `*_constants.rs` — domain-specific constants with type invariants
