# Spec workflow (Verus + crypto Rust)

## 1) Start from intent, not code

- Identify the mathematical object and claim (field op, group op, encoding/decoding relation, hash-to-bytes model).
- Decide what “correct” means at the math level (a function, a relation, or a partial function).

## 2) Write/extend a reference spec first

- Prefer a reference spec module under `src/specs/*_specs.rs` that defines:
  - Domain objects (e.g., `(nat, nat)` affine points, `nat` field elements, `Seq<u8>` encodings).
  - Operations (e.g., `add`, `mul`, `encode`, `decode`).
  - Validity predicates/invariants (curve equation, bounds, subgroup membership, canonical encodings).
- Keep this layer *declarative*: define math functions/relations; avoid mirroring the exec algorithm.
- Document notation and structures in module-level comments (match the style of existing spec modules).

## 3) Link exec code to the reference spec

- Add `requires` that make exec operations well-defined (bounds, nonzero denominators, well-formed points, feature guards).
- Add `ensures` that connect the returned value to the reference spec (often one primary ensures is better than many procedural ones).
- If you can’t prove a bridge yet, introduce an admitted lemma/axiom with a descriptive name and use it from the exec spec.

## 4) Preserve correspondence (minimize refactors)

- Keep function order aligned with upstream/original files.
- Refactor in small chunks and keep `/* ORIGINAL CODE: ... */` to ~1–2 lines near the change.
- Prefer helper functions over restructuring loops/branches when the goal is only “make it verifiable/specifiable”.

## 5) Keep ghost/imports readable and buildable

- Put ghost-only items/imports inside `verus! { ... }` blocks.
- Avoid sprinkling `#[cfg(verus_keep_ghost)]` on individual items unless necessary (IDE dimming + import churn).
- Prefer fully-qualified paths in `ensures` over additional `use` lines that only exist for specs.

## 6) Review + validate

- Do a “spec review pass”:
  - Preconditions sufficient for every operation used?
  - Postconditions express the intended math claim (not an implementation trace)?
  - Any repeated `ensures` that should be a helper `spec fn`?
- Run both:
  - `cargo build -p curve25519-dalek`
  - `cargo verus verify -p curve25519-dalek`
