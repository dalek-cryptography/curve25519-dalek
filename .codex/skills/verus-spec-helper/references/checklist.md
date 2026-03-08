# Spec completeness checklist (requires/ensures)

Use this as a “review pass” checklist when you think you’re done.

## Preconditions (requires)

- Representation well-formedness
  - Limb bounds / canonicality assumptions (if needed).
  - Type invariants required by helper lemmas or operator specs.
- Algebraic domain assumptions
  - Curve membership / curve equation.
  - Prime-subgroup vs torsion/coset assumptions.
  - Nonzero denominators / invertibility assumptions for divisions/inversions.
- Input shape constraints
  - Array lengths, indices in range, slices sized correctly.
  - Encoding constraints (canonical bytes, permitted top bits, etc.).
- Feature/environment guards
  - `cfg(feature = "...")` requirements when calling feature-gated code.

## Postconditions (ensures)

- Primary correctness claim
  - Result equals the reference spec operation (or satisfies the reference relation).
  - If modeling a partial function (decode), use `Option` or an explicit predicate.
- Invariants preserved
  - Output remains well-formed/bounded.
  - Output stays on-curve / in subgroup (if applicable).
- Encoding/decoding specific
  - **Soundness**: if `decode(bytes) == Some(m)`, then `bytes` is in the spec-defined preimage of `m`.
  - **Roundtrip**: `decode(encode(m)) == Some(m)` (and uniqueness if the design requires it).
  - Length/shape of outputs (e.g., fixed-size arrays).
- “No surprises”
  - Avoid claiming constant-time / side-channel properties in specs unless you actually plan to verify them.
  - Avoid overly procedural ensures that only restate the implementation.
