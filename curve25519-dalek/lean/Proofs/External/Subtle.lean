module
public import ForHumans.Specs.External.Subtle.Types
public import ForHumans.Specs.External.Subtle.Contract
public import Proofs.External.Subtle.Lemmas
public import Proofs.External.Subtle.Instances

/-! # The `subtle` crate

* `ForHumans/Specs/External/Subtle/Types.lean`, `ForHumans/Specs/External/Subtle/Contract.lean`:
  TRUSTED. Types, opaque signatures, spec axiom and faithful bodies.
* `Proofs/External/Subtle/Lemmas.lean`: derived generic results (no axioms).
* `Proofs/External/Subtle/Instances.lean`: derived results about the instances generated in
  `Curve25519Dalek/Funs.lean`.

The trait structures (`subtle.ConstantTimeEq`, …) are generated in `Curve25519Dalek/Types.lean`,
so this library depends on, and is specific to, the `Curve25519Dalek` translation.
-/
