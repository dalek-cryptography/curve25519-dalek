module
public import Subtle.Types
public import Subtle.Contract
public import Subtle.Lemmas
public import Subtle.Instances

/-! # The `subtle` crate

* `Subtle/Types.lean`, `Subtle/Contract.lean`: TRUSTED. Types, opaque signatures, spec axiom and
  faithful bodies.
* `Subtle/Lemmas.lean`: derived generic results (no axioms).
* `Subtle/Instances.lean`: derived results about the instances generated in
  `Curve25519Dalek/Funs.lean`.

The trait structures (`subtle.ConstantTimeEq`, …) are generated in `Curve25519Dalek/Types.lean`,
so this library depends on, and is specific to, the `Curve25519Dalek` translation.
-/
