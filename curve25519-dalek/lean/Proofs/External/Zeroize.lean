module
public import Proofs.External.Zeroize.Contract
public import Proofs.External.Zeroize.Lemmas
public import Proofs.External.Zeroize.Instances

/-! # The `zeroize` crate (zeroize-1.8.2)

* `ForHumans/Specs/External/Zeroize/Contract.lean`: TRUSTED. Opaque signatures and spec axiom.
  `Curve25519Dalek/Funs.lean` imports it.
* `Proofs/External/Zeroize/Lemmas.lean`: derived generic results (no axioms).
* `Proofs/External/Zeroize/Instances.lean`: derived results about the instances generated in
  `Curve25519Dalek/Funs.lean`.

The trait structures (`zeroize.Zeroize`, `zeroize.DefaultIsZeroes`) are generated in
`Curve25519Dalek/Types.lean`, so this library depends on, and is specific to, the
`Curve25519Dalek` translation.
-/
