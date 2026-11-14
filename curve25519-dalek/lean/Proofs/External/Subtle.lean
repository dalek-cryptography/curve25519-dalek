module
public import ForHumans.Specs.External.Subtle.Types
public import Proofs.External.Subtle.Contract
public import Proofs.External.Subtle.Lemmas
public import Proofs.External.Subtle.Instances

/-! # The `subtle` crate: derived results

The trusted part, the types, signatures, contracts and axiom, is in
`ForHumans/Specs/External/Subtle/`. Here: the contracts as theorems (`Contract.lean`), generic
lemmas (`Lemmas.lean`) and results about the instances generated in `Curve25519Dalek/Funs.lean`
(`Instances.lean`). -/
