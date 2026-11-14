module
public import Proofs.External.Zeroize.Contract
public import Proofs.External.Zeroize.Lemmas
public import Proofs.External.Zeroize.Instances

/-! # The `zeroize` crate (zeroize-1.8.2): derived results

The trusted part, the signatures, contracts and axiom, is in
`ForHumans/Specs/External/Zeroize/Contract.lean`. Here: the contracts as theorems
(`Contract.lean`), generic lemmas (`Lemmas.lean`) and results about the instances generated in
`Curve25519Dalek/Funs.lean` (`Instances.lean`). -/
