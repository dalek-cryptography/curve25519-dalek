module
public import ForHumans.Specs.Ristretto
public import ForHumans.Specs.Montgomery
public import ForHumans.Specs.External.Alloc
public import ForHumans.Specs.External.Subtle.Contract
public import ForHumans.Specs.External.Zeroize.Contract
public import ForHumans.Specs.Representation

/-! # The specifications

The definitions that the theorems of `ForHumans/Theorems/` use, with no proofs. In import order:

* `Constants`, `Bytes`, `Field`: the constants of the RFCs, byte strings as numbers, the sign of a
  field element and `SQRT_RATIO_M1`;
* `Curves`, `Models`: edwards25519 and curve25519, the RFC 8032 encoding on any twisted Edwards
  model and the Ristretto relation;
* `Edwards`, `Montgomery`, `X25519`, `Ristretto`: the basepoints, the encodings and the functions of
  RFC 8032, RFC 7748 and RFC 9496;
* `Representation/`: the value of a Rust value;
* `External/`: the assumptions about the crates dalek calls. -/
