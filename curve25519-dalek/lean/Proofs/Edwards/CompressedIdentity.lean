module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Curve25519.Edwards.Encoding
public import Proofs.Helpers.ByteValues
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for CompressedEdwardsY`: the bytes `[1, 0, …, 0]`, value `1`. -/
@[step]
theorem identity_asNat :
    identity ⦃ (r : CompressedEdwardsY) => r.asNat = 1 ⦄ := by
  unfold identity
  step*
  simp [CompressedEdwardsY.asNat_def, Array.asNat_def, Array.make_val, Nat.ofDigits]

/-- `Identity for CompressedEdwardsY` is the encoding of the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : CompressedEdwardsY) => r.toVector = encode 0 ⦄ := by
  simp only [Curve25519Dalek.edwards.CompressedEdwardsY.toVector_eq_encode_iff]
  exact spec_mono identity_asNat fun r hr => by rw [hr, encodeNat_zero]

end Curve25519Dalek.edwards.CompressedEdwardsY.Insts.Curve25519_dalekTraitsIdentity
