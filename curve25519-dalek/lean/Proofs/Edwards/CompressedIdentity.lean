/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Curve25519.Edwards.Encoding
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for CompressedEdwardsY`: the bytes `[1, 0, …, 0]`, value `1`. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : CompressedEdwardsY) => r.asNat = 1 ⦄ := by
  unfold identity
  step*
  simp [CompressedEdwardsY.asNat_def, Array.asNat_def, Array.make_val, Nat.ofDigits]

/-- `Identity for CompressedEdwardsY` is the encoding of the neutral element. -/
theorem identity_spec_point :
    identity ⦃ (r : CompressedEdwardsY) => r.asNat = encode 0 ⦄ :=
  spec_mono identity_spec fun r hr => by rw [hr, encode_zero]

end Curve25519Dalek.edwards.CompressedEdwardsY.Insts.Curve25519_dalekTraitsIdentity
