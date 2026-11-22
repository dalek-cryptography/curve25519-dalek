/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ForHumans.Specs.Representation.Montgomery
import all ForHumans.Specs.Representation.Montgomery
public import Proofs.Curve25519.X25519
public import Proofs.Representation.Array
public import Proofs.Representation.FieldElement2625
public import Proofs.Representation.FieldElement51
public section

/-! # `montgomery.rs`: the `u`-coordinate bytes and the ladder's projective points (audited)

`MontgomeryPoint` is 32 bytes; `toVector` (`Proofs/ToAeneas/Array.lean`) gives them as a
`Vector UInt8 32`, the byte string of RFC 7748, whose `u`-coordinate is RFC 7748
`decodeUCoordinate`.

`ProjectivePoint (U : W)` is the `x`-only projective point of the Montgomery ladder: `toXZ` maps
it to `MontgomeryModel.XZ (ZMod p)`, whose `toU` is `U / W` (`0` at `W = 0`, as `as_affine`).
`LimbsLt n` says every limb is `< 2^n`; the 64-bit specs use `LimbsLt 52`: the code's
`differential_add_and_double` adds two coordinates before squaring or multiplying them, so it
needs limbs `< 2^53`, and every producer (`identity`, `from_bytes`, the `mul`/`square` outputs of
the ladder step) gives `< 2^52`. -/

open Aeneas Aeneas.Std curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.montgomery

/-! ### `MontgomeryPoint` -/

/-! ### `ProjectivePoint` -/

namespace ProjectivePoint.«64bit-tables»

/-- The projective `u`-line point `(U : W)` as field elements. -/
noncomputable def toXZ (self : ProjectivePoint.«64bit-tables») : MontgomeryModel.XZ (ZMod p) :=
  ⟨self.U.toField, self.W.toField⟩

theorem toXZ_def (self : ProjectivePoint.«64bit-tables») :
    self.toXZ = ⟨self.U.toField, self.W.toField⟩ := by
  unfold toXZ
  rfl

/-- Every limb of a Montgomery `ProjectivePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectivePoint.«64bit-tables») : Prop :=
  self.U.LimbsLt n ∧ self.W.LimbsLt n

end ProjectivePoint.«64bit-tables»

namespace ProjectivePoint.«32bit-tables»

/-- The projective `u`-line point `(U : W)` as field elements. -/
noncomputable def toXZ (self : ProjectivePoint.«32bit-tables») : MontgomeryModel.XZ (ZMod p) :=
  ⟨self.U.toField, self.W.toField⟩

theorem toXZ_def (self : ProjectivePoint.«32bit-tables») :
    self.toXZ = ⟨self.U.toField, self.W.toField⟩ := by
  unfold toXZ
  rfl

/-- Every limb of a Montgomery `ProjectivePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectivePoint.«32bit-tables») : Prop :=
  self.U.LimbsLt n ∧ self.W.LimbsLt n

end ProjectivePoint.«32bit-tables»

namespace ProjectivePoint.«64bit-notables»

/-- The projective `u`-line point `(U : W)` as field elements. -/
noncomputable def toXZ (self : ProjectivePoint.«64bit-notables») :
    MontgomeryModel.XZ (ZMod p) :=
  ⟨self.U.toField, self.W.toField⟩

theorem toXZ_def (self : ProjectivePoint.«64bit-notables») :
    self.toXZ = ⟨self.U.toField, self.W.toField⟩ := by
  unfold toXZ
  rfl

/-- Every limb of a Montgomery `ProjectivePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectivePoint.«64bit-notables») : Prop :=
  self.U.LimbsLt n ∧ self.W.LimbsLt n

end ProjectivePoint.«64bit-notables»

namespace ProjectivePoint.«32bit-notables»

/-- The projective `u`-line point `(U : W)` as field elements. -/
noncomputable def toXZ (self : ProjectivePoint.«32bit-notables») :
    MontgomeryModel.XZ (ZMod p) :=
  ⟨self.U.toField, self.W.toField⟩

theorem toXZ_def (self : ProjectivePoint.«32bit-notables») :
    self.toXZ = ⟨self.U.toField, self.W.toField⟩ := by
  unfold toXZ
  rfl

/-- Every limb of a Montgomery `ProjectivePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectivePoint.«32bit-notables») : Prop :=
  self.U.LimbsLt n ∧ self.W.LimbsLt n

end ProjectivePoint.«32bit-notables»

end Curve25519Dalek.montgomery
