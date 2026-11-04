/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Defs.FieldElement2625
public import Defs.FieldElement51
public section

/-! # `montgomery.rs`: the `u`-coordinate bytes and the ladder's projective points (audited)

`MontgomeryPoint` is 32 bytes: `asNat` is their little-endian value and `u` the `u`-coordinate
they encode, RFC 7748 `decodeUCoordinate` (`curve25519.decodeU`: bit `255` masked, reduced
modulo `p`). A canonical output has `asNat < p` (`to_bytes`).

`ProjectivePoint (U : W)` is the `x`-only projective point of the Montgomery ladder: `toXZ` maps
it to `MontgomeryModel.XZ (ZMod p)`, whose `toU` is `U / W` (`0` at `W = 0`, as `as_affine`).
`LimbsLt n` says every limb is `< 2^n`; the x86_64 specs use `LimbsLt 52`: the code's
`differential_add_and_double` adds two coordinates before squaring or multiplying them, so it
needs limbs `< 2^53`, and every producer (`identity`, `from_bytes`, the `mul`/`square` outputs of
the ladder step) gives `< 2^52`. -/

open Aeneas Aeneas.Std curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.montgomery

/-! ### `MontgomeryPoint` -/

/-- The little-endian value of the 32 bytes. -/
def MontgomeryPoint.asNat (self : MontgomeryPoint) : ℕ :=
  Aeneas.Std.Array.asNat 8 self

theorem MontgomeryPoint.asNat_def (self : MontgomeryPoint) :
    self.asNat = Aeneas.Std.Array.asNat 8 self := by
  unfold MontgomeryPoint.asNat
  rfl

/-- Needed for `v[i]!` on vectors of points; the default is never observed for in-range
indices. -/
instance MontgomeryPoint.instInhabited : Inhabited MontgomeryPoint :=
  inferInstanceAs (Inhabited (Array U8 32#usize))

/-- The `u`-coordinate encoded by the bytes: RFC 7748 `decodeUCoordinate`, i.e. the value of
the low `255` bits modulo `p`. -/
def MontgomeryPoint.u (self : MontgomeryPoint) : ZMod p :=
  decodeU self.asNat

theorem MontgomeryPoint.u_def (self : MontgomeryPoint) : self.u = decodeU self.asNat := by
  unfold MontgomeryPoint.u
  rfl

/-! ### `ProjectivePoint` -/

namespace ProjectivePoint.«x86_64-tables»

/-- The projective `u`-line point `(U : W)` as field elements. -/
noncomputable def toXZ (self : ProjectivePoint.«x86_64-tables») : MontgomeryModel.XZ (ZMod p) :=
  ⟨self.U.toField, self.W.toField⟩

theorem toXZ_def (self : ProjectivePoint.«x86_64-tables») :
    self.toXZ = ⟨self.U.toField, self.W.toField⟩ := by
  unfold toXZ
  rfl

/-- Every limb of a Montgomery `ProjectivePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectivePoint.«x86_64-tables») : Prop :=
  self.U.LimbsLt n ∧ self.W.LimbsLt n

end ProjectivePoint.«x86_64-tables»

namespace ProjectivePoint.«i686-tables»

/-- The projective `u`-line point `(U : W)` as field elements. -/
noncomputable def toXZ (self : ProjectivePoint.«i686-tables») : MontgomeryModel.XZ (ZMod p) :=
  ⟨self.U.toField, self.W.toField⟩

theorem toXZ_def (self : ProjectivePoint.«i686-tables») :
    self.toXZ = ⟨self.U.toField, self.W.toField⟩ := by
  unfold toXZ
  rfl

/-- Every limb of a Montgomery `ProjectivePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectivePoint.«i686-tables») : Prop :=
  self.U.LimbsLt n ∧ self.W.LimbsLt n

end ProjectivePoint.«i686-tables»

namespace ProjectivePoint.«x86_64-no-tables»

/-- The projective `u`-line point `(U : W)` as field elements. -/
noncomputable def toXZ (self : ProjectivePoint.«x86_64-no-tables») :
    MontgomeryModel.XZ (ZMod p) :=
  ⟨self.U.toField, self.W.toField⟩

theorem toXZ_def (self : ProjectivePoint.«x86_64-no-tables») :
    self.toXZ = ⟨self.U.toField, self.W.toField⟩ := by
  unfold toXZ
  rfl

/-- Every limb of a Montgomery `ProjectivePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectivePoint.«x86_64-no-tables») : Prop :=
  self.U.LimbsLt n ∧ self.W.LimbsLt n

end ProjectivePoint.«x86_64-no-tables»

namespace ProjectivePoint.«i686-no-tables»

/-- The projective `u`-line point `(U : W)` as field elements. -/
noncomputable def toXZ (self : ProjectivePoint.«i686-no-tables») :
    MontgomeryModel.XZ (ZMod p) :=
  ⟨self.U.toField, self.W.toField⟩

theorem toXZ_def (self : ProjectivePoint.«i686-no-tables») :
    self.toXZ = ⟨self.U.toField, self.W.toField⟩ := by
  unfold toXZ
  rfl

/-- Every limb of a Montgomery `ProjectivePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectivePoint.«i686-no-tables») : Prop :=
  self.U.LimbsLt n ∧ self.W.LimbsLt n

end ProjectivePoint.«i686-no-tables»

end Curve25519Dalek.montgomery
