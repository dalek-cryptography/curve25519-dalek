/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Field.Invert
import Proofs.Backend.Serial.U64.Constants.EdwardsD2
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Constants.EdwardsD2
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.Backend

variable (B : Backend)

/-- `EdwardsPoint::as_affine_niels` over a backend: `d2` is `EDWARDS_D2`, `mk` builds the
`AffineNielsPoint`. -/
@[expose] def asAffineNielsBody {P : Type} (d2 : Result B.F) (mk : B.F → B.F → B.F → P)
    (X Y Z : B.F) : Result P := do
  let recip ← B.invert Z
  let x ← B.mul X recip
  let y ← B.mul Y recip
  let fe ← B.mul x y
  let fe1 ← d2
  let xy2d ← B.mul fe fe1
  let fe2 ← B.add y x
  let fe3 ← B.sub y x
  ok (mk fe2 fe3 xy2d)

/-- `asAffineNielsBody`: `(y + x, y - x, x y (2 d))` with `x = X Z⁻¹`, `y = Y Z⁻¹`. -/
theorem asAffineNielsBody_spec (hadd : B.AddSpec) (hsub : B.SubSpec) (hmul : B.MulSpec)
    (hinv : B.InvertSpec) (d2 : Result B.F)
    (hd2 : d2 ⦃ (r : B.F) => B.toField r = 2 * d ∧ B.Red r ⦄) {P : Type}
    (mk : B.F → B.F → B.F → P) (X Y Z T : B.F) (hX : B.Red X) (hY : B.Red Y) (hZ : B.Red Z) :
    B.asAffineNielsBody d2 mk X Y Z ⦃ (r : P) => ∃ a b c, r = mk a b c ∧
      (⟨B.toField X, B.toField Y, B.toField Z, B.toField T⟩ : edwards.Extended).toAffineNiels =
        ⟨B.toField a, B.toField b, B.toField c⟩ ∧ B.Sum2 a ∧ B.Red b ∧ B.Red c ⦄ := by
  unfold asAffineNielsBody
  step with hinv Z (B.red_sqIn hZ) as ⟨recip, hr, hrb⟩
  step with hmul X recip (B.red_mulIn hX) (B.red_mulIn hrb) as ⟨x, hx, hxb⟩
  step with hmul Y recip (B.red_mulIn hY) (B.red_mulIn hrb) as ⟨y, hy, hyb⟩
  step with hmul x y (B.red_mulIn hxb) (B.red_mulIn hyb) as ⟨xy, hxy, hxyb⟩
  apply spec_bind hd2
  rintro D2 ⟨hD2, hD2b⟩
  step with hmul xy D2 (B.red_mulIn hxyb) (B.red_mulIn hD2b) as ⟨xy2d, hxy2d, hxy2db⟩
  step with hadd y x hyb hxb as ⟨ypx, hypx, hypxb⟩
  step with hsub y x (B.red_mulIn hyb) (B.red_mulIn hxb) as ⟨ymx, hymx, hymxb⟩
  refine ⟨ypx, ymx, xy2d, rfl, ?_, hypxb, hymxb, hxy2db⟩
  simp only [Extended.toAffineNiels, hypx, hymx, hxy2d, hxy, hx, hy, hr, hD2, edwards_d]

end Curve25519Dalek.Backend

namespace Curve25519Dalek.edwards

namespace «EdwardsPoint64bit-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::as_affine_niels`: `(y + x, y - x, x y (2 d))` with `x = X Z⁻¹`, `y = Y Z⁻¹`
(`0⁻¹ = 0`); limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem as_affine_niels_toAffineNiels (self : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt
    52) :
    as_affine_niels self ⦃ (r : AffineNielsPoint.«64bit-tables») =>
      r.toAffineNiels = self.toExtended.toAffineNiels ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_affine_niels
  apply spec_mono (Backend.asAffineNielsBody_spec Backend.U64 Backend.U64.add_spec
    Backend.U64.sub_spec Backend.U64.mul_spec Backend.U64.invert_spec _
    (spec_mono backend.serial.u64.constants.EDWARDS_D2_spec fun _ ⟨h, hb⟩ =>
      ⟨toField_eq_two_mul_d_of_asNat h, limbs_lt_of_le (by decide) hb⟩)
    (fun a b c => ({ y_plus_x := a, y_minus_x := b, xy2d := c } :
      AffineNielsPoint.«64bit-tables»)) _ _ _ self.T hX hY hZ)
  rintro _ ⟨a, b, c, rfl, h, ha, hb, hc⟩
  refine ⟨by
    rw [AffineNielsPoint.«64bit-tables».toAffineNiels_def,
      EdwardsPoint.«64bit-tables».toExtended_def]
    exact h.symm, limbs_lt_of_le (by decide) ha, limbs_lt_of_le (by decide) hb,
    limbs_lt_of_le (by decide) hc⟩

/-- `EdwardsPoint::as_affine_niels` represents the same point. -/
theorem as_affine_niels_spec (self : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    as_affine_niels self ⦃ (r : AffineNielsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (as_affine_niels_toAffineNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«64bit-tables».onCurve_iff,
      AffineNielsPoint.«64bit-tables».toPoint_def, hr,
      EdwardsPoint.«64bit-tables».toPoint_def]
    exact ⟨Extended.onCurve_toAffineNiels hon,
      Extended.toPoint_toAffineNiels hon, hb⟩

end «EdwardsPoint64bit-tables»

namespace «EdwardsPoint32bit-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::as_affine_niels`: `(y + x, y - x, x y (2 d))` with `x = X Z⁻¹`, `y = Y Z⁻¹`
(`0⁻¹ = 0`); limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem as_affine_niels_toAffineNiels (self : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    :
    as_affine_niels self ⦃ (r : AffineNielsPoint.«32bit-tables») =>
      r.toAffineNiels = self.toExtended.toAffineNiels ∧ r.LimbsLt 27 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_affine_niels
  apply spec_mono (Backend.asAffineNielsBody_spec Backend.U32 Backend.U32.add_spec
    Backend.U32.sub_spec Backend.U32.mul_spec Backend.U32.invert_spec _
    (spec_mono backend.serial.u32.constants.EDWARDS_D2_spec fun _ ⟨h, hb⟩ =>
      ⟨toField_eq_two_mul_d_of_asNat h, limbs_lt_of_le (by decide) hb⟩)
    (fun a b c => ({ y_plus_x := a, y_minus_x := b, xy2d := c } :
      AffineNielsPoint.«32bit-tables»)) _ _ _ self.T hX hY hZ)
  rintro _ ⟨a, b, c, rfl, h, ha, hb, hc⟩
  refine ⟨by
    rw [AffineNielsPoint.«32bit-tables».toAffineNiels_def,
      EdwardsPoint.«32bit-tables».toExtended_def]
    exact h.symm, limbs_lt_of_le (by decide) ha, limbs_lt_of_le (by decide) hb,
    limbs_lt_of_le (by decide) hc⟩

/-- `EdwardsPoint::as_affine_niels` represents the same point. -/
theorem as_affine_niels_spec (self : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    as_affine_niels self ⦃ (r : AffineNielsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (as_affine_niels_toAffineNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«32bit-tables».onCurve_iff,
      AffineNielsPoint.«32bit-tables».toPoint_def, hr,
      EdwardsPoint.«32bit-tables».toPoint_def]
    exact ⟨Extended.onCurve_toAffineNiels hon,
      Extended.toPoint_toAffineNiels hon, hb⟩

end «EdwardsPoint32bit-tables»

namespace «EdwardsPoint64bit-notables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::as_affine_niels`: `(y + x, y - x, x y (2 d))` with `x = X Z⁻¹`, `y = Y Z⁻¹`
(`0⁻¹ = 0`); limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem as_affine_niels_toAffineNiels (self : EdwardsPoint.«64bit-notables») (hself :
    self.LimbsLt 52) :
    as_affine_niels self ⦃ (r : AffineNielsPoint.«64bit-notables») =>
      r.toAffineNiels = self.toExtended.toAffineNiels ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_affine_niels
  apply spec_mono (Backend.asAffineNielsBody_spec Backend.U64 Backend.U64.add_spec
    Backend.U64.sub_spec Backend.U64.mul_spec Backend.U64.invert_spec _
    (spec_mono backend.serial.u64.constants.EDWARDS_D2_spec fun _ ⟨h, hb⟩ =>
      ⟨toField_eq_two_mul_d_of_asNat h, limbs_lt_of_le (by decide) hb⟩)
    (fun a b c => ({ y_plus_x := a, y_minus_x := b, xy2d := c } :
      AffineNielsPoint.«64bit-notables»)) _ _ _ self.T hX hY hZ)
  rintro _ ⟨a, b, c, rfl, h, ha, hb, hc⟩
  refine ⟨by
    rw [AffineNielsPoint.«64bit-notables».toAffineNiels_def,
      EdwardsPoint.«64bit-notables».toExtended_def]
    exact h.symm, limbs_lt_of_le (by decide) ha, limbs_lt_of_le (by decide) hb,
    limbs_lt_of_le (by decide) hc⟩

/-- `EdwardsPoint::as_affine_niels` represents the same point. -/
theorem as_affine_niels_spec (self : EdwardsPoint.«64bit-notables»)
    (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    as_affine_niels self ⦃ (r : AffineNielsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (as_affine_niels_toAffineNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«64bit-notables».onCurve_iff,
      AffineNielsPoint.«64bit-notables».toPoint_def, hr,
      EdwardsPoint.«64bit-notables».toPoint_def]
    exact ⟨Extended.onCurve_toAffineNiels hon,
      Extended.toPoint_toAffineNiels hon, hb⟩

end «EdwardsPoint64bit-notables»

namespace «EdwardsPoint32bit-notables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::as_affine_niels`: `(y + x, y - x, x y (2 d))` with `x = X Z⁻¹`, `y = Y Z⁻¹`
(`0⁻¹ = 0`); limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem as_affine_niels_toAffineNiels (self : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt
    26) :
    as_affine_niels self ⦃ (r : AffineNielsPoint.«32bit-notables») =>
      r.toAffineNiels = self.toExtended.toAffineNiels ∧ r.LimbsLt 27 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_affine_niels
  apply spec_mono (Backend.asAffineNielsBody_spec Backend.U32 Backend.U32.add_spec
    Backend.U32.sub_spec Backend.U32.mul_spec Backend.U32.invert_spec _
    (spec_mono backend.serial.u32.constants.EDWARDS_D2_spec fun _ ⟨h, hb⟩ =>
      ⟨toField_eq_two_mul_d_of_asNat h, limbs_lt_of_le (by decide) hb⟩)
    (fun a b c => ({ y_plus_x := a, y_minus_x := b, xy2d := c } :
      AffineNielsPoint.«32bit-notables»)) _ _ _ self.T hX hY hZ)
  rintro _ ⟨a, b, c, rfl, h, ha, hb, hc⟩
  refine ⟨by
    rw [AffineNielsPoint.«32bit-notables».toAffineNiels_def,
      EdwardsPoint.«32bit-notables».toExtended_def]
    exact h.symm, limbs_lt_of_le (by decide) ha, limbs_lt_of_le (by decide) hb,
    limbs_lt_of_le (by decide) hc⟩

/-- `EdwardsPoint::as_affine_niels` represents the same point. -/
theorem as_affine_niels_spec (self : EdwardsPoint.«32bit-notables»)
    (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    as_affine_niels self ⦃ (r : AffineNielsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (as_affine_niels_toAffineNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«32bit-notables».onCurve_iff,
      AffineNielsPoint.«32bit-notables».toPoint_def, hr,
      EdwardsPoint.«32bit-notables».toPoint_def]
    exact ⟨Extended.onCurve_toAffineNiels hon,
      Extended.toPoint_toAffineNiels hon, hb⟩

end «EdwardsPoint32bit-notables»

end Curve25519Dalek.edwards
