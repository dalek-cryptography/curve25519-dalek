/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Ristretto.Even
public import Defs.Edwards
public import Subtle.Contract
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Field.CtEq
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Helpers.ToField2625
public section

/-! # `ConstantTimeEq` and `PartialEq` for `RistrettoPoint`

`ct_eq` compares `X₁ Y₂ = Y₁ X₂` or `X₁ X₂ = Y₁ Y₂`: after dividing by `Z₁ Z₂`, the coordinate
formula of the Ristretto equivalence (`rel_iff_formula`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.ristretto

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- Cross products of fractions with nonzero denominators. -/
private theorem div_mul_div_eq_iff {a b c e z₁ z₂ : ZMod p} (hz : z₁ * z₂ ≠ 0) :
    a / z₁ * (b / z₂) = c / z₁ * (e / z₂) ↔ a * b = c * e := by
  rw [div_mul_div_comm, div_mul_div_comm, div_left_inj' hz]

namespace RistrettoPoint.«x86_64-tables».Insts.SubtleConstantTimeEq

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

open edwards.EdwardsPoint.«x86_64-tables» in
/-- `ConstantTimeEq for RistrettoPoint`: equality in the Ristretto group, i.e. of the classes of
the represented points (`X₁ Y₂ = Y₁ X₂` or `X₁ X₂ = Y₁ Y₂`); limbs `< 2^52`. -/
@[step]
theorem ct_eq_spec (self other : RistrettoPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ curve25519.edwards.Rel self.toPoint other.toPoint) ⦄ := by
  have hZ := ((onCurve_iff_equation self).mp hself_on).1
  have hZ' := ((onCurve_iff_equation other).mp hother_on).1
  obtain ⟨hX, hY, -, _⟩ := hself
  obtain ⟨hX', hY', -, _⟩ := hother
  unfold ct_eq
  step as ⟨X1Y2, h1, _⟩
  step as ⟨Y1X2, h2, _⟩
  step as ⟨X1X2, h3, _⟩
  step as ⟨Y1Y2, h4, _⟩
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨c1, hc1v, hc11, hc10⟩
  step as ⟨c2, hc2v, hc2⟩
  refine ⟨hc2v, ?_⟩
  have key : (X1Y2.toField = Y1X2.toField ∨ X1X2.toField = Y1Y2.toField) ↔
      curve25519.edwards.Rel self.toPoint other.toPoint := by
    rw [rel_iff_formula, toPoint_x hself_on, toPoint_y hself_on, toPoint_x hother_on,
      toPoint_y hother_on, div_mul_div_eq_iff (mul_ne_zero hZ hZ'),
      div_mul_div_eq_iff (mul_ne_zero hZ hZ'), toField_mul_of_mod h1, toField_mul_of_mod h2,
      toField_mul_of_mod h3, toField_mul_of_mod h4]
  rw [hc2, ← key, ← eq_one_iff_toField_eq hc1 hc0, ← eq_one_iff_toField_eq hc11 hc10]
  rcases hcv with rfl | rfl <;> rcases hc1v with rfl | rfl <;> decide

end RistrettoPoint.«x86_64-tables».Insts.SubtleConstantTimeEq

namespace RistrettoPoint.«i686-tables».Insts.SubtleConstantTimeEq

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

open edwards.EdwardsPoint.«i686-tables» in
/-- `ConstantTimeEq for RistrettoPoint`: equality in the Ristretto group, i.e. of the classes of
the represented points (`X₁ Y₂ = Y₁ X₂` or `X₁ X₂ = Y₁ Y₂`); limbs `< 2^26`. -/
@[step]
theorem ct_eq_spec (self other : RistrettoPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ curve25519.edwards.Rel self.toPoint other.toPoint) ⦄ := by
  have hZ := ((onCurve_iff_equation self).mp hself_on).1
  have hZ' := ((onCurve_iff_equation other).mp hother_on).1
  obtain ⟨hX, hY, -, _⟩ := hself
  obtain ⟨hX', hY', -, _⟩ := hother
  unfold ct_eq
  step as ⟨X1Y2, h1, _⟩
  step as ⟨Y1X2, h2, _⟩
  step as ⟨X1X2, h3, _⟩
  step as ⟨Y1Y2, h4, _⟩
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨c1, hc1v, hc11, hc10⟩
  step as ⟨c2, hc2v, hc2⟩
  refine ⟨hc2v, ?_⟩
  have key : (X1Y2.toField = Y1X2.toField ∨ X1X2.toField = Y1Y2.toField) ↔
      curve25519.edwards.Rel self.toPoint other.toPoint := by
    rw [rel_iff_formula, toPoint_x hself_on, toPoint_y hself_on, toPoint_x hother_on,
      toPoint_y hother_on, div_mul_div_eq_iff (mul_ne_zero hZ hZ'),
      div_mul_div_eq_iff (mul_ne_zero hZ hZ'), toField_mul_of_mod h1, toField_mul_of_mod h2,
      toField_mul_of_mod h3, toField_mul_of_mod h4]
  rw [hc2, ← key, ← eq_one_iff_toField_eq hc1 hc0, ← eq_one_iff_toField_eq hc11 hc10]
  rcases hcv with rfl | rfl <;> rcases hc1v with rfl | rfl <;> decide

end RistrettoPoint.«i686-tables».Insts.SubtleConstantTimeEq

namespace RistrettoPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreCmpPartialEqRistrettoPointx86_64-tables»

/-- `PartialEq for RistrettoPoint`: equality in the Ristretto group; limbs `< 2^52`. -/
@[step]
theorem eq_spec (self other : RistrettoPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ curve25519.edwards.Rel self.toPoint other.toPoint ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

end «CoreCmpPartialEqRistrettoPointx86_64-tables»
end RistrettoPoint.«x86_64-tables».Insts

namespace RistrettoPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreCmpPartialEqRistrettoPointi686-tables»

/-- `PartialEq for RistrettoPoint`: equality in the Ristretto group; limbs `< 2^26`. -/
@[step]
theorem eq_spec (self other : RistrettoPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ curve25519.edwards.Rel self.toPoint other.toPoint ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

end «CoreCmpPartialEqRistrettoPointi686-tables»
end RistrettoPoint.«i686-tables».Insts

namespace RistrettoPoint.«x86_64-no-tables».Insts.SubtleConstantTimeEq

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

open edwards.EdwardsPoint.«x86_64-no-tables» in
/-- `ConstantTimeEq for RistrettoPoint`: equality in the Ristretto group, i.e. of the classes of
the represented points (`X₁ Y₂ = Y₁ X₂` or `X₁ X₂ = Y₁ Y₂`); limbs `< 2^52`. -/
@[step]
theorem ct_eq_spec (self other : RistrettoPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ curve25519.edwards.Rel self.toPoint other.toPoint) ⦄ := by
  have hZ := ((onCurve_iff_equation self).mp hself_on).1
  have hZ' := ((onCurve_iff_equation other).mp hother_on).1
  obtain ⟨hX, hY, -, _⟩ := hself
  obtain ⟨hX', hY', -, _⟩ := hother
  unfold ct_eq
  step as ⟨X1Y2, h1, _⟩
  step as ⟨Y1X2, h2, _⟩
  step as ⟨X1X2, h3, _⟩
  step as ⟨Y1Y2, h4, _⟩
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨c1, hc1v, hc11, hc10⟩
  step as ⟨c2, hc2v, hc2⟩
  refine ⟨hc2v, ?_⟩
  have key : (X1Y2.toField = Y1X2.toField ∨ X1X2.toField = Y1Y2.toField) ↔
      curve25519.edwards.Rel self.toPoint other.toPoint := by
    rw [rel_iff_formula, toPoint_x hself_on, toPoint_y hself_on, toPoint_x hother_on,
      toPoint_y hother_on, div_mul_div_eq_iff (mul_ne_zero hZ hZ'),
      div_mul_div_eq_iff (mul_ne_zero hZ hZ'), toField_mul_of_mod h1, toField_mul_of_mod h2,
      toField_mul_of_mod h3, toField_mul_of_mod h4]
  rw [hc2, ← key, ← eq_one_iff_toField_eq hc1 hc0, ← eq_one_iff_toField_eq hc11 hc10]
  rcases hcv with rfl | rfl <;> rcases hc1v with rfl | rfl <;> decide

end RistrettoPoint.«x86_64-no-tables».Insts.SubtleConstantTimeEq

namespace RistrettoPoint.«i686-no-tables».Insts.SubtleConstantTimeEq

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

open edwards.EdwardsPoint.«i686-no-tables» in
/-- `ConstantTimeEq for RistrettoPoint`: equality in the Ristretto group, i.e. of the classes of
the represented points (`X₁ Y₂ = Y₁ X₂` or `X₁ X₂ = Y₁ Y₂`); limbs `< 2^26`. -/
@[step]
theorem ct_eq_spec (self other : RistrettoPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ curve25519.edwards.Rel self.toPoint other.toPoint) ⦄ := by
  have hZ := ((onCurve_iff_equation self).mp hself_on).1
  have hZ' := ((onCurve_iff_equation other).mp hother_on).1
  obtain ⟨hX, hY, -, _⟩ := hself
  obtain ⟨hX', hY', -, _⟩ := hother
  unfold ct_eq
  step as ⟨X1Y2, h1, _⟩
  step as ⟨Y1X2, h2, _⟩
  step as ⟨X1X2, h3, _⟩
  step as ⟨Y1Y2, h4, _⟩
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨c1, hc1v, hc11, hc10⟩
  step as ⟨c2, hc2v, hc2⟩
  refine ⟨hc2v, ?_⟩
  have key : (X1Y2.toField = Y1X2.toField ∨ X1X2.toField = Y1Y2.toField) ↔
      curve25519.edwards.Rel self.toPoint other.toPoint := by
    rw [rel_iff_formula, toPoint_x hself_on, toPoint_y hself_on, toPoint_x hother_on,
      toPoint_y hother_on, div_mul_div_eq_iff (mul_ne_zero hZ hZ'),
      div_mul_div_eq_iff (mul_ne_zero hZ hZ'), toField_mul_of_mod h1, toField_mul_of_mod h2,
      toField_mul_of_mod h3, toField_mul_of_mod h4]
  rw [hc2, ← key, ← eq_one_iff_toField_eq hc1 hc0, ← eq_one_iff_toField_eq hc11 hc10]
  rcases hcv with rfl | rfl <;> rcases hc1v with rfl | rfl <;> decide

end RistrettoPoint.«i686-no-tables».Insts.SubtleConstantTimeEq

namespace RistrettoPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreCmpPartialEqRistrettoPointx86_64-no-tables»

/-- `PartialEq for RistrettoPoint`: equality in the Ristretto group; limbs `< 2^52`. -/
@[step]
theorem eq_spec (self other : RistrettoPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ curve25519.edwards.Rel self.toPoint other.toPoint ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

end «CoreCmpPartialEqRistrettoPointx86_64-no-tables»
end RistrettoPoint.«x86_64-no-tables».Insts

namespace RistrettoPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreCmpPartialEqRistrettoPointi686-no-tables»

/-- `PartialEq for RistrettoPoint`: equality in the Ristretto group; limbs `< 2^26`. -/
@[step]
theorem eq_spec (self other : RistrettoPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ curve25519.edwards.Rel self.toPoint other.toPoint ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

end «CoreCmpPartialEqRistrettoPointi686-no-tables»
end RistrettoPoint.«i686-no-tables».Insts

end Curve25519Dalek.ristretto
