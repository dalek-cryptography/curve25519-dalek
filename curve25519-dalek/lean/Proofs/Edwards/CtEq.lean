/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Subtle.Contract
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Field.CtEq
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace EdwardsPoint.«x86_64-tables».Insts.SubtleConstantTimeEq

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ConstantTimeEq for EdwardsPoint`: projective equality
`X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` is not compared); limbs `< 2^52`. -/
@[step]
theorem ct_eq_spec (self other : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.ProjEq other) ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  obtain ⟨hX', hY', hZ', hT'⟩ := hother
  unfold ct_eq
  step as ⟨XZ', hXZ', hXZ'_lt⟩
  step as ⟨X'Z, hX'Z, hX'Z_lt⟩
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨YZ', hYZ', hYZ'_lt⟩
  step as ⟨Y'Z, hY'Z, hY'Z_lt⟩
  step as ⟨c1, hc1v, hc11, hc10⟩
  step as ⟨c2, hc2v, hc2⟩
  refine ⟨hc2v, ?_⟩
  rw [hc2, EdwardsPoint.«x86_64-tables».projEq_iff, ← toField_mul_of_mod hXZ',
    ← toField_mul_of_mod hX'Z, ← toField_mul_of_mod hYZ', ← toField_mul_of_mod hY'Z,
    ← eq_one_iff_toField_eq hc1 hc0, ← eq_one_iff_toField_eq hc11 hc10]
  rcases hcv with rfl | rfl <;> rcases hc1v with rfl | rfl <;> decide

/-- `ConstantTimeEq for EdwardsPoint` on points: equality of the represented points. -/
theorem ct_eq_spec_point (self other : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.toPoint = other.toPoint) ⦄ :=
  spec_mono (ct_eq_spec self other hself hother) fun _ ⟨hcv, hc⟩ =>
    ⟨hcv, hc.trans (EdwardsPoint.«x86_64-tables».projEq_iff_toPoint_eq hself_on hother_on)⟩

end EdwardsPoint.«x86_64-tables».Insts.SubtleConstantTimeEq

namespace EdwardsPoint.«i686-tables».Insts.SubtleConstantTimeEq

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ConstantTimeEq for EdwardsPoint`: projective equality
`X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` is not compared); limbs `< 2^26`. -/
@[step]
theorem ct_eq_spec (self other : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.ProjEq other) ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  obtain ⟨hX', hY', hZ', hT'⟩ := hother
  unfold ct_eq
  step as ⟨XZ', hXZ', hXZ'_lt⟩
  step as ⟨X'Z, hX'Z, hX'Z_lt⟩
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨YZ', hYZ', hYZ'_lt⟩
  step as ⟨Y'Z, hY'Z, hY'Z_lt⟩
  step as ⟨c1, hc1v, hc11, hc10⟩
  step as ⟨c2, hc2v, hc2⟩
  refine ⟨hc2v, ?_⟩
  rw [hc2, EdwardsPoint.«i686-tables».projEq_iff, ← toField_mul_of_mod hXZ',
    ← toField_mul_of_mod hX'Z, ← toField_mul_of_mod hYZ', ← toField_mul_of_mod hY'Z,
    ← eq_one_iff_toField_eq hc1 hc0, ← eq_one_iff_toField_eq hc11 hc10]
  rcases hcv with rfl | rfl <;> rcases hc1v with rfl | rfl <;> decide

/-- `ConstantTimeEq for EdwardsPoint` on points: equality of the represented points. -/
theorem ct_eq_spec_point (self other : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.toPoint = other.toPoint) ⦄ :=
  spec_mono (ct_eq_spec self other hself hother) fun _ ⟨hcv, hc⟩ =>
    ⟨hcv, hc.trans (EdwardsPoint.«i686-tables».projEq_iff_toPoint_eq hself_on hother_on)⟩

end EdwardsPoint.«i686-tables».Insts.SubtleConstantTimeEq

namespace EdwardsPoint.«x86_64-no-tables».Insts.SubtleConstantTimeEq

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ConstantTimeEq for EdwardsPoint`: projective equality
`X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` is not compared); limbs `< 2^52`. -/
@[step]
theorem ct_eq_spec (self other : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.ProjEq other) ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  obtain ⟨hX', hY', hZ', hT'⟩ := hother
  unfold ct_eq
  step as ⟨XZ', hXZ', hXZ'_lt⟩
  step as ⟨X'Z, hX'Z, hX'Z_lt⟩
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨YZ', hYZ', hYZ'_lt⟩
  step as ⟨Y'Z, hY'Z, hY'Z_lt⟩
  step as ⟨c1, hc1v, hc11, hc10⟩
  step as ⟨c2, hc2v, hc2⟩
  refine ⟨hc2v, ?_⟩
  rw [hc2, EdwardsPoint.«x86_64-no-tables».projEq_iff, ← toField_mul_of_mod hXZ',
    ← toField_mul_of_mod hX'Z, ← toField_mul_of_mod hYZ', ← toField_mul_of_mod hY'Z,
    ← eq_one_iff_toField_eq hc1 hc0, ← eq_one_iff_toField_eq hc11 hc10]
  rcases hcv with rfl | rfl <;> rcases hc1v with rfl | rfl <;> decide

/-- `ConstantTimeEq for EdwardsPoint` on points: equality of the represented points. -/
theorem ct_eq_spec_point (self other : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.toPoint = other.toPoint) ⦄ :=
  spec_mono (ct_eq_spec self other hself hother) fun _ ⟨hcv, hc⟩ =>
    ⟨hcv, hc.trans (EdwardsPoint.«x86_64-no-tables».projEq_iff_toPoint_eq hself_on hother_on)⟩

end EdwardsPoint.«x86_64-no-tables».Insts.SubtleConstantTimeEq

namespace EdwardsPoint.«i686-no-tables».Insts.SubtleConstantTimeEq

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ConstantTimeEq for EdwardsPoint`: projective equality
`X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` is not compared); limbs `< 2^26`. -/
@[step]
theorem ct_eq_spec (self other : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.ProjEq other) ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  obtain ⟨hX', hY', hZ', hT'⟩ := hother
  unfold ct_eq
  step as ⟨XZ', hXZ', hXZ'_lt⟩
  step as ⟨X'Z, hX'Z, hX'Z_lt⟩
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨YZ', hYZ', hYZ'_lt⟩
  step as ⟨Y'Z, hY'Z, hY'Z_lt⟩
  step as ⟨c1, hc1v, hc11, hc10⟩
  step as ⟨c2, hc2v, hc2⟩
  refine ⟨hc2v, ?_⟩
  rw [hc2, EdwardsPoint.«i686-no-tables».projEq_iff, ← toField_mul_of_mod hXZ',
    ← toField_mul_of_mod hX'Z, ← toField_mul_of_mod hYZ', ← toField_mul_of_mod hY'Z,
    ← eq_one_iff_toField_eq hc1 hc0, ← eq_one_iff_toField_eq hc11 hc10]
  rcases hcv with rfl | rfl <;> rcases hc1v with rfl | rfl <;> decide

/-- `ConstantTimeEq for EdwardsPoint` on points: equality of the represented points. -/
theorem ct_eq_spec_point (self other : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.toPoint = other.toPoint) ⦄ :=
  spec_mono (ct_eq_spec self other hself hother) fun _ ⟨hcv, hc⟩ =>
    ⟨hcv, hc.trans (EdwardsPoint.«i686-no-tables».projEq_iff_toPoint_eq hself_on hother_on)⟩

end EdwardsPoint.«i686-no-tables».Insts.SubtleConstantTimeEq

end Curve25519Dalek.edwards
