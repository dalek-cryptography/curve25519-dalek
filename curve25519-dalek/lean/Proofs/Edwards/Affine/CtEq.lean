/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Subtle.Contract
import Proofs.Field.CtEq
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.edwards.affine

namespace AffinePoint.«x86_64-tables».Insts.SubtleConstantTimeEq

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ConstantTimeEq for AffinePoint`: both coordinates agree modulo `p`. -/
@[step]
theorem ct_eq_spec (self other : AffinePoint.«x86_64-tables») :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧
        (c = 1#u8 ↔
          self.x.toField = other.x.toField ∧ self.y.toField = other.y.toField) ⦄ := by
  unfold ct_eq
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨c1, hc1v, hc11, hc10⟩
  step as ⟨c2, hc2v, hc2⟩
  refine ⟨hc2v, ?_⟩
  rw [hc2, ← eq_one_iff_toField_eq hc1 hc0, ← eq_one_iff_toField_eq hc11 hc10]
  rcases hcv with rfl | rfl <;> rcases hc1v with rfl | rfl <;> decide

/-- `ConstantTimeEq for AffinePoint` on points: equality of the represented points. -/
theorem ct_eq_spec_point (self other : AffinePoint.«x86_64-tables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.toPoint = other.toPoint) ⦄ :=
  spec_mono (ct_eq_spec self other) fun _ ⟨hcv, hc⟩ => by
    rw [AffinePoint.«x86_64-tables».toPoint_eq_mk hself,
      AffinePoint.«x86_64-tables».toPoint_eq_mk hother, Point.ext_iff]
    exact ⟨hcv, hc⟩

end AffinePoint.«x86_64-tables».Insts.SubtleConstantTimeEq

namespace AffinePoint.«i686-tables».Insts.SubtleConstantTimeEq

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ConstantTimeEq for AffinePoint`: both coordinates agree modulo `p`. -/
@[step]
theorem ct_eq_spec (self other : AffinePoint.«i686-tables») :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧
        (c = 1#u8 ↔
          self.x.toField = other.x.toField ∧ self.y.toField = other.y.toField) ⦄ := by
  unfold ct_eq
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨c1, hc1v, hc11, hc10⟩
  step as ⟨c2, hc2v, hc2⟩
  refine ⟨hc2v, ?_⟩
  rw [hc2, ← eq_one_iff_toField_eq hc1 hc0, ← eq_one_iff_toField_eq hc11 hc10]
  rcases hcv with rfl | rfl <;> rcases hc1v with rfl | rfl <;> decide

/-- `ConstantTimeEq for AffinePoint` on points: equality of the represented points. -/
theorem ct_eq_spec_point (self other : AffinePoint.«i686-tables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.toPoint = other.toPoint) ⦄ :=
  spec_mono (ct_eq_spec self other) fun _ ⟨hcv, hc⟩ => by
    rw [AffinePoint.«i686-tables».toPoint_eq_mk hself,
      AffinePoint.«i686-tables».toPoint_eq_mk hother, Point.ext_iff]
    exact ⟨hcv, hc⟩

end AffinePoint.«i686-tables».Insts.SubtleConstantTimeEq

namespace AffinePoint.«x86_64-no-tables».Insts.SubtleConstantTimeEq

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ConstantTimeEq for AffinePoint`: both coordinates agree modulo `p`. -/
@[step]
theorem ct_eq_spec (self other : AffinePoint.«x86_64-no-tables») :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧
        (c = 1#u8 ↔
          self.x.toField = other.x.toField ∧ self.y.toField = other.y.toField) ⦄ := by
  unfold ct_eq
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨c1, hc1v, hc11, hc10⟩
  step as ⟨c2, hc2v, hc2⟩
  refine ⟨hc2v, ?_⟩
  rw [hc2, ← eq_one_iff_toField_eq hc1 hc0, ← eq_one_iff_toField_eq hc11 hc10]
  rcases hcv with rfl | rfl <;> rcases hc1v with rfl | rfl <;> decide

/-- `ConstantTimeEq for AffinePoint` on points: equality of the represented points. -/
theorem ct_eq_spec_point (self other : AffinePoint.«x86_64-no-tables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.toPoint = other.toPoint) ⦄ :=
  spec_mono (ct_eq_spec self other) fun _ ⟨hcv, hc⟩ => by
    rw [AffinePoint.«x86_64-no-tables».toPoint_eq_mk hself,
      AffinePoint.«x86_64-no-tables».toPoint_eq_mk hother, Point.ext_iff]
    exact ⟨hcv, hc⟩

end AffinePoint.«x86_64-no-tables».Insts.SubtleConstantTimeEq

namespace AffinePoint.«i686-no-tables».Insts.SubtleConstantTimeEq

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ConstantTimeEq for AffinePoint`: both coordinates agree modulo `p`. -/
@[step]
theorem ct_eq_spec (self other : AffinePoint.«i686-no-tables») :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧
        (c = 1#u8 ↔
          self.x.toField = other.x.toField ∧ self.y.toField = other.y.toField) ⦄ := by
  unfold ct_eq
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨c1, hc1v, hc11, hc10⟩
  step as ⟨c2, hc2v, hc2⟩
  refine ⟨hc2v, ?_⟩
  rw [hc2, ← eq_one_iff_toField_eq hc1 hc0, ← eq_one_iff_toField_eq hc11 hc10]
  rcases hcv with rfl | rfl <;> rcases hc1v with rfl | rfl <;> decide

/-- `ConstantTimeEq for AffinePoint` on points: equality of the represented points. -/
theorem ct_eq_spec_point (self other : AffinePoint.«i686-no-tables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.toPoint = other.toPoint) ⦄ :=
  spec_mono (ct_eq_spec self other) fun _ ⟨hcv, hc⟩ => by
    rw [AffinePoint.«i686-no-tables».toPoint_eq_mk hself,
      AffinePoint.«i686-no-tables».toPoint_eq_mk hother, Point.ext_iff]
    exact ⟨hcv, hc⟩

end AffinePoint.«i686-no-tables».Insts.SubtleConstantTimeEq

end Curve25519Dalek.edwards.affine
