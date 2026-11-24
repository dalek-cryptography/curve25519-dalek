module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Edwards.CtEq
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace EdwardsPoint.«64bit-tables».Insts.«CoreCmpPartialEqEdwardsPoint64bit-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `PartialEq for EdwardsPoint`: projective equality
`X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` is not compared); limbs `< 2^52`. -/
@[step]
theorem eq_projEq (self other : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.ProjEq other ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

/-- `PartialEq for EdwardsPoint` on points: equality of the represented points. -/
theorem eq_spec (self other : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (r : Bool) => r = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_projEq self other hself hother) fun _ hb =>
    hb.trans (EdwardsPoint.«64bit-tables».projEq_iff_toPoint_eq hself_on hother_on)

end EdwardsPoint.«64bit-tables».Insts.«CoreCmpPartialEqEdwardsPoint64bit-tables»

namespace EdwardsPoint.«32bit-tables».Insts.«CoreCmpPartialEqEdwardsPoint32bit-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `PartialEq for EdwardsPoint`: projective equality
`X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` is not compared); limbs `< 2^26`. -/
@[step]
theorem eq_projEq (self other : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.ProjEq other ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

/-- `PartialEq for EdwardsPoint` on points: equality of the represented points. -/
theorem eq_spec (self other : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (r : Bool) => r = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_projEq self other hself hother) fun _ hb =>
    hb.trans (EdwardsPoint.«32bit-tables».projEq_iff_toPoint_eq hself_on hother_on)

end EdwardsPoint.«32bit-tables».Insts.«CoreCmpPartialEqEdwardsPoint32bit-tables»

namespace EdwardsPoint.«64bit-notables».Insts.«CoreCmpPartialEqEdwardsPoint64bit-notables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `PartialEq for EdwardsPoint`: projective equality
`X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` is not compared); limbs `< 2^52`. -/
@[step]
theorem eq_projEq (self other : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.ProjEq other ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

/-- `PartialEq for EdwardsPoint` on points: equality of the represented points. -/
theorem eq_spec (self other : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (r : Bool) => r = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_projEq self other hself hother) fun _ hb =>
    hb.trans (EdwardsPoint.«64bit-notables».projEq_iff_toPoint_eq hself_on hother_on)

end EdwardsPoint.«64bit-notables».Insts.«CoreCmpPartialEqEdwardsPoint64bit-notables»

namespace EdwardsPoint.«32bit-notables».Insts.«CoreCmpPartialEqEdwardsPoint32bit-notables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `PartialEq for EdwardsPoint`: projective equality
`X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` is not compared); limbs `< 2^26`. -/
@[step]
theorem eq_projEq (self other : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.ProjEq other ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

/-- `PartialEq for EdwardsPoint` on points: equality of the represented points. -/
theorem eq_spec (self other : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (r : Bool) => r = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_projEq self other hself hother) fun _ hb =>
    hb.trans (EdwardsPoint.«32bit-notables».projEq_iff_toPoint_eq hself_on hother_on)

end EdwardsPoint.«32bit-notables».Insts.«CoreCmpPartialEqEdwardsPoint32bit-notables»

end Curve25519Dalek.edwards
