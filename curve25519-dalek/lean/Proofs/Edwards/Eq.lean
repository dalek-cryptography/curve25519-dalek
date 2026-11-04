/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Edwards.CtEq
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace EdwardsPoint.«x86_64-tables».Insts.«CoreCmpPartialEqEdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `PartialEq for EdwardsPoint`: projective equality
`X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` is not compared); limbs `< 2^52`. -/
@[step]
theorem eq_spec (self other : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.ProjEq other ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

/-- `PartialEq for EdwardsPoint` on points: equality of the represented points. -/
theorem eq_spec_point (self other : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_spec self other hself hother) fun _ hb =>
    hb.trans (EdwardsPoint.«x86_64-tables».projEq_iff_toPoint_eq hself_on hother_on)

end EdwardsPoint.«x86_64-tables».Insts.«CoreCmpPartialEqEdwardsPointx86_64-tables»

namespace EdwardsPoint.«i686-tables».Insts.«CoreCmpPartialEqEdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `PartialEq for EdwardsPoint`: projective equality
`X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` is not compared); limbs `< 2^26`. -/
@[step]
theorem eq_spec (self other : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.ProjEq other ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

/-- `PartialEq for EdwardsPoint` on points: equality of the represented points. -/
theorem eq_spec_point (self other : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_spec self other hself hother) fun _ hb =>
    hb.trans (EdwardsPoint.«i686-tables».projEq_iff_toPoint_eq hself_on hother_on)

end EdwardsPoint.«i686-tables».Insts.«CoreCmpPartialEqEdwardsPointi686-tables»

namespace EdwardsPoint.«x86_64-no-tables».Insts.«CoreCmpPartialEqEdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `PartialEq for EdwardsPoint`: projective equality
`X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` is not compared); limbs `< 2^52`. -/
@[step]
theorem eq_spec (self other : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.ProjEq other ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

/-- `PartialEq for EdwardsPoint` on points: equality of the represented points. -/
theorem eq_spec_point (self other : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_spec self other hself hother) fun _ hb =>
    hb.trans (EdwardsPoint.«x86_64-no-tables».projEq_iff_toPoint_eq hself_on hother_on)

end EdwardsPoint.«x86_64-no-tables».Insts.«CoreCmpPartialEqEdwardsPointx86_64-no-tables»

namespace EdwardsPoint.«i686-no-tables».Insts.«CoreCmpPartialEqEdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `PartialEq for EdwardsPoint`: projective equality
`X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` is not compared); limbs `< 2^26`. -/
@[step]
theorem eq_spec (self other : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.ProjEq other ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

/-- `PartialEq for EdwardsPoint` on points: equality of the represented points. -/
theorem eq_spec_point (self other : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_spec self other hself hother) fun _ hb =>
    hb.trans (EdwardsPoint.«i686-no-tables».projEq_iff_toPoint_eq hself_on hother_on)

end EdwardsPoint.«i686-no-tables».Insts.«CoreCmpPartialEqEdwardsPointi686-no-tables»

end Curve25519Dalek.edwards
