/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.CurveModels
import Proofs.Field.Eq
public import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.backend.serial.curve_models

namespace AffineNielsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreCmpPartialEqAffineNielsPointx86_64-tables»

/-- `PartialEq for AffineNielsPoint` (derived): the three coordinates agree modulo `p`. -/
@[step]
theorem eq_spec (self other : AffineNielsPoint.«x86_64-tables») :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ self.toAffineNiels = other.toAffineNiels ⦄ := by
  unfold eq
  simp only [AffineNielsPoint.«x86_64-tables».toAffineNiels_def, AffineNiels.mk.injEq,
    toField_eq_toField_iff]
  step*

/-- `PartialEq for AffineNielsPoint` on points: equality of the represented points. -/
theorem eq_spec_point (self other : AffineNielsPoint.«x86_64-tables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_spec self other) fun b hb => by
    rw [hb, AffineNielsPoint.«x86_64-tables».toPoint_def,
      AffineNielsPoint.«x86_64-tables».toPoint_def]
    exact (AffineNiels.toPoint_inj hself hother).symm

end «CoreCmpPartialEqAffineNielsPointx86_64-tables»
end AffineNielsPoint.«x86_64-tables».Insts

namespace AffineNielsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreCmpPartialEqAffineNielsPointi686-tables»

/-- `PartialEq for AffineNielsPoint` (derived): the three coordinates agree modulo `p`. -/
@[step]
theorem eq_spec (self other : AffineNielsPoint.«i686-tables») :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ self.toAffineNiels = other.toAffineNiels ⦄ := by
  unfold eq
  simp only [AffineNielsPoint.«i686-tables».toAffineNiels_def, AffineNiels.mk.injEq,
    toField_eq_toField_iff]
  step*

/-- `PartialEq for AffineNielsPoint` on points: equality of the represented points. -/
theorem eq_spec_point (self other : AffineNielsPoint.«i686-tables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_spec self other) fun b hb => by
    rw [hb, AffineNielsPoint.«i686-tables».toPoint_def,
      AffineNielsPoint.«i686-tables».toPoint_def]
    exact (AffineNiels.toPoint_inj hself hother).symm

end «CoreCmpPartialEqAffineNielsPointi686-tables»
end AffineNielsPoint.«i686-tables».Insts

namespace AffineNielsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreCmpPartialEqAffineNielsPointx86_64-no-tables»

/-- `PartialEq for AffineNielsPoint` (derived): the three coordinates agree modulo `p`. -/
@[step]
theorem eq_spec (self other : AffineNielsPoint.«x86_64-no-tables») :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ self.toAffineNiels = other.toAffineNiels ⦄ := by
  unfold eq
  simp only [AffineNielsPoint.«x86_64-no-tables».toAffineNiels_def, AffineNiels.mk.injEq,
    toField_eq_toField_iff]
  step*

/-- `PartialEq for AffineNielsPoint` on points: equality of the represented points. -/
theorem eq_spec_point (self other : AffineNielsPoint.«x86_64-no-tables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_spec self other) fun b hb => by
    rw [hb, AffineNielsPoint.«x86_64-no-tables».toPoint_def,
      AffineNielsPoint.«x86_64-no-tables».toPoint_def]
    exact (AffineNiels.toPoint_inj hself hother).symm

end «CoreCmpPartialEqAffineNielsPointx86_64-no-tables»
end AffineNielsPoint.«x86_64-no-tables».Insts

namespace AffineNielsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreCmpPartialEqAffineNielsPointi686-no-tables»

/-- `PartialEq for AffineNielsPoint` (derived): the three coordinates agree modulo `p`. -/
@[step]
theorem eq_spec (self other : AffineNielsPoint.«i686-no-tables») :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ self.toAffineNiels = other.toAffineNiels ⦄ := by
  unfold eq
  simp only [AffineNielsPoint.«i686-no-tables».toAffineNiels_def, AffineNiels.mk.injEq,
    toField_eq_toField_iff]
  step*

/-- `PartialEq for AffineNielsPoint` on points: equality of the represented points. -/
theorem eq_spec_point (self other : AffineNielsPoint.«i686-no-tables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_spec self other) fun b hb => by
    rw [hb, AffineNielsPoint.«i686-no-tables».toPoint_def,
      AffineNielsPoint.«i686-no-tables».toPoint_def]
    exact (AffineNiels.toPoint_inj hself hother).symm

end «CoreCmpPartialEqAffineNielsPointi686-no-tables»
end AffineNielsPoint.«i686-no-tables».Insts

end Curve25519Dalek.backend.serial.curve_models
