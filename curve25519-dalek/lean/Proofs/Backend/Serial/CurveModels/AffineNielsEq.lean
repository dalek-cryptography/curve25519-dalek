module
public import Curve25519Dalek.Funs
public import Proofs.Representation.CurveModels
import Proofs.Field.Eq
public import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.backend.serial.curve_models

namespace AffineNielsPoint.«64bit-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreCmpPartialEqAffineNielsPoint64bit-tables»

/-- `PartialEq for AffineNielsPoint` (derived): the three coordinates agree modulo `p`. -/
@[step]
theorem eq_toAffineNiels (self other : AffineNielsPoint.«64bit-tables») :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ self.toAffineNiels = other.toAffineNiels ⦄ := by
  unfold eq
  simp only [AffineNielsPoint.«64bit-tables».toAffineNiels_def, AffineNiels.mk.injEq,
    toField_eq_toField_iff]
  step*

/-- `PartialEq for AffineNielsPoint` on points: equality of the represented points. -/
theorem eq_spec (self other : AffineNielsPoint.«64bit-tables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_toAffineNiels self other) fun b hb => by
    rw [hb, AffineNielsPoint.«64bit-tables».toPoint_def,
      AffineNielsPoint.«64bit-tables».toPoint_def]
    exact (AffineNiels.toPoint_inj hself hother).symm

end «CoreCmpPartialEqAffineNielsPoint64bit-tables»
end AffineNielsPoint.«64bit-tables».Insts

namespace AffineNielsPoint.«32bit-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreCmpPartialEqAffineNielsPoint32bit-tables»

/-- `PartialEq for AffineNielsPoint` (derived): the three coordinates agree modulo `p`. -/
@[step]
theorem eq_toAffineNiels (self other : AffineNielsPoint.«32bit-tables») :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ self.toAffineNiels = other.toAffineNiels ⦄ := by
  unfold eq
  simp only [AffineNielsPoint.«32bit-tables».toAffineNiels_def, AffineNiels.mk.injEq,
    toField_eq_toField_iff]
  step*

/-- `PartialEq for AffineNielsPoint` on points: equality of the represented points. -/
theorem eq_spec (self other : AffineNielsPoint.«32bit-tables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_toAffineNiels self other) fun b hb => by
    rw [hb, AffineNielsPoint.«32bit-tables».toPoint_def,
      AffineNielsPoint.«32bit-tables».toPoint_def]
    exact (AffineNiels.toPoint_inj hself hother).symm

end «CoreCmpPartialEqAffineNielsPoint32bit-tables»
end AffineNielsPoint.«32bit-tables».Insts

namespace AffineNielsPoint.«64bit-notables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreCmpPartialEqAffineNielsPoint64bit-notables»

/-- `PartialEq for AffineNielsPoint` (derived): the three coordinates agree modulo `p`. -/
@[step]
theorem eq_toAffineNiels (self other : AffineNielsPoint.«64bit-notables») :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ self.toAffineNiels = other.toAffineNiels ⦄ := by
  unfold eq
  simp only [AffineNielsPoint.«64bit-notables».toAffineNiels_def, AffineNiels.mk.injEq,
    toField_eq_toField_iff]
  step*

/-- `PartialEq for AffineNielsPoint` on points: equality of the represented points. -/
theorem eq_spec (self other : AffineNielsPoint.«64bit-notables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_toAffineNiels self other) fun b hb => by
    rw [hb, AffineNielsPoint.«64bit-notables».toPoint_def,
      AffineNielsPoint.«64bit-notables».toPoint_def]
    exact (AffineNiels.toPoint_inj hself hother).symm

end «CoreCmpPartialEqAffineNielsPoint64bit-notables»
end AffineNielsPoint.«64bit-notables».Insts

namespace AffineNielsPoint.«32bit-notables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreCmpPartialEqAffineNielsPoint32bit-notables»

/-- `PartialEq for AffineNielsPoint` (derived): the three coordinates agree modulo `p`. -/
@[step]
theorem eq_toAffineNiels (self other : AffineNielsPoint.«32bit-notables») :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ self.toAffineNiels = other.toAffineNiels ⦄ := by
  unfold eq
  simp only [AffineNielsPoint.«32bit-notables».toAffineNiels_def, AffineNiels.mk.injEq,
    toField_eq_toField_iff]
  step*

/-- `PartialEq for AffineNielsPoint` on points: equality of the represented points. -/
theorem eq_spec (self other : AffineNielsPoint.«32bit-notables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_toAffineNiels self other) fun b hb => by
    rw [hb, AffineNielsPoint.«32bit-notables».toPoint_def,
      AffineNielsPoint.«32bit-notables».toPoint_def]
    exact (AffineNiels.toPoint_inj hself hother).symm

end «CoreCmpPartialEqAffineNielsPoint32bit-notables»
end AffineNielsPoint.«32bit-notables».Insts

end Curve25519Dalek.backend.serial.curve_models
