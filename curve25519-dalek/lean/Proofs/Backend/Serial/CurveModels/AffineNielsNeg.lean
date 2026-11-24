module
public import Curve25519Dalek.Funs
public import Proofs.Representation.CurveModels
import Proofs.Backend.Serial.U64.Field.Neg
public import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.Neg
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek

namespace «Shared0AffineNielsPoint64bit-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithNegAffineNielsPoint64bit-tables»

/-- `Neg for &AffineNielsPoint`: swap `y + x` and `y - x`, negate `xy2d`; limbs `< 2^54`. -/
@[step]
theorem neg_toAffineNiels (self : AffineNielsPoint.«64bit-tables») (hself : self.LimbsLt 54) :
    neg self ⦃ (r : AffineNielsPoint.«64bit-tables») =>
      r.toAffineNiels = self.toAffineNiels.neg ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨hypx, hymx, hxy2d⟩ := hself
  unfold neg
  step as ⟨xy2d', hxy2d', hxy2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [AffineNielsPoint.«64bit-tables».toAffineNiels_def, AffineNiels.neg,
      toField_neg_of_mod hxy2d']
  · exact ⟨hymx, hypx, limbs_lt_of_le (by decide) hxy2d'_lt⟩

/-- `Neg for &AffineNielsPoint` negates the represented point. -/
theorem neg_spec (self : AffineNielsPoint.«64bit-tables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    neg self ⦃ (r : AffineNielsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (neg_toAffineNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«64bit-tables».onCurve_iff,
      AffineNielsPoint.«64bit-tables».toPoint_def, hr,
      AffineNielsPoint.«64bit-tables».toPoint_def]
    exact ⟨AffineNiels.onCurve_neg hon, AffineNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegAffineNielsPoint64bit-tables»
end «Shared0AffineNielsPoint64bit-tables».Insts

namespace «Shared0AffineNielsPoint32bit-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithNegAffineNielsPoint32bit-tables»

/-- `Neg for &AffineNielsPoint`: swap `y + x` and `y - x`, negate `xy2d`; limbs `< 2^27`. -/
@[step]
theorem neg_toAffineNiels (self : AffineNielsPoint.«32bit-tables») (hself : self.LimbsLt 27) :
    neg self ⦃ (r : AffineNielsPoint.«32bit-tables») =>
      r.toAffineNiels = self.toAffineNiels.neg ∧ r.LimbsLt 27 ⦄ := by
  obtain ⟨hypx, hymx, hxy2d⟩ := hself
  unfold neg
  step as ⟨xy2d', hxy2d', hxy2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [AffineNielsPoint.«32bit-tables».toAffineNiels_def, AffineNiels.neg,
      toField_neg_of_mod hxy2d']
  · exact ⟨hymx, hypx, limbs_lt_of_le (by decide) hxy2d'_lt⟩

/-- `Neg for &AffineNielsPoint` negates the represented point. -/
theorem neg_spec (self : AffineNielsPoint.«32bit-tables») (hself : self.LimbsLt 27)
    (hon : self.OnCurve) :
    neg self ⦃ (r : AffineNielsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (neg_toAffineNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«32bit-tables».onCurve_iff,
      AffineNielsPoint.«32bit-tables».toPoint_def, hr,
      AffineNielsPoint.«32bit-tables».toPoint_def]
    exact ⟨AffineNiels.onCurve_neg hon, AffineNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegAffineNielsPoint32bit-tables»
end «Shared0AffineNielsPoint32bit-tables».Insts

namespace «Shared0AffineNielsPoint64bit-notables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithNegAffineNielsPoint64bit-notables»

/-- `Neg for &AffineNielsPoint`: swap `y + x` and `y - x`, negate `xy2d`; limbs `< 2^54`. -/
@[step]
theorem neg_toAffineNiels (self : AffineNielsPoint.«64bit-notables») (hself : self.LimbsLt 54) :
    neg self ⦃ (r : AffineNielsPoint.«64bit-notables») =>
      r.toAffineNiels = self.toAffineNiels.neg ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨hypx, hymx, hxy2d⟩ := hself
  unfold neg
  step as ⟨xy2d', hxy2d', hxy2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [AffineNielsPoint.«64bit-notables».toAffineNiels_def, AffineNiels.neg,
      toField_neg_of_mod hxy2d']
  · exact ⟨hymx, hypx, limbs_lt_of_le (by decide) hxy2d'_lt⟩

/-- `Neg for &AffineNielsPoint` negates the represented point. -/
theorem neg_spec (self : AffineNielsPoint.«64bit-notables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    neg self ⦃ (r : AffineNielsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (neg_toAffineNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«64bit-notables».onCurve_iff,
      AffineNielsPoint.«64bit-notables».toPoint_def, hr,
      AffineNielsPoint.«64bit-notables».toPoint_def]
    exact ⟨AffineNiels.onCurve_neg hon, AffineNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegAffineNielsPoint64bit-notables»
end «Shared0AffineNielsPoint64bit-notables».Insts

namespace «Shared0AffineNielsPoint32bit-notables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithNegAffineNielsPoint32bit-notables»

/-- `Neg for &AffineNielsPoint`: swap `y + x` and `y - x`, negate `xy2d`; limbs `< 2^27`. -/
@[step]
theorem neg_toAffineNiels (self : AffineNielsPoint.«32bit-notables») (hself : self.LimbsLt 27) :
    neg self ⦃ (r : AffineNielsPoint.«32bit-notables») =>
      r.toAffineNiels = self.toAffineNiels.neg ∧ r.LimbsLt 27 ⦄ := by
  obtain ⟨hypx, hymx, hxy2d⟩ := hself
  unfold neg
  step as ⟨xy2d', hxy2d', hxy2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [AffineNielsPoint.«32bit-notables».toAffineNiels_def, AffineNiels.neg,
      toField_neg_of_mod hxy2d']
  · exact ⟨hymx, hypx, limbs_lt_of_le (by decide) hxy2d'_lt⟩

/-- `Neg for &AffineNielsPoint` negates the represented point. -/
theorem neg_spec (self : AffineNielsPoint.«32bit-notables») (hself : self.LimbsLt 27)
    (hon : self.OnCurve) :
    neg self ⦃ (r : AffineNielsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (neg_toAffineNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«32bit-notables».onCurve_iff,
      AffineNielsPoint.«32bit-notables».toPoint_def, hr,
      AffineNielsPoint.«32bit-notables».toPoint_def]
    exact ⟨AffineNiels.onCurve_neg hon, AffineNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegAffineNielsPoint32bit-notables»
end «Shared0AffineNielsPoint32bit-notables».Insts

end Curve25519Dalek
