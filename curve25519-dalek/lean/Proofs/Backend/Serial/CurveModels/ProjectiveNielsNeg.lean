/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

namespace «Shared0ProjectiveNielsPoint64bit-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithNegProjectiveNielsPoint64bit-tables»

/-- `Neg for &ProjectiveNielsPoint`: swap `Y + X` and `Y - X`, negate `T2d`; limbs `< 2^54`. -/
@[step]
theorem neg_toProjectiveNiels (self : ProjectiveNielsPoint.«64bit-tables») (hself : self.LimbsLt
    54) :
    neg self ⦃ (r : ProjectiveNielsPoint.«64bit-tables») =>
      r.toProjectiveNiels = self.toProjectiveNiels.neg ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨hYpX, hYmX, hZ, hT2d⟩ := hself
  unfold neg
  step as ⟨T2d', hT2d', hT2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«64bit-tables».toProjectiveNiels_def, ProjectiveNiels.neg,
      toField_neg_of_mod hT2d']
  · exact ⟨hYmX, hYpX, hZ, limbs_lt_of_le (by decide) hT2d'_lt⟩

/-- `Neg for &ProjectiveNielsPoint` negates the represented point. -/
theorem neg_spec (self : ProjectiveNielsPoint.«64bit-tables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ProjectiveNielsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (neg_toProjectiveNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«64bit-tables».onCurve_iff,
      ProjectiveNielsPoint.«64bit-tables».toPoint_def, hr,
      ProjectiveNielsPoint.«64bit-tables».toPoint_def]
    exact ⟨ProjectiveNiels.onCurve_neg hon, ProjectiveNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegProjectiveNielsPoint64bit-tables»
end «Shared0ProjectiveNielsPoint64bit-tables».Insts

namespace «Shared0ProjectiveNielsPoint32bit-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithNegProjectiveNielsPoint32bit-tables»

/-- `Neg for &ProjectiveNielsPoint`: swap `Y + X` and `Y - X`, negate `T2d`; limbs `< 2^27`. -/
@[step]
theorem neg_toProjectiveNiels (self : ProjectiveNielsPoint.«32bit-tables») (hself : self.LimbsLt 27)
    :
    neg self ⦃ (r : ProjectiveNielsPoint.«32bit-tables») =>
      r.toProjectiveNiels = self.toProjectiveNiels.neg ∧ r.LimbsLt 27 ⦄ := by
  obtain ⟨hYpX, hYmX, hZ, hT2d⟩ := hself
  unfold neg
  step as ⟨T2d', hT2d', hT2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«32bit-tables».toProjectiveNiels_def, ProjectiveNiels.neg,
      toField_neg_of_mod hT2d']
  · exact ⟨hYmX, hYpX, hZ, limbs_lt_of_le (by decide) hT2d'_lt⟩

/-- `Neg for &ProjectiveNielsPoint` negates the represented point. -/
theorem neg_spec (self : ProjectiveNielsPoint.«32bit-tables») (hself : self.LimbsLt 27)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ProjectiveNielsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (neg_toProjectiveNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«32bit-tables».onCurve_iff,
      ProjectiveNielsPoint.«32bit-tables».toPoint_def, hr,
      ProjectiveNielsPoint.«32bit-tables».toPoint_def]
    exact ⟨ProjectiveNiels.onCurve_neg hon, ProjectiveNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegProjectiveNielsPoint32bit-tables»
end «Shared0ProjectiveNielsPoint32bit-tables».Insts

namespace «Shared0ProjectiveNielsPoint64bit-notables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithNegProjectiveNielsPoint64bit-notables»

/-- `Neg for &ProjectiveNielsPoint`: swap `Y + X` and `Y - X`, negate `T2d`; limbs `< 2^54`. -/
@[step]
theorem neg_toProjectiveNiels (self : ProjectiveNielsPoint.«64bit-notables») (hself :
    self.LimbsLt 54) :
    neg self ⦃ (r : ProjectiveNielsPoint.«64bit-notables») =>
      r.toProjectiveNiels = self.toProjectiveNiels.neg ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨hYpX, hYmX, hZ, hT2d⟩ := hself
  unfold neg
  step as ⟨T2d', hT2d', hT2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«64bit-notables».toProjectiveNiels_def, ProjectiveNiels.neg,
      toField_neg_of_mod hT2d']
  · exact ⟨hYmX, hYpX, hZ, limbs_lt_of_le (by decide) hT2d'_lt⟩

/-- `Neg for &ProjectiveNielsPoint` negates the represented point. -/
theorem neg_spec (self : ProjectiveNielsPoint.«64bit-notables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ProjectiveNielsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (neg_toProjectiveNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«64bit-notables».onCurve_iff,
      ProjectiveNielsPoint.«64bit-notables».toPoint_def, hr,
      ProjectiveNielsPoint.«64bit-notables».toPoint_def]
    exact ⟨ProjectiveNiels.onCurve_neg hon, ProjectiveNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegProjectiveNielsPoint64bit-notables»
end «Shared0ProjectiveNielsPoint64bit-notables».Insts

namespace «Shared0ProjectiveNielsPoint32bit-notables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithNegProjectiveNielsPoint32bit-notables»

/-- `Neg for &ProjectiveNielsPoint`: swap `Y + X` and `Y - X`, negate `T2d`; limbs `< 2^27`. -/
@[step]
theorem neg_toProjectiveNiels (self : ProjectiveNielsPoint.«32bit-notables») (hself : self.LimbsLt
    27) :
    neg self ⦃ (r : ProjectiveNielsPoint.«32bit-notables») =>
      r.toProjectiveNiels = self.toProjectiveNiels.neg ∧ r.LimbsLt 27 ⦄ := by
  obtain ⟨hYpX, hYmX, hZ, hT2d⟩ := hself
  unfold neg
  step as ⟨T2d', hT2d', hT2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«32bit-notables».toProjectiveNiels_def, ProjectiveNiels.neg,
      toField_neg_of_mod hT2d']
  · exact ⟨hYmX, hYpX, hZ, limbs_lt_of_le (by decide) hT2d'_lt⟩

/-- `Neg for &ProjectiveNielsPoint` negates the represented point. -/
theorem neg_spec (self : ProjectiveNielsPoint.«32bit-notables») (hself : self.LimbsLt 27)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ProjectiveNielsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (neg_toProjectiveNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«32bit-notables».onCurve_iff,
      ProjectiveNielsPoint.«32bit-notables».toPoint_def, hr,
      ProjectiveNielsPoint.«32bit-notables».toPoint_def]
    exact ⟨ProjectiveNiels.onCurve_neg hon, ProjectiveNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegProjectiveNielsPoint32bit-notables»
end «Shared0ProjectiveNielsPoint32bit-notables».Insts

end Curve25519Dalek
