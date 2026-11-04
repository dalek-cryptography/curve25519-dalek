/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.CurveModels
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

namespace «Shared0ProjectiveNielsPointx86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithNegProjectiveNielsPointx86_64-tables»

/-- `Neg for &ProjectiveNielsPoint`: swap `Y + X` and `Y - X`, negate `T2d`; limbs `< 2^54`. -/
@[step]
theorem neg_spec (self : ProjectiveNielsPoint.«x86_64-tables») (hself : self.LimbsLt 54) :
    neg self ⦃ (r : ProjectiveNielsPoint.«x86_64-tables») =>
      r.toProjectiveNiels = self.toProjectiveNiels.neg ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨hYpX, hYmX, hZ, hT2d⟩ := hself
  unfold neg
  step as ⟨T2d', hT2d', hT2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«x86_64-tables».toProjectiveNiels_def, ProjectiveNiels.neg,
      toField_neg_of_mod hT2d']
  · exact ⟨hYmX, hYpX, hZ, limbs_lt_of_le (by decide) hT2d'_lt⟩

/-- `Neg for &ProjectiveNielsPoint` negates the represented point. -/
theorem neg_spec_point (self : ProjectiveNielsPoint.«x86_64-tables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ProjectiveNielsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (neg_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«x86_64-tables».onCurve_iff,
      ProjectiveNielsPoint.«x86_64-tables».toPoint_def, hr,
      ProjectiveNielsPoint.«x86_64-tables».toPoint_def]
    exact ⟨ProjectiveNiels.onCurve_neg hon, ProjectiveNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegProjectiveNielsPointx86_64-tables»
end «Shared0ProjectiveNielsPointx86_64-tables».Insts

namespace «Shared0ProjectiveNielsPointi686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithNegProjectiveNielsPointi686-tables»

/-- `Neg for &ProjectiveNielsPoint`: swap `Y + X` and `Y - X`, negate `T2d`; limbs `< 2^27`. -/
@[step]
theorem neg_spec (self : ProjectiveNielsPoint.«i686-tables») (hself : self.LimbsLt 27) :
    neg self ⦃ (r : ProjectiveNielsPoint.«i686-tables») =>
      r.toProjectiveNiels = self.toProjectiveNiels.neg ∧ r.LimbsLt 27 ⦄ := by
  obtain ⟨hYpX, hYmX, hZ, hT2d⟩ := hself
  unfold neg
  step as ⟨T2d', hT2d', hT2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«i686-tables».toProjectiveNiels_def, ProjectiveNiels.neg,
      toField_neg_of_mod hT2d']
  · exact ⟨hYmX, hYpX, hZ, limbs_lt_of_le (by decide) hT2d'_lt⟩

/-- `Neg for &ProjectiveNielsPoint` negates the represented point. -/
theorem neg_spec_point (self : ProjectiveNielsPoint.«i686-tables») (hself : self.LimbsLt 27)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ProjectiveNielsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (neg_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«i686-tables».onCurve_iff,
      ProjectiveNielsPoint.«i686-tables».toPoint_def, hr,
      ProjectiveNielsPoint.«i686-tables».toPoint_def]
    exact ⟨ProjectiveNiels.onCurve_neg hon, ProjectiveNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegProjectiveNielsPointi686-tables»
end «Shared0ProjectiveNielsPointi686-tables».Insts

namespace «Shared0ProjectiveNielsPointx86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithNegProjectiveNielsPointx86_64-no-tables»

/-- `Neg for &ProjectiveNielsPoint`: swap `Y + X` and `Y - X`, negate `T2d`; limbs `< 2^54`. -/
@[step]
theorem neg_spec (self : ProjectiveNielsPoint.«x86_64-no-tables») (hself : self.LimbsLt 54) :
    neg self ⦃ (r : ProjectiveNielsPoint.«x86_64-no-tables») =>
      r.toProjectiveNiels = self.toProjectiveNiels.neg ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨hYpX, hYmX, hZ, hT2d⟩ := hself
  unfold neg
  step as ⟨T2d', hT2d', hT2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«x86_64-no-tables».toProjectiveNiels_def, ProjectiveNiels.neg,
      toField_neg_of_mod hT2d']
  · exact ⟨hYmX, hYpX, hZ, limbs_lt_of_le (by decide) hT2d'_lt⟩

/-- `Neg for &ProjectiveNielsPoint` negates the represented point. -/
theorem neg_spec_point (self : ProjectiveNielsPoint.«x86_64-no-tables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ProjectiveNielsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (neg_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«x86_64-no-tables».onCurve_iff,
      ProjectiveNielsPoint.«x86_64-no-tables».toPoint_def, hr,
      ProjectiveNielsPoint.«x86_64-no-tables».toPoint_def]
    exact ⟨ProjectiveNiels.onCurve_neg hon, ProjectiveNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegProjectiveNielsPointx86_64-no-tables»
end «Shared0ProjectiveNielsPointx86_64-no-tables».Insts

namespace «Shared0ProjectiveNielsPointi686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithNegProjectiveNielsPointi686-no-tables»

/-- `Neg for &ProjectiveNielsPoint`: swap `Y + X` and `Y - X`, negate `T2d`; limbs `< 2^27`. -/
@[step]
theorem neg_spec (self : ProjectiveNielsPoint.«i686-no-tables») (hself : self.LimbsLt 27) :
    neg self ⦃ (r : ProjectiveNielsPoint.«i686-no-tables») =>
      r.toProjectiveNiels = self.toProjectiveNiels.neg ∧ r.LimbsLt 27 ⦄ := by
  obtain ⟨hYpX, hYmX, hZ, hT2d⟩ := hself
  unfold neg
  step as ⟨T2d', hT2d', hT2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«i686-no-tables».toProjectiveNiels_def, ProjectiveNiels.neg,
      toField_neg_of_mod hT2d']
  · exact ⟨hYmX, hYpX, hZ, limbs_lt_of_le (by decide) hT2d'_lt⟩

/-- `Neg for &ProjectiveNielsPoint` negates the represented point. -/
theorem neg_spec_point (self : ProjectiveNielsPoint.«i686-no-tables») (hself : self.LimbsLt 27)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ProjectiveNielsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (neg_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«i686-no-tables».onCurve_iff,
      ProjectiveNielsPoint.«i686-no-tables».toPoint_def, hr,
      ProjectiveNielsPoint.«i686-no-tables».toPoint_def]
    exact ⟨ProjectiveNiels.onCurve_neg hon, ProjectiveNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegProjectiveNielsPointi686-no-tables»
end «Shared0ProjectiveNielsPointi686-no-tables».Insts

end Curve25519Dalek
