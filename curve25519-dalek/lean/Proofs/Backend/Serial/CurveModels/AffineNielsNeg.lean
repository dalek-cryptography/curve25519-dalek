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

namespace «Shared0AffineNielsPointx86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithNegAffineNielsPointx86_64-tables»

/-- `Neg for &AffineNielsPoint`: swap `y + x` and `y - x`, negate `xy2d`; limbs `< 2^54`. -/
@[step]
theorem neg_spec (self : AffineNielsPoint.«x86_64-tables») (hself : self.LimbsLt 54) :
    neg self ⦃ (r : AffineNielsPoint.«x86_64-tables») =>
      r.toAffineNiels = self.toAffineNiels.neg ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨hypx, hymx, hxy2d⟩ := hself
  unfold neg
  step as ⟨xy2d', hxy2d', hxy2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [AffineNielsPoint.«x86_64-tables».toAffineNiels_def, AffineNiels.neg,
      toField_neg_of_mod hxy2d']
  · exact ⟨hymx, hypx, limbs_lt_of_le (by decide) hxy2d'_lt⟩

/-- `Neg for &AffineNielsPoint` negates the represented point. -/
theorem neg_spec_point (self : AffineNielsPoint.«x86_64-tables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    neg self ⦃ (r : AffineNielsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (neg_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«x86_64-tables».onCurve_iff,
      AffineNielsPoint.«x86_64-tables».toPoint_def, hr,
      AffineNielsPoint.«x86_64-tables».toPoint_def]
    exact ⟨AffineNiels.onCurve_neg hon, AffineNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegAffineNielsPointx86_64-tables»
end «Shared0AffineNielsPointx86_64-tables».Insts

namespace «Shared0AffineNielsPointi686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithNegAffineNielsPointi686-tables»

/-- `Neg for &AffineNielsPoint`: swap `y + x` and `y - x`, negate `xy2d`; limbs `< 2^27`. -/
@[step]
theorem neg_spec (self : AffineNielsPoint.«i686-tables») (hself : self.LimbsLt 27) :
    neg self ⦃ (r : AffineNielsPoint.«i686-tables») =>
      r.toAffineNiels = self.toAffineNiels.neg ∧ r.LimbsLt 27 ⦄ := by
  obtain ⟨hypx, hymx, hxy2d⟩ := hself
  unfold neg
  step as ⟨xy2d', hxy2d', hxy2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [AffineNielsPoint.«i686-tables».toAffineNiels_def, AffineNiels.neg,
      toField_neg_of_mod hxy2d']
  · exact ⟨hymx, hypx, limbs_lt_of_le (by decide) hxy2d'_lt⟩

/-- `Neg for &AffineNielsPoint` negates the represented point. -/
theorem neg_spec_point (self : AffineNielsPoint.«i686-tables») (hself : self.LimbsLt 27)
    (hon : self.OnCurve) :
    neg self ⦃ (r : AffineNielsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (neg_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«i686-tables».onCurve_iff,
      AffineNielsPoint.«i686-tables».toPoint_def, hr,
      AffineNielsPoint.«i686-tables».toPoint_def]
    exact ⟨AffineNiels.onCurve_neg hon, AffineNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegAffineNielsPointi686-tables»
end «Shared0AffineNielsPointi686-tables».Insts

namespace «Shared0AffineNielsPointx86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithNegAffineNielsPointx86_64-no-tables»

/-- `Neg for &AffineNielsPoint`: swap `y + x` and `y - x`, negate `xy2d`; limbs `< 2^54`. -/
@[step]
theorem neg_spec (self : AffineNielsPoint.«x86_64-no-tables») (hself : self.LimbsLt 54) :
    neg self ⦃ (r : AffineNielsPoint.«x86_64-no-tables») =>
      r.toAffineNiels = self.toAffineNiels.neg ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨hypx, hymx, hxy2d⟩ := hself
  unfold neg
  step as ⟨xy2d', hxy2d', hxy2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [AffineNielsPoint.«x86_64-no-tables».toAffineNiels_def, AffineNiels.neg,
      toField_neg_of_mod hxy2d']
  · exact ⟨hymx, hypx, limbs_lt_of_le (by decide) hxy2d'_lt⟩

/-- `Neg for &AffineNielsPoint` negates the represented point. -/
theorem neg_spec_point (self : AffineNielsPoint.«x86_64-no-tables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    neg self ⦃ (r : AffineNielsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (neg_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«x86_64-no-tables».onCurve_iff,
      AffineNielsPoint.«x86_64-no-tables».toPoint_def, hr,
      AffineNielsPoint.«x86_64-no-tables».toPoint_def]
    exact ⟨AffineNiels.onCurve_neg hon, AffineNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegAffineNielsPointx86_64-no-tables»
end «Shared0AffineNielsPointx86_64-no-tables».Insts

namespace «Shared0AffineNielsPointi686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithNegAffineNielsPointi686-no-tables»

/-- `Neg for &AffineNielsPoint`: swap `y + x` and `y - x`, negate `xy2d`; limbs `< 2^27`. -/
@[step]
theorem neg_spec (self : AffineNielsPoint.«i686-no-tables») (hself : self.LimbsLt 27) :
    neg self ⦃ (r : AffineNielsPoint.«i686-no-tables») =>
      r.toAffineNiels = self.toAffineNiels.neg ∧ r.LimbsLt 27 ⦄ := by
  obtain ⟨hypx, hymx, hxy2d⟩ := hself
  unfold neg
  step as ⟨xy2d', hxy2d', hxy2d'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [AffineNielsPoint.«i686-no-tables».toAffineNiels_def, AffineNiels.neg,
      toField_neg_of_mod hxy2d']
  · exact ⟨hymx, hypx, limbs_lt_of_le (by decide) hxy2d'_lt⟩

/-- `Neg for &AffineNielsPoint` negates the represented point. -/
theorem neg_spec_point (self : AffineNielsPoint.«i686-no-tables») (hself : self.LimbsLt 27)
    (hon : self.OnCurve) :
    neg self ⦃ (r : AffineNielsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (neg_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«i686-no-tables».onCurve_iff,
      AffineNielsPoint.«i686-no-tables».toPoint_def, hr,
      AffineNielsPoint.«i686-no-tables».toPoint_def]
    exact ⟨AffineNiels.onCurve_neg hon, AffineNiels.toPoint_neg hon, hb⟩

end «CoreOpsArithNegAffineNielsPointi686-no-tables»
end «Shared0AffineNielsPointi686-no-tables».Insts

end Curve25519Dalek
