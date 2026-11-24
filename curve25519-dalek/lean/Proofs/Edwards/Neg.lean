module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Backend.Serial.U64.Field.Neg
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.Neg
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek

namespace «Shared0EdwardsPoint64bit-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithNegEdwardsPoint64bit-tables»

/-- `Neg for &EdwardsPoint`: `(-X : Y : Z : -T)`, limbs `< 2^52`. -/
@[step]
theorem neg_toExtended (self : edwards.EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52) :
    neg self ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.toExtended = self.toExtended.neg ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold neg
  step as ⟨X', hX', hX'_lt⟩
  step as ⟨T', hT', hT'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [edwards.EdwardsPoint.«64bit-tables».toExtended_def, Extended.neg,
      toField_neg_of_mod hX', toField_neg_of_mod hT']
  · exact ⟨limbs_lt_of_le (by decide) hX'_lt, hY, hZ, limbs_lt_of_le (by decide) hT'_lt⟩

/-- The point-level reading of the postcondition of `neg_toExtended`. -/
private theorem point_of_post {self r : edwards.EdwardsPoint.«64bit-tables»}
    (hon : self.OnCurve) (h : r.toExtended = self.toExtended.neg ∧ r.LimbsLt 52) :
    r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 52 := by
  obtain ⟨hr, hb⟩ := h
  rw [edwards.EdwardsPoint.«64bit-tables».onCurve_iff,
    edwards.EdwardsPoint.«64bit-tables».toPoint_def, hr,
    edwards.EdwardsPoint.«64bit-tables».toPoint_def]
  exact ⟨Extended.onCurve_neg hon, Extended.toPoint_neg hon, hb⟩

/-- `Neg for &EdwardsPoint` negates the represented point. -/
theorem neg_spec (self : edwards.EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    neg self ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (neg_toExtended self hself) fun _ => point_of_post hon

end «CoreOpsArithNegEdwardsPoint64bit-tables»
end «Shared0EdwardsPoint64bit-tables».Insts

namespace «Shared0EdwardsPoint32bit-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithNegEdwardsPoint32bit-tables»

/-- `Neg for &EdwardsPoint`: `(-X : Y : Z : -T)`, limbs `< 2^26`. -/
@[step]
theorem neg_toExtended (self : edwards.EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26) :
    neg self ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.toExtended = self.toExtended.neg ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold neg
  step as ⟨X', hX', hX'_lt⟩
  step as ⟨T', hT', hT'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [edwards.EdwardsPoint.«32bit-tables».toExtended_def, Extended.neg,
      toField_neg_of_mod hX', toField_neg_of_mod hT']
  · exact ⟨limbs_lt_of_le (by decide) hX'_lt, hY, hZ, limbs_lt_of_le (by decide) hT'_lt⟩

/-- The point-level reading of the postcondition of `neg_toExtended`. -/
private theorem point_of_post {self r : edwards.EdwardsPoint.«32bit-tables»}
    (hon : self.OnCurve) (h : r.toExtended = self.toExtended.neg ∧ r.LimbsLt 26) :
    r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 26 := by
  obtain ⟨hr, hb⟩ := h
  rw [edwards.EdwardsPoint.«32bit-tables».onCurve_iff,
    edwards.EdwardsPoint.«32bit-tables».toPoint_def, hr,
    edwards.EdwardsPoint.«32bit-tables».toPoint_def]
  exact ⟨Extended.onCurve_neg hon, Extended.toPoint_neg hon, hb⟩

/-- `Neg for &EdwardsPoint` negates the represented point. -/
theorem neg_spec (self : edwards.EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    neg self ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (neg_toExtended self hself) fun _ => point_of_post hon

end «CoreOpsArithNegEdwardsPoint32bit-tables»
end «Shared0EdwardsPoint32bit-tables».Insts

open «Shared0EdwardsPoint64bit-tables».Insts
open «CoreOpsArithNegEdwardsPoint64bit-tables» (point_of_post)

namespace edwards.EdwardsPoint.«64bit-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithNegEdwardsPoint64bit-tables»

/-- `Neg for EdwardsPoint` (by value): `(-X : Y : Z : -T)`, limbs `< 2^52`. -/
@[step]
theorem neg_toExtended (self : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52) :
    neg self ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.toExtended = self.toExtended.neg ∧ r.LimbsLt 52 ⦄ := by
  unfold neg
  step*

/-- `Neg for EdwardsPoint` (by value) negates the represented point. -/
theorem neg_spec (self : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    neg self ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (neg_toExtended self hself) fun _ => point_of_post hon

end «CoreOpsArithNegEdwardsPoint64bit-tables»
end edwards.EdwardsPoint.«64bit-tables».Insts

namespace edwards.EdwardsPoint.«32bit-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithNegEdwardsPoint32bit-tables» (point_of_post)

namespace «CoreOpsArithNegEdwardsPoint32bit-tables»

/-- `Neg for EdwardsPoint` (by value): `(-X : Y : Z : -T)`, limbs `< 2^26`. -/
@[step]
theorem neg_toExtended (self : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26) :
    neg self ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.toExtended = self.toExtended.neg ∧ r.LimbsLt 26 ⦄ := by
  unfold neg
  step*

/-- `Neg for EdwardsPoint` (by value) negates the represented point. -/
theorem neg_spec (self : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    neg self ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (neg_toExtended self hself) fun _ => point_of_post hon

end «CoreOpsArithNegEdwardsPoint32bit-tables»
end edwards.EdwardsPoint.«32bit-tables».Insts

namespace «Shared0EdwardsPoint64bit-notables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithNegEdwardsPoint64bit-notables»

/-- `Neg for &EdwardsPoint`: `(-X : Y : Z : -T)`, limbs `< 2^52`. -/
@[step]
theorem neg_toExtended (self : edwards.EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52) :
    neg self ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.toExtended = self.toExtended.neg ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold neg
  step as ⟨X', hX', hX'_lt⟩
  step as ⟨T', hT', hT'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [edwards.EdwardsPoint.«64bit-notables».toExtended_def, Extended.neg,
      toField_neg_of_mod hX', toField_neg_of_mod hT']
  · exact ⟨limbs_lt_of_le (by decide) hX'_lt, hY, hZ, limbs_lt_of_le (by decide) hT'_lt⟩

/-- The point-level reading of the postcondition of `neg_toExtended`. -/
private theorem point_of_post {self r : edwards.EdwardsPoint.«64bit-notables»}
    (hon : self.OnCurve) (h : r.toExtended = self.toExtended.neg ∧ r.LimbsLt 52) :
    r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 52 := by
  obtain ⟨hr, hb⟩ := h
  rw [edwards.EdwardsPoint.«64bit-notables».onCurve_iff,
    edwards.EdwardsPoint.«64bit-notables».toPoint_def, hr,
    edwards.EdwardsPoint.«64bit-notables».toPoint_def]
  exact ⟨Extended.onCurve_neg hon, Extended.toPoint_neg hon, hb⟩

/-- `Neg for &EdwardsPoint` negates the represented point. -/
theorem neg_spec (self : edwards.EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    neg self ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (neg_toExtended self hself) fun _ => point_of_post hon

end «CoreOpsArithNegEdwardsPoint64bit-notables»
end «Shared0EdwardsPoint64bit-notables».Insts

namespace «Shared0EdwardsPoint32bit-notables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithNegEdwardsPoint32bit-notables»

/-- `Neg for &EdwardsPoint`: `(-X : Y : Z : -T)`, limbs `< 2^26`. -/
@[step]
theorem neg_toExtended (self : edwards.EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26) :
    neg self ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.toExtended = self.toExtended.neg ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold neg
  step as ⟨X', hX', hX'_lt⟩
  step as ⟨T', hT', hT'_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [edwards.EdwardsPoint.«32bit-notables».toExtended_def, Extended.neg,
      toField_neg_of_mod hX', toField_neg_of_mod hT']
  · exact ⟨limbs_lt_of_le (by decide) hX'_lt, hY, hZ, limbs_lt_of_le (by decide) hT'_lt⟩

/-- The point-level reading of the postcondition of `neg_toExtended`. -/
private theorem point_of_post {self r : edwards.EdwardsPoint.«32bit-notables»}
    (hon : self.OnCurve) (h : r.toExtended = self.toExtended.neg ∧ r.LimbsLt 26) :
    r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 26 := by
  obtain ⟨hr, hb⟩ := h
  rw [edwards.EdwardsPoint.«32bit-notables».onCurve_iff,
    edwards.EdwardsPoint.«32bit-notables».toPoint_def, hr,
    edwards.EdwardsPoint.«32bit-notables».toPoint_def]
  exact ⟨Extended.onCurve_neg hon, Extended.toPoint_neg hon, hb⟩

/-- `Neg for &EdwardsPoint` negates the represented point. -/
theorem neg_spec (self : edwards.EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    neg self ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (neg_toExtended self hself) fun _ => point_of_post hon

end «CoreOpsArithNegEdwardsPoint32bit-notables»
end «Shared0EdwardsPoint32bit-notables».Insts

open «Shared0EdwardsPoint64bit-notables».Insts
open «CoreOpsArithNegEdwardsPoint64bit-notables» (point_of_post)

namespace edwards.EdwardsPoint.«64bit-notables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithNegEdwardsPoint64bit-notables»

/-- `Neg for EdwardsPoint` (by value): `(-X : Y : Z : -T)`, limbs `< 2^52`. -/
@[step]
theorem neg_toExtended (self : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52) :
    neg self ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.toExtended = self.toExtended.neg ∧ r.LimbsLt 52 ⦄ := by
  unfold neg
  step*

/-- `Neg for EdwardsPoint` (by value) negates the represented point. -/
theorem neg_spec (self : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    neg self ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (neg_toExtended self hself) fun _ => point_of_post hon

end «CoreOpsArithNegEdwardsPoint64bit-notables»
end edwards.EdwardsPoint.«64bit-notables».Insts

namespace edwards.EdwardsPoint.«32bit-notables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPoint32bit-notables».Insts
open «CoreOpsArithNegEdwardsPoint32bit-notables» (point_of_post)

namespace «CoreOpsArithNegEdwardsPoint32bit-notables»

/-- `Neg for EdwardsPoint` (by value): `(-X : Y : Z : -T)`, limbs `< 2^26`. -/
@[step]
theorem neg_toExtended (self : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26) :
    neg self ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.toExtended = self.toExtended.neg ∧ r.LimbsLt 26 ⦄ := by
  unfold neg
  step*

/-- `Neg for EdwardsPoint` (by value) negates the represented point. -/
theorem neg_spec (self : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    neg self ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (neg_toExtended self hself) fun _ => point_of_post hon

end «CoreOpsArithNegEdwardsPoint32bit-notables»
end edwards.EdwardsPoint.«32bit-notables».Insts

end Curve25519Dalek
