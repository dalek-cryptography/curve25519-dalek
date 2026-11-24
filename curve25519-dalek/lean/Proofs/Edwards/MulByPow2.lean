module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.CurveModels.CompletedAsProjective
import Proofs.Backend.Serial.CurveModels.ProjectiveDouble
import Proofs.Edwards.AsProjective
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace «EdwardsPoint64bit-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- The loop of `mul_by_pow_2`: `end - start` projective doublings. -/
@[local step]
private theorem mul_by_pow_2_loop_spec (iter : core.ops.range.Range U32)
    (s : ProjectivePoint.«64bit-tables») (hiter : iter.start.val ≤ iter.end.val)
    (hs : s.LimbsLt 52) (hon : s.OnCurve) :
    mul_by_pow_2_loop iter s ⦃ (r : ProjectivePoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = 2 ^ (iter.end.val - iter.start.val) • s.toPoint ∧
        r.LimbsLt 52 ⦄ := by
  unfold mul_by_pow_2_loop
  apply loop.spec_decr_nat (measure := fun (it, _) => it.end.val - it.start.val)
    (inv := fun (it, s') => it.end = iter.end ∧ iter.start.val ≤ it.start.val ∧
      it.start.val ≤ it.end.val ∧ s'.OnCurve ∧ s'.LimbsLt 52 ∧
      s'.toPoint = 2 ^ (it.start.val - iter.start.val) • s.toPoint)
  · rintro ⟨it, s'⟩ ⟨hend, hstart, hle, hon', hb', hs'⟩
    unfold mul_by_pow_2_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_U32_some_spec
        as ⟨o, it1, ho, hstart1, hend1⟩
      subst ho
      step with «ProjectivePoint64bit-tables».double_spec as ⟨r, hron, hr, hrb⟩
      step with «CompletedPoint64bit-tables».as_projective_spec
        as ⟨s1, hs1on, hs1, hs1b⟩
      refine ⟨hend1.trans hend, by scalar_tac, by rw [hend1]; scalar_tac, hs1on, hs1b, ?_,
        by rw [hend1]; scalar_tac⟩
      rw [hs1, hr, hs', smul_smul, ← pow_succ', hstart1, Nat.sub_add_comm hstart]
    · have hs'' : it.start.val = it.end.val := Nat.le_antisymm hle (Nat.le_of_not_lt hlt)
      step with core.iter.range.IteratorRange.next_U32_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      rw [← hend, ← hs'']
      exact ⟨hon', hs', hb'⟩
  · exact ⟨rfl, le_refl _, hiter, hon, hs, by simp⟩

/-- `EdwardsPoint::mul_by_pow_2`: `k` doublings, `2^k • P` (requires `k > 0`); limbs `< 2^52`. -/
@[step]
theorem mul_by_pow_2_spec (self : EdwardsPoint.«64bit-tables») (k : U32)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hk : 0 < k.val) :
    mul_by_pow_2 self k ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = 2 ^ k.val • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_by_pow_2
  step
  step with as_projective_spec as ⟨s, hson, hs, hsb⟩
  step as ⟨i, hi⟩
  step as ⟨s1, hs1on, hs1, hs1b⟩
  step with «ProjectivePoint64bit-tables».double_spec as ⟨cp, hcpon, hcp, hcpb⟩
  step with «CompletedPoint64bit-tables».as_extended_spec as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hcp, hs1, hs, smul_smul, ← pow_succ',
    show i.val - 0 + 1 = k.val by scalar_tac]

end «EdwardsPoint64bit-tables»

namespace «EdwardsPoint32bit-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- The loop of `mul_by_pow_2`: `end - start` projective doublings. -/
@[local step]
private theorem mul_by_pow_2_loop_spec (iter : core.ops.range.Range U32)
    (s : ProjectivePoint.«32bit-tables») (hiter : iter.start.val ≤ iter.end.val)
    (hs : s.LimbsLt 26) (hon : s.OnCurve) :
    mul_by_pow_2_loop iter s ⦃ (r : ProjectivePoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = 2 ^ (iter.end.val - iter.start.val) • s.toPoint ∧
        r.LimbsLt 26 ⦄ := by
  unfold mul_by_pow_2_loop
  apply loop.spec_decr_nat (measure := fun (it, _) => it.end.val - it.start.val)
    (inv := fun (it, s') => it.end = iter.end ∧ iter.start.val ≤ it.start.val ∧
      it.start.val ≤ it.end.val ∧ s'.OnCurve ∧ s'.LimbsLt 26 ∧
      s'.toPoint = 2 ^ (it.start.val - iter.start.val) • s.toPoint)
  · rintro ⟨it, s'⟩ ⟨hend, hstart, hle, hon', hb', hs'⟩
    unfold mul_by_pow_2_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_U32_some_spec
        as ⟨o, it1, ho, hstart1, hend1⟩
      subst ho
      step with «ProjectivePoint32bit-tables».double_spec as ⟨r, hron, hr, hrb⟩
      step with «CompletedPoint32bit-tables».as_projective_spec
        as ⟨s1, hs1on, hs1, hs1b⟩
      refine ⟨hend1.trans hend, by scalar_tac, by rw [hend1]; scalar_tac, hs1on, hs1b, ?_,
        by rw [hend1]; scalar_tac⟩
      rw [hs1, hr, hs', smul_smul, ← pow_succ', hstart1, Nat.sub_add_comm hstart]
    · have hs'' : it.start.val = it.end.val := Nat.le_antisymm hle (Nat.le_of_not_lt hlt)
      step with core.iter.range.IteratorRange.next_U32_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      rw [← hend, ← hs'']
      exact ⟨hon', hs', hb'⟩
  · exact ⟨rfl, le_refl _, hiter, hon, hs, by simp⟩

/-- `EdwardsPoint::mul_by_pow_2`: `k` doublings, `2^k • P` (requires `k > 0`); limbs `< 2^26`. -/
@[step]
theorem mul_by_pow_2_spec (self : EdwardsPoint.«32bit-tables») (k : U32)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hk : 0 < k.val) :
    mul_by_pow_2 self k ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = 2 ^ k.val • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_by_pow_2
  step
  step with as_projective_spec as ⟨s, hson, hs, hsb⟩
  step as ⟨i, hi⟩
  step as ⟨s1, hs1on, hs1, hs1b⟩
  step with «ProjectivePoint32bit-tables».double_spec as ⟨cp, hcpon, hcp, hcpb⟩
  step with «CompletedPoint32bit-tables».as_extended_spec as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hcp, hs1, hs, smul_smul, ← pow_succ',
    show i.val - 0 + 1 = k.val by scalar_tac]

end «EdwardsPoint32bit-tables»

namespace «EdwardsPoint64bit-notables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- The loop of `mul_by_pow_2`: `end - start` projective doublings. -/
@[local step]
private theorem mul_by_pow_2_loop_spec (iter : core.ops.range.Range U32)
    (s : ProjectivePoint.«64bit-notables») (hiter : iter.start.val ≤ iter.end.val)
    (hs : s.LimbsLt 52) (hon : s.OnCurve) :
    mul_by_pow_2_loop iter s ⦃ (r : ProjectivePoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = 2 ^ (iter.end.val - iter.start.val) • s.toPoint ∧
        r.LimbsLt 52 ⦄ := by
  unfold mul_by_pow_2_loop
  apply loop.spec_decr_nat (measure := fun (it, _) => it.end.val - it.start.val)
    (inv := fun (it, s') => it.end = iter.end ∧ iter.start.val ≤ it.start.val ∧
      it.start.val ≤ it.end.val ∧ s'.OnCurve ∧ s'.LimbsLt 52 ∧
      s'.toPoint = 2 ^ (it.start.val - iter.start.val) • s.toPoint)
  · rintro ⟨it, s'⟩ ⟨hend, hstart, hle, hon', hb', hs'⟩
    unfold mul_by_pow_2_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_U32_some_spec
        as ⟨o, it1, ho, hstart1, hend1⟩
      subst ho
      step with «ProjectivePoint64bit-notables».double_spec as ⟨r, hron, hr, hrb⟩
      step with «CompletedPoint64bit-notables».as_projective_spec
        as ⟨s1, hs1on, hs1, hs1b⟩
      refine ⟨hend1.trans hend, by scalar_tac, by rw [hend1]; scalar_tac, hs1on, hs1b, ?_,
        by rw [hend1]; scalar_tac⟩
      rw [hs1, hr, hs', smul_smul, ← pow_succ', hstart1, Nat.sub_add_comm hstart]
    · have hs'' : it.start.val = it.end.val := Nat.le_antisymm hle (Nat.le_of_not_lt hlt)
      step with core.iter.range.IteratorRange.next_U32_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      rw [← hend, ← hs'']
      exact ⟨hon', hs', hb'⟩
  · exact ⟨rfl, le_refl _, hiter, hon, hs, by simp⟩

/-- `EdwardsPoint::mul_by_pow_2`: `k` doublings, `2^k • P` (requires `k > 0`); limbs `< 2^52`. -/
@[step]
theorem mul_by_pow_2_spec (self : EdwardsPoint.«64bit-notables») (k : U32)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hk : 0 < k.val) :
    mul_by_pow_2 self k ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = 2 ^ k.val • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_by_pow_2
  step
  step with as_projective_spec as ⟨s, hson, hs, hsb⟩
  step as ⟨i, hi⟩
  step as ⟨s1, hs1on, hs1, hs1b⟩
  step with «ProjectivePoint64bit-notables».double_spec as ⟨cp, hcpon, hcp, hcpb⟩
  step with «CompletedPoint64bit-notables».as_extended_spec as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hcp, hs1, hs, smul_smul, ← pow_succ',
    show i.val - 0 + 1 = k.val by scalar_tac]

end «EdwardsPoint64bit-notables»

namespace «EdwardsPoint32bit-notables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- The loop of `mul_by_pow_2`: `end - start` projective doublings. -/
@[local step]
private theorem mul_by_pow_2_loop_spec (iter : core.ops.range.Range U32)
    (s : ProjectivePoint.«32bit-notables») (hiter : iter.start.val ≤ iter.end.val)
    (hs : s.LimbsLt 26) (hon : s.OnCurve) :
    mul_by_pow_2_loop iter s ⦃ (r : ProjectivePoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = 2 ^ (iter.end.val - iter.start.val) • s.toPoint ∧
        r.LimbsLt 26 ⦄ := by
  unfold mul_by_pow_2_loop
  apply loop.spec_decr_nat (measure := fun (it, _) => it.end.val - it.start.val)
    (inv := fun (it, s') => it.end = iter.end ∧ iter.start.val ≤ it.start.val ∧
      it.start.val ≤ it.end.val ∧ s'.OnCurve ∧ s'.LimbsLt 26 ∧
      s'.toPoint = 2 ^ (it.start.val - iter.start.val) • s.toPoint)
  · rintro ⟨it, s'⟩ ⟨hend, hstart, hle, hon', hb', hs'⟩
    unfold mul_by_pow_2_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_U32_some_spec
        as ⟨o, it1, ho, hstart1, hend1⟩
      subst ho
      step with «ProjectivePoint32bit-notables».double_spec as ⟨r, hron, hr, hrb⟩
      step with «CompletedPoint32bit-notables».as_projective_spec
        as ⟨s1, hs1on, hs1, hs1b⟩
      refine ⟨hend1.trans hend, by scalar_tac, by rw [hend1]; scalar_tac, hs1on, hs1b, ?_,
        by rw [hend1]; scalar_tac⟩
      rw [hs1, hr, hs', smul_smul, ← pow_succ', hstart1, Nat.sub_add_comm hstart]
    · have hs'' : it.start.val = it.end.val := Nat.le_antisymm hle (Nat.le_of_not_lt hlt)
      step with core.iter.range.IteratorRange.next_U32_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      rw [← hend, ← hs'']
      exact ⟨hon', hs', hb'⟩
  · exact ⟨rfl, le_refl _, hiter, hon, hs, by simp⟩

/-- `EdwardsPoint::mul_by_pow_2`: `k` doublings, `2^k • P` (requires `k > 0`); limbs `< 2^26`. -/
@[step]
theorem mul_by_pow_2_spec (self : EdwardsPoint.«32bit-notables») (k : U32)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hk : 0 < k.val) :
    mul_by_pow_2 self k ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = 2 ^ k.val • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_by_pow_2
  step
  step with as_projective_spec as ⟨s, hson, hs, hsb⟩
  step as ⟨i, hi⟩
  step as ⟨s1, hs1on, hs1, hs1b⟩
  step with «ProjectivePoint32bit-notables».double_spec as ⟨cp, hcpon, hcp, hcpb⟩
  step with «CompletedPoint32bit-notables».as_extended_spec as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hcp, hs1, hs, smul_smul, ← pow_succ',
    show i.val - 0 + 1 = k.val by scalar_tac]

end «EdwardsPoint32bit-notables»

end Curve25519Dalek.edwards
