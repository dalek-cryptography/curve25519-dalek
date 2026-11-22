/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Helpers.Coords
public import Proofs.Helpers.Backend.U32
public import Proofs.Helpers.Backend.U64
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.Backend

variable (B : Backend)

/-- `&EdwardsPoint - &ProjectiveNielsPoint` over a backend. -/
@[expose] def subProjectiveNiels {P : Type} (mk : B.F → B.F → B.F → B.F → P)
    (X Y Z T YpX YmX Z' T2d : B.F) : Result P := do
  let Y_plus_X ← B.add Y X
  let Y_minus_X ← B.sub Y X
  let PM ← B.mul Y_plus_X YmX
  let MP ← B.mul Y_minus_X YpX
  let TT2d ← B.mul T T2d
  let ZZ ← B.mul Z Z'
  let ZZ2 ← B.add ZZ ZZ
  let fe ← B.sub PM MP
  let fe1 ← B.add PM MP
  let fe2 ← B.sub ZZ2 TT2d
  let fe3 ← B.add ZZ2 TT2d
  ok (mk fe fe1 fe2 fe3)

/-- `subProjectiveNiels` computes `Extended.subProjectiveNiels`. -/
theorem subProjectiveNiels_spec
    (hadd : B.AddSpec) (hadd2 : B.AddSum2Spec) (hsub : B.SubSpec) (hmul : B.MulSpec)
    {P : Type} (mk : B.F → B.F → B.F → B.F → P)
    (X Y Z T YpX YmX Z' T2d : B.F) (hX : B.Red X) (hY : B.Red Y) (hZ : B.Red Z) (hT : B.Red T)
    (hYpX : B.Niels YpX) (hYmX : B.Niels YmX) (hZ' : B.Niels Z') (hT2d : B.Niels T2d) :
    B.subProjectiveNiels mk X Y Z T YpX YmX Z' T2d ⦃ r => ∃ a b c d, r = mk a b c d ∧
      (⟨B.toField a, B.toField b, B.toField c, B.toField d⟩ : edwards.Completed) =
        (⟨B.toField X, B.toField Y, B.toField Z, B.toField T⟩ :
          edwards.Extended).subProjectiveNiels
          ⟨B.toField YpX, B.toField YmX, B.toField Z', B.toField T2d⟩ ∧
      B.MulIn a ∧ B.MulIn b ∧ B.MulIn c ∧ B.MulIn d ⦄ := by
  unfold subProjectiveNiels
  step with hadd Y X hY hX as ⟨ypx, hypx, hypx'⟩
  step with hsub Y X (B.red_mulIn hY) (B.red_mulIn hX) as ⟨ymx, hymx, hymx'⟩
  step with hmul ypx YmX (B.sum2_mulIn hypx') (B.niels_mulIn hYmX) as ⟨pm, hpm, hpm'⟩
  step with hmul ymx YpX (B.red_mulIn hymx') (B.niels_mulIn hYpX) as ⟨mp, hmp, hmp'⟩
  step with hmul T T2d (B.red_mulIn hT) (B.niels_mulIn hT2d) as ⟨tt, htt, htt'⟩
  step with hmul Z Z' (B.red_mulIn hZ) (B.niels_mulIn hZ') as ⟨zz, hzz, hzz'⟩
  step with hadd zz zz hzz' hzz' as ⟨zz2, hzz2, hzz2'⟩
  step with hsub pm mp (B.red_mulIn hpm') (B.red_mulIn hmp') as ⟨a, ha, ha'⟩
  step with hadd pm mp hpm' hmp' as ⟨b, hb, hb'⟩
  step with hsub zz2 tt (B.sum2_mulIn hzz2') (B.red_mulIn htt') as ⟨c, hc, hc'⟩
  step with hadd2 zz2 tt hzz2' htt' as ⟨d, hd, hd'⟩
  refine ⟨a, b, c, d, rfl, ?_, B.red_mulIn ha', B.sum2_mulIn hb', B.red_mulIn hc', hd'⟩
  rw [ha, hb, hc, hd, hpm, hmp, hzz2, htt, hzz, hypx, hymx]
  rfl

end Curve25519Dalek.Backend

namespace Curve25519Dalek

namespace «Shared0EdwardsPoint64bit-tables».Insts

namespace «CoreOpsArithSubSharedAProjectiveNielsPoint64bit-tablesCompletedPoint64bit-tables»

theorem sub_eq (self : edwards.EdwardsPoint.«64bit-tables»)
    (other : ProjectiveNielsPoint.«64bit-tables») :
    sub self other = Backend.subProjectiveNiels Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«64bit-tables»))
      self.X self.Y self.Z self.T other.Y_plus_X other.Y_minus_X other.Z other.T2d := rfl

/-- `Sub<&ProjectiveNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.subProjectiveNiels`; limbs `< 2^52` and `< 2^54` in, `< 2^54` out. -/
@[step]
theorem sub_toCompleted (self : edwards.EdwardsPoint.«64bit-tables»)
    (other : ProjectiveNielsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) :
    sub self other ⦃ (r : CompletedPoint.«64bit-tables») =>
      r.toCompleted = self.toExtended.subProjectiveNiels other.toProjectiveNiels ∧
        r.LimbsLt 54 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  obtain ⟨h5, h6, h7, h8⟩ := hother
  rw [sub_eq]
  apply spec_mono (Backend.subProjectiveNiels_spec Backend.U64
    Backend.U64.add_spec Backend.U64.add_sum2_spec Backend.U64.sub_spec Backend.U64.mul_spec _ _ _ _
    _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«64bit-tables».toCompleted_def,
    edwards.EdwardsPoint.«64bit-tables».toExtended_def,
    ProjectiveNielsPoint.«64bit-tables».toProjectiveNiels_def]; exact h, ha, hb, hc, hd⟩

/-- `Sub<&ProjectiveNielsPoint> for &EdwardsPoint` subtracts the represented points. -/
theorem sub_spec (self : edwards.EdwardsPoint.«64bit-tables»)
    (other : ProjectiveNielsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    sub self other ⦃ (r : CompletedPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (sub_toCompleted self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«64bit-tables».onCurve_iff,
      CompletedPoint.«64bit-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«64bit-tables».toPoint_def,
      ProjectiveNielsPoint.«64bit-tables».toPoint_def]
    exact ⟨Extended.subProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_subProjectiveNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithSubSharedAProjectiveNielsPoint64bit-tablesCompletedPoint64bit-tables»
end «Shared0EdwardsPoint64bit-tables».Insts

namespace «Shared0EdwardsPoint32bit-tables».Insts

namespace «CoreOpsArithSubSharedAProjectiveNielsPoint32bit-tablesCompletedPoint32bit-tables»

theorem sub_eq (self : edwards.EdwardsPoint.«32bit-tables»)
    (other : ProjectiveNielsPoint.«32bit-tables») :
    sub self other = Backend.subProjectiveNiels Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«32bit-tables»))
      self.X self.Y self.Z self.T other.Y_plus_X other.Y_minus_X other.Z other.T2d := rfl

/-- `Sub<&ProjectiveNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.subProjectiveNiels`; limbs `< 2^26` and `< 2^27` in, `< 3 · 2^26` out. -/
@[step]
theorem sub_toCompleted (self : edwards.EdwardsPoint.«32bit-tables»)
    (other : ProjectiveNielsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) :
    sub self other ⦃ (r : CompletedPoint.«32bit-tables») =>
      r.toCompleted = self.toExtended.subProjectiveNiels other.toProjectiveNiels ∧
        r.MulBounded ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  obtain ⟨h5, h6, h7, h8⟩ := hother
  rw [sub_eq]
  apply spec_mono (Backend.subProjectiveNiels_spec Backend.U32
    Backend.U32.add_spec Backend.U32.add_sum2_spec Backend.U32.sub_spec Backend.U32.mul_spec _ _ _ _
    _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«32bit-tables».toCompleted_def,
    edwards.EdwardsPoint.«32bit-tables».toExtended_def,
    ProjectiveNielsPoint.«32bit-tables».toProjectiveNiels_def]; exact h, ha, hb, hc, hd⟩

/-- `Sub<&ProjectiveNielsPoint> for &EdwardsPoint` subtracts the represented points. -/
theorem sub_spec (self : edwards.EdwardsPoint.«32bit-tables»)
    (other : ProjectiveNielsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    sub self other ⦃ (r : CompletedPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.MulBounded ⦄ :=
  spec_mono (sub_toCompleted self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«32bit-tables».onCurve_iff,
      CompletedPoint.«32bit-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«32bit-tables».toPoint_def,
      ProjectiveNielsPoint.«32bit-tables».toPoint_def]
    exact ⟨Extended.subProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_subProjectiveNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithSubSharedAProjectiveNielsPoint32bit-tablesCompletedPoint32bit-tables»
end «Shared0EdwardsPoint32bit-tables».Insts

namespace «Shared0EdwardsPoint64bit-notables».Insts

namespace «CoreOpsArithSubSharedAProjectiveNielsPoint64bit-notablesCompletedPoint64bit-notables»

theorem sub_eq (self : edwards.EdwardsPoint.«64bit-notables»)
    (other : ProjectiveNielsPoint.«64bit-notables») :
    sub self other = Backend.subProjectiveNiels Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«64bit-notables»))
      self.X self.Y self.Z self.T other.Y_plus_X other.Y_minus_X other.Z other.T2d := rfl

/-- `Sub<&ProjectiveNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.subProjectiveNiels`; limbs `< 2^52` and `< 2^54` in, `< 2^54` out. -/
@[step]
theorem sub_toCompleted (self : edwards.EdwardsPoint.«64bit-notables»)
    (other : ProjectiveNielsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) :
    sub self other ⦃ (r : CompletedPoint.«64bit-notables») =>
      r.toCompleted = self.toExtended.subProjectiveNiels other.toProjectiveNiels ∧
        r.LimbsLt 54 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  obtain ⟨h5, h6, h7, h8⟩ := hother
  rw [sub_eq]
  apply spec_mono (Backend.subProjectiveNiels_spec Backend.U64
    Backend.U64.add_spec Backend.U64.add_sum2_spec Backend.U64.sub_spec Backend.U64.mul_spec _ _ _ _
    _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«64bit-notables».toCompleted_def,
    edwards.EdwardsPoint.«64bit-notables».toExtended_def,
    ProjectiveNielsPoint.«64bit-notables».toProjectiveNiels_def]; exact h, ha, hb, hc, hd⟩

/-- `Sub<&ProjectiveNielsPoint> for &EdwardsPoint` subtracts the represented points. -/
theorem sub_spec (self : edwards.EdwardsPoint.«64bit-notables»)
    (other : ProjectiveNielsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    sub self other ⦃ (r : CompletedPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (sub_toCompleted self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«64bit-notables».onCurve_iff,
      CompletedPoint.«64bit-notables».toPoint_def, hr,
      edwards.EdwardsPoint.«64bit-notables».toPoint_def,
      ProjectiveNielsPoint.«64bit-notables».toPoint_def]
    exact ⟨Extended.subProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_subProjectiveNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithSubSharedAProjectiveNielsPoint64bit-notablesCompletedPoint64bit-notables»
end «Shared0EdwardsPoint64bit-notables».Insts

namespace «Shared0EdwardsPoint32bit-notables».Insts

namespace «CoreOpsArithSubSharedAProjectiveNielsPoint32bit-notablesCompletedPoint32bit-notables»

theorem sub_eq (self : edwards.EdwardsPoint.«32bit-notables»)
    (other : ProjectiveNielsPoint.«32bit-notables») :
    sub self other = Backend.subProjectiveNiels Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«32bit-notables»))
      self.X self.Y self.Z self.T other.Y_plus_X other.Y_minus_X other.Z other.T2d := rfl

/-- `Sub<&ProjectiveNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.subProjectiveNiels`; limbs `< 2^26` and `< 2^27` in, `< 3 · 2^26` out. -/
@[step]
theorem sub_toCompleted (self : edwards.EdwardsPoint.«32bit-notables»)
    (other : ProjectiveNielsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) :
    sub self other ⦃ (r : CompletedPoint.«32bit-notables») =>
      r.toCompleted = self.toExtended.subProjectiveNiels other.toProjectiveNiels ∧
        r.MulBounded ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  obtain ⟨h5, h6, h7, h8⟩ := hother
  rw [sub_eq]
  apply spec_mono (Backend.subProjectiveNiels_spec Backend.U32
    Backend.U32.add_spec Backend.U32.add_sum2_spec Backend.U32.sub_spec Backend.U32.mul_spec _ _ _ _
    _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«32bit-notables».toCompleted_def,
    edwards.EdwardsPoint.«32bit-notables».toExtended_def,
    ProjectiveNielsPoint.«32bit-notables».toProjectiveNiels_def]; exact h, ha, hb, hc, hd⟩

/-- `Sub<&ProjectiveNielsPoint> for &EdwardsPoint` subtracts the represented points. -/
theorem sub_spec (self : edwards.EdwardsPoint.«32bit-notables»)
    (other : ProjectiveNielsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    sub self other ⦃ (r : CompletedPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.MulBounded ⦄ :=
  spec_mono (sub_toCompleted self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«32bit-notables».onCurve_iff,
      CompletedPoint.«32bit-notables».toPoint_def, hr,
      edwards.EdwardsPoint.«32bit-notables».toPoint_def,
      ProjectiveNielsPoint.«32bit-notables».toPoint_def]
    exact ⟨Extended.subProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_subProjectiveNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithSubSharedAProjectiveNielsPoint32bit-notablesCompletedPoint32bit-notables»
end «Shared0EdwardsPoint32bit-notables».Insts

end Curve25519Dalek
