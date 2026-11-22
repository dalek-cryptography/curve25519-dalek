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

/-- `&EdwardsPoint - &AffineNielsPoint` over a backend. -/
@[expose] def subAffineNiels {P : Type} (mk : B.F → B.F → B.F → B.F → P)
    (X Y Z T ypx ymx xy2d : B.F) : Result P := do
  let Y_plus_X ← B.add Y X
  let Y_minus_X ← B.sub Y X
  let PM ← B.mul Y_plus_X ymx
  let MP ← B.mul Y_minus_X ypx
  let Txy2d ← B.mul T xy2d
  let Z2 ← B.add Z Z
  let fe ← B.sub PM MP
  let fe1 ← B.add PM MP
  let fe2 ← B.sub Z2 Txy2d
  let fe3 ← B.add Z2 Txy2d
  ok (mk fe fe1 fe2 fe3)

/-- `subAffineNiels` computes `Extended.subAffineNiels`. -/
theorem subAffineNiels_spec
    (hadd : B.AddSpec) (hadd2 : B.AddSum2Spec) (hsub : B.SubSpec) (hmul : B.MulSpec)
    {P : Type} (mk : B.F → B.F → B.F → B.F → P)
    (X Y Z T ypx ymx xy2d : B.F) (hX : B.Red X) (hY : B.Red Y) (hZ : B.Red Z) (hT : B.Red T)
    (hypx : B.Niels ypx) (hymx : B.Niels ymx) (hxy2d : B.Niels xy2d) :
    B.subAffineNiels mk X Y Z T ypx ymx xy2d ⦃ r => ∃ a b c d, r = mk a b c d ∧
      (⟨B.toField a, B.toField b, B.toField c, B.toField d⟩ : edwards.Completed) =
        (⟨B.toField X, B.toField Y, B.toField Z, B.toField T⟩ : edwards.Extended).subAffineNiels
          ⟨B.toField ypx, B.toField ymx, B.toField xy2d⟩ ∧
      B.MulIn a ∧ B.MulIn b ∧ B.MulIn c ∧ B.MulIn d ⦄ := by
  unfold subAffineNiels
  step with hadd Y X hY hX as ⟨yx, hyx, hyx'⟩
  step with hsub Y X (B.red_mulIn hY) (B.red_mulIn hX) as ⟨y_x, hy_x, hy_x'⟩
  step with hmul yx ymx (B.sum2_mulIn hyx') (B.niels_mulIn hymx) as ⟨pm, hpm, hpm'⟩
  step with hmul y_x ypx (B.red_mulIn hy_x') (B.niels_mulIn hypx) as ⟨mp, hmp, hmp'⟩
  step with hmul T xy2d (B.red_mulIn hT) (B.niels_mulIn hxy2d) as ⟨txy, htxy, htxy'⟩
  step with hadd Z Z hZ hZ as ⟨z2, hz2, z2'⟩
  step with hsub pm mp (B.red_mulIn hpm') (B.red_mulIn hmp') as ⟨a, ha, ha'⟩
  step with hadd pm mp hpm' hmp' as ⟨b, hb, hb'⟩
  step with hsub z2 txy (B.sum2_mulIn z2') (B.red_mulIn htxy') as ⟨c, hc, hc'⟩
  step with hadd2 z2 txy z2' htxy' as ⟨d, hd, hd'⟩
  refine ⟨a, b, c, d, rfl, ?_, B.red_mulIn ha', B.sum2_mulIn hb', B.red_mulIn hc', hd'⟩
  rw [ha, hb, hc, hd, hpm, hmp, hz2, htxy, hyx, hy_x]
  rfl

end Curve25519Dalek.Backend

namespace Curve25519Dalek

namespace «Shared0EdwardsPoint64bit-tables».Insts

namespace «CoreOpsArithSubSharedAAffineNielsPoint64bit-tablesCompletedPoint64bit-tables»

theorem sub_eq (self : edwards.EdwardsPoint.«64bit-tables»)
    (other : AffineNielsPoint.«64bit-tables») :
    sub self other = Backend.subAffineNiels Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«64bit-tables»))
      self.X self.Y self.Z self.T other.y_plus_x other.y_minus_x other.xy2d := rfl

/-- `Sub<&AffineNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.subAffineNiels`; limbs `< 2^52` and `< 2^54` in, `< 2^54` out. -/
@[step]
theorem sub_toCompleted (self : edwards.EdwardsPoint.«64bit-tables»)
    (other : AffineNielsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) :
    sub self other ⦃ (r : CompletedPoint.«64bit-tables») =>
      r.toCompleted = self.toExtended.subAffineNiels other.toAffineNiels ∧
        r.LimbsLt 54 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  obtain ⟨h5, h6, h7⟩ := hother
  rw [sub_eq]
  apply spec_mono (Backend.subAffineNiels_spec Backend.U64
    Backend.U64.add_spec Backend.U64.add_sum2_spec Backend.U64.sub_spec Backend.U64.mul_spec _ _ _ _
    _ _ _ _ h1 h2 h3 h4 h5 h6 h7)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«64bit-tables».toCompleted_def,
    edwards.EdwardsPoint.«64bit-tables».toExtended_def,
    AffineNielsPoint.«64bit-tables».toAffineNiels_def]; exact h, ha, hb, hc, hd⟩

/-- `Sub<&AffineNielsPoint> for &EdwardsPoint` subtracts the represented points. -/
theorem sub_spec (self : edwards.EdwardsPoint.«64bit-tables»)
    (other : AffineNielsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    sub self other ⦃ (r : CompletedPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (sub_toCompleted self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«64bit-tables».onCurve_iff,
      CompletedPoint.«64bit-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«64bit-tables».toPoint_def,
      AffineNielsPoint.«64bit-tables».toPoint_def]
    exact ⟨Extended.subAffineNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_subAffineNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithSubSharedAAffineNielsPoint64bit-tablesCompletedPoint64bit-tables»
end «Shared0EdwardsPoint64bit-tables».Insts

namespace «Shared0EdwardsPoint32bit-tables».Insts

namespace «CoreOpsArithSubSharedAAffineNielsPoint32bit-tablesCompletedPoint32bit-tables»

theorem sub_eq (self : edwards.EdwardsPoint.«32bit-tables»)
    (other : AffineNielsPoint.«32bit-tables») :
    sub self other = Backend.subAffineNiels Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«32bit-tables»))
      self.X self.Y self.Z self.T other.y_plus_x other.y_minus_x other.xy2d := rfl

/-- `Sub<&AffineNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.subAffineNiels`; limbs `< 2^26` and `< 2^27` in, `< 3 · 2^26` out. -/
@[step]
theorem sub_toCompleted (self : edwards.EdwardsPoint.«32bit-tables»)
    (other : AffineNielsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) :
    sub self other ⦃ (r : CompletedPoint.«32bit-tables») =>
      r.toCompleted = self.toExtended.subAffineNiels other.toAffineNiels ∧
        r.MulBounded ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  obtain ⟨h5, h6, h7⟩ := hother
  rw [sub_eq]
  apply spec_mono (Backend.subAffineNiels_spec Backend.U32
    Backend.U32.add_spec Backend.U32.add_sum2_spec Backend.U32.sub_spec Backend.U32.mul_spec _ _ _ _
    _ _ _ _ h1 h2 h3 h4 h5 h6 h7)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«32bit-tables».toCompleted_def,
    edwards.EdwardsPoint.«32bit-tables».toExtended_def,
    AffineNielsPoint.«32bit-tables».toAffineNiels_def]; exact h, ha, hb, hc, hd⟩

/-- `Sub<&AffineNielsPoint> for &EdwardsPoint` subtracts the represented points. -/
theorem sub_spec (self : edwards.EdwardsPoint.«32bit-tables»)
    (other : AffineNielsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    sub self other ⦃ (r : CompletedPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.MulBounded ⦄ :=
  spec_mono (sub_toCompleted self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«32bit-tables».onCurve_iff,
      CompletedPoint.«32bit-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«32bit-tables».toPoint_def,
      AffineNielsPoint.«32bit-tables».toPoint_def]
    exact ⟨Extended.subAffineNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_subAffineNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithSubSharedAAffineNielsPoint32bit-tablesCompletedPoint32bit-tables»
end «Shared0EdwardsPoint32bit-tables».Insts

namespace «Shared0EdwardsPoint64bit-notables».Insts

namespace «CoreOpsArithSubSharedAAffineNielsPoint64bit-notablesCompletedPoint64bit-notables»

theorem sub_eq (self : edwards.EdwardsPoint.«64bit-notables»)
    (other : AffineNielsPoint.«64bit-notables») :
    sub self other = Backend.subAffineNiels Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«64bit-notables»))
      self.X self.Y self.Z self.T other.y_plus_x other.y_minus_x other.xy2d := rfl

/-- `Sub<&AffineNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.subAffineNiels`; limbs `< 2^52` and `< 2^54` in, `< 2^54` out. -/
@[step]
theorem sub_toCompleted (self : edwards.EdwardsPoint.«64bit-notables»)
    (other : AffineNielsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) :
    sub self other ⦃ (r : CompletedPoint.«64bit-notables») =>
      r.toCompleted = self.toExtended.subAffineNiels other.toAffineNiels ∧
        r.LimbsLt 54 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  obtain ⟨h5, h6, h7⟩ := hother
  rw [sub_eq]
  apply spec_mono (Backend.subAffineNiels_spec Backend.U64
    Backend.U64.add_spec Backend.U64.add_sum2_spec Backend.U64.sub_spec Backend.U64.mul_spec _ _ _ _
    _ _ _ _ h1 h2 h3 h4 h5 h6 h7)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«64bit-notables».toCompleted_def,
    edwards.EdwardsPoint.«64bit-notables».toExtended_def,
    AffineNielsPoint.«64bit-notables».toAffineNiels_def]; exact h, ha, hb, hc, hd⟩

/-- `Sub<&AffineNielsPoint> for &EdwardsPoint` subtracts the represented points. -/
theorem sub_spec (self : edwards.EdwardsPoint.«64bit-notables»)
    (other : AffineNielsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    sub self other ⦃ (r : CompletedPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (sub_toCompleted self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«64bit-notables».onCurve_iff,
      CompletedPoint.«64bit-notables».toPoint_def, hr,
      edwards.EdwardsPoint.«64bit-notables».toPoint_def,
      AffineNielsPoint.«64bit-notables».toPoint_def]
    exact ⟨Extended.subAffineNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_subAffineNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithSubSharedAAffineNielsPoint64bit-notablesCompletedPoint64bit-notables»
end «Shared0EdwardsPoint64bit-notables».Insts

namespace «Shared0EdwardsPoint32bit-notables».Insts

namespace «CoreOpsArithSubSharedAAffineNielsPoint32bit-notablesCompletedPoint32bit-notables»

theorem sub_eq (self : edwards.EdwardsPoint.«32bit-notables»)
    (other : AffineNielsPoint.«32bit-notables») :
    sub self other = Backend.subAffineNiels Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«32bit-notables»))
      self.X self.Y self.Z self.T other.y_plus_x other.y_minus_x other.xy2d := rfl

/-- `Sub<&AffineNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.subAffineNiels`; limbs `< 2^26` and `< 2^27` in, `< 3 · 2^26` out. -/
@[step]
theorem sub_toCompleted (self : edwards.EdwardsPoint.«32bit-notables»)
    (other : AffineNielsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) :
    sub self other ⦃ (r : CompletedPoint.«32bit-notables») =>
      r.toCompleted = self.toExtended.subAffineNiels other.toAffineNiels ∧
        r.MulBounded ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  obtain ⟨h5, h6, h7⟩ := hother
  rw [sub_eq]
  apply spec_mono (Backend.subAffineNiels_spec Backend.U32
    Backend.U32.add_spec Backend.U32.add_sum2_spec Backend.U32.sub_spec Backend.U32.mul_spec _ _ _ _
    _ _ _ _ h1 h2 h3 h4 h5 h6 h7)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«32bit-notables».toCompleted_def,
    edwards.EdwardsPoint.«32bit-notables».toExtended_def,
    AffineNielsPoint.«32bit-notables».toAffineNiels_def]; exact h, ha, hb, hc, hd⟩

/-- `Sub<&AffineNielsPoint> for &EdwardsPoint` subtracts the represented points. -/
theorem sub_spec (self : edwards.EdwardsPoint.«32bit-notables»)
    (other : AffineNielsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    sub self other ⦃ (r : CompletedPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.MulBounded ⦄ :=
  spec_mono (sub_toCompleted self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«32bit-notables».onCurve_iff,
      CompletedPoint.«32bit-notables».toPoint_def, hr,
      edwards.EdwardsPoint.«32bit-notables».toPoint_def,
      AffineNielsPoint.«32bit-notables».toPoint_def]
    exact ⟨Extended.subAffineNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_subAffineNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithSubSharedAAffineNielsPoint32bit-notablesCompletedPoint32bit-notables»
end «Shared0EdwardsPoint32bit-notables».Insts

end Curve25519Dalek
