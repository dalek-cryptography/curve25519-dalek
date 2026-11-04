/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
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

namespace «Shared0EdwardsPointx86_64-tables».Insts

namespace «CoreOpsArithSubSharedAAffineNielsPointx86_64-tablesCompletedPointx86_64-tables»

theorem sub_eq (self : edwards.EdwardsPoint.«x86_64-tables»)
    (other : AffineNielsPoint.«x86_64-tables») :
    sub self other = Backend.subAffineNiels Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«x86_64-tables»))
      self.X self.Y self.Z self.T other.y_plus_x other.y_minus_x other.xy2d := rfl

/-- `Sub<&AffineNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.subAffineNiels`; limbs `< 2^52` and `< 2^54` in, `< 2^54` out. -/
@[step]
theorem sub_spec (self : edwards.EdwardsPoint.«x86_64-tables»)
    (other : AffineNielsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) :
    sub self other ⦃ (r : CompletedPoint.«x86_64-tables») =>
      r.toCompleted = self.toExtended.subAffineNiels other.toAffineNiels ∧
        r.LimbsLt 54 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  obtain ⟨h5, h6, h7⟩ := hother
  rw [sub_eq]
  apply spec_mono (Backend.subAffineNiels_spec Backend.U64
    Backend.U64.add_spec Backend.U64.add_sum2_spec Backend.U64.sub_spec Backend.U64.mul_spec _ _ _ _
    _ _ _ _ h1 h2 h3 h4 h5 h6 h7)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«x86_64-tables».toCompleted_def,
    edwards.EdwardsPoint.«x86_64-tables».toExtended_def,
    AffineNielsPoint.«x86_64-tables».toAffineNiels_def]; exact h, ha, hb, hc, hd⟩

/-- `Sub<&AffineNielsPoint> for &EdwardsPoint` subtracts the represented points. -/
theorem sub_spec_point (self : edwards.EdwardsPoint.«x86_64-tables»)
    (other : AffineNielsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    sub self other ⦃ (r : CompletedPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (sub_spec self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«x86_64-tables».onCurve_iff,
      CompletedPoint.«x86_64-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«x86_64-tables».toPoint_def,
      AffineNielsPoint.«x86_64-tables».toPoint_def]
    exact ⟨Extended.subAffineNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_subAffineNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithSubSharedAAffineNielsPointx86_64-tablesCompletedPointx86_64-tables»
end «Shared0EdwardsPointx86_64-tables».Insts

namespace «Shared0EdwardsPointi686-tables».Insts

namespace «CoreOpsArithSubSharedAAffineNielsPointi686-tablesCompletedPointi686-tables»

theorem sub_eq (self : edwards.EdwardsPoint.«i686-tables»)
    (other : AffineNielsPoint.«i686-tables») :
    sub self other = Backend.subAffineNiels Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«i686-tables»))
      self.X self.Y self.Z self.T other.y_plus_x other.y_minus_x other.xy2d := rfl

/-- `Sub<&AffineNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.subAffineNiels`; limbs `< 2^26` and `< 2^27` in, `< 3 · 2^26` out. -/
@[step]
theorem sub_spec (self : edwards.EdwardsPoint.«i686-tables»)
    (other : AffineNielsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) :
    sub self other ⦃ (r : CompletedPoint.«i686-tables») =>
      r.toCompleted = self.toExtended.subAffineNiels other.toAffineNiels ∧
        r.MulBounded ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  obtain ⟨h5, h6, h7⟩ := hother
  rw [sub_eq]
  apply spec_mono (Backend.subAffineNiels_spec Backend.U32
    Backend.U32.add_spec Backend.U32.add_sum2_spec Backend.U32.sub_spec Backend.U32.mul_spec _ _ _ _
    _ _ _ _ h1 h2 h3 h4 h5 h6 h7)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«i686-tables».toCompleted_def,
    edwards.EdwardsPoint.«i686-tables».toExtended_def,
    AffineNielsPoint.«i686-tables».toAffineNiels_def]; exact h, ha, hb, hc, hd⟩

/-- `Sub<&AffineNielsPoint> for &EdwardsPoint` subtracts the represented points. -/
theorem sub_spec_point (self : edwards.EdwardsPoint.«i686-tables»)
    (other : AffineNielsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    sub self other ⦃ (r : CompletedPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.MulBounded ⦄ :=
  spec_mono (sub_spec self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«i686-tables».onCurve_iff,
      CompletedPoint.«i686-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«i686-tables».toPoint_def,
      AffineNielsPoint.«i686-tables».toPoint_def]
    exact ⟨Extended.subAffineNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_subAffineNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithSubSharedAAffineNielsPointi686-tablesCompletedPointi686-tables»
end «Shared0EdwardsPointi686-tables».Insts

namespace «Shared0EdwardsPointx86_64-no-tables».Insts

namespace «CoreOpsArithSubSharedAAffineNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»

theorem sub_eq (self : edwards.EdwardsPoint.«x86_64-no-tables»)
    (other : AffineNielsPoint.«x86_64-no-tables») :
    sub self other = Backend.subAffineNiels Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«x86_64-no-tables»))
      self.X self.Y self.Z self.T other.y_plus_x other.y_minus_x other.xy2d := rfl

/-- `Sub<&AffineNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.subAffineNiels`; limbs `< 2^52` and `< 2^54` in, `< 2^54` out. -/
@[step]
theorem sub_spec (self : edwards.EdwardsPoint.«x86_64-no-tables»)
    (other : AffineNielsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) :
    sub self other ⦃ (r : CompletedPoint.«x86_64-no-tables») =>
      r.toCompleted = self.toExtended.subAffineNiels other.toAffineNiels ∧
        r.LimbsLt 54 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  obtain ⟨h5, h6, h7⟩ := hother
  rw [sub_eq]
  apply spec_mono (Backend.subAffineNiels_spec Backend.U64
    Backend.U64.add_spec Backend.U64.add_sum2_spec Backend.U64.sub_spec Backend.U64.mul_spec _ _ _ _
    _ _ _ _ h1 h2 h3 h4 h5 h6 h7)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«x86_64-no-tables».toCompleted_def,
    edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def,
    AffineNielsPoint.«x86_64-no-tables».toAffineNiels_def]; exact h, ha, hb, hc, hd⟩

/-- `Sub<&AffineNielsPoint> for &EdwardsPoint` subtracts the represented points. -/
theorem sub_spec_point (self : edwards.EdwardsPoint.«x86_64-no-tables»)
    (other : AffineNielsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    sub self other ⦃ (r : CompletedPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (sub_spec self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«x86_64-no-tables».onCurve_iff,
      CompletedPoint.«x86_64-no-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def,
      AffineNielsPoint.«x86_64-no-tables».toPoint_def]
    exact ⟨Extended.subAffineNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_subAffineNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithSubSharedAAffineNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
end «Shared0EdwardsPointx86_64-no-tables».Insts

namespace «Shared0EdwardsPointi686-no-tables».Insts

namespace «CoreOpsArithSubSharedAAffineNielsPointi686-no-tablesCompletedPointi686-no-tables»

theorem sub_eq (self : edwards.EdwardsPoint.«i686-no-tables»)
    (other : AffineNielsPoint.«i686-no-tables») :
    sub self other = Backend.subAffineNiels Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«i686-no-tables»))
      self.X self.Y self.Z self.T other.y_plus_x other.y_minus_x other.xy2d := rfl

/-- `Sub<&AffineNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.subAffineNiels`; limbs `< 2^26` and `< 2^27` in, `< 3 · 2^26` out. -/
@[step]
theorem sub_spec (self : edwards.EdwardsPoint.«i686-no-tables»)
    (other : AffineNielsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) :
    sub self other ⦃ (r : CompletedPoint.«i686-no-tables») =>
      r.toCompleted = self.toExtended.subAffineNiels other.toAffineNiels ∧
        r.MulBounded ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  obtain ⟨h5, h6, h7⟩ := hother
  rw [sub_eq]
  apply spec_mono (Backend.subAffineNiels_spec Backend.U32
    Backend.U32.add_spec Backend.U32.add_sum2_spec Backend.U32.sub_spec Backend.U32.mul_spec _ _ _ _
    _ _ _ _ h1 h2 h3 h4 h5 h6 h7)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«i686-no-tables».toCompleted_def,
    edwards.EdwardsPoint.«i686-no-tables».toExtended_def,
    AffineNielsPoint.«i686-no-tables».toAffineNiels_def]; exact h, ha, hb, hc, hd⟩

/-- `Sub<&AffineNielsPoint> for &EdwardsPoint` subtracts the represented points. -/
theorem sub_spec_point (self : edwards.EdwardsPoint.«i686-no-tables»)
    (other : AffineNielsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    sub self other ⦃ (r : CompletedPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.MulBounded ⦄ :=
  spec_mono (sub_spec self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«i686-no-tables».onCurve_iff,
      CompletedPoint.«i686-no-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«i686-no-tables».toPoint_def,
      AffineNielsPoint.«i686-no-tables».toPoint_def]
    exact ⟨Extended.subAffineNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_subAffineNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithSubSharedAAffineNielsPointi686-no-tablesCompletedPointi686-no-tables»
end «Shared0EdwardsPointi686-no-tables».Insts

end Curve25519Dalek
