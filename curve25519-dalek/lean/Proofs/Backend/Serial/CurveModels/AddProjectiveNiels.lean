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

/-- `&EdwardsPoint + &ProjectiveNielsPoint` over a backend. -/
@[expose] def addProjectiveNiels {P : Type} (mk : B.F → B.F → B.F → B.F → P)
    (X Y Z T YpX YmX Z' T2d : B.F) : Result P := do
  let Y_plus_X ← B.add Y X
  let Y_minus_X ← B.sub Y X
  let PP ← B.mul Y_plus_X YpX
  let MM ← B.mul Y_minus_X YmX
  let TT2d ← B.mul T T2d
  let ZZ ← B.mul Z Z'
  let ZZ2 ← B.add ZZ ZZ
  let fe ← B.sub PP MM
  let fe1 ← B.add PP MM
  let fe2 ← B.add ZZ2 TT2d
  let fe3 ← B.sub ZZ2 TT2d
  ok (mk fe fe1 fe2 fe3)

/-- `addProjectiveNiels` computes `Extended.addProjectiveNiels`. -/
theorem addProjectiveNiels_spec
    (hadd : B.AddSpec) (hadd2 : B.AddSum2Spec) (hsub : B.SubSpec) (hmul : B.MulSpec)
    {P : Type} (mk : B.F → B.F → B.F → B.F → P)
    (X Y Z T YpX YmX Z' T2d : B.F) (hX : B.Red X) (hY : B.Red Y) (hZ : B.Red Z) (hT : B.Red T)
    (hYpX : B.Niels YpX) (hYmX : B.Niels YmX) (hZ' : B.Niels Z') (hT2d : B.Niels T2d) :
    B.addProjectiveNiels mk X Y Z T YpX YmX Z' T2d ⦃ r => ∃ a b c d, r = mk a b c d ∧
      (⟨B.toField a, B.toField b, B.toField c, B.toField d⟩ : edwards.Completed) =
        (⟨B.toField X, B.toField Y, B.toField Z, B.toField T⟩ :
          edwards.Extended).addProjectiveNiels
          ⟨B.toField YpX, B.toField YmX, B.toField Z', B.toField T2d⟩ ∧
      B.MulIn a ∧ B.MulIn b ∧ B.MulIn c ∧ B.MulIn d ⦄ := by
  unfold addProjectiveNiels
  step with hadd Y X hY hX as ⟨ypx, hypx, hypx'⟩
  step with hsub Y X (B.red_mulIn hY) (B.red_mulIn hX) as ⟨ymx, hymx, hymx'⟩
  step with hmul ypx YpX (B.sum2_mulIn hypx') (B.niels_mulIn hYpX) as ⟨pp, hpp, hpp'⟩
  step with hmul ymx YmX (B.red_mulIn hymx') (B.niels_mulIn hYmX) as ⟨mm, hmm, hmm'⟩
  step with hmul T T2d (B.red_mulIn hT) (B.niels_mulIn hT2d) as ⟨tt, htt, htt'⟩
  step with hmul Z Z' (B.red_mulIn hZ) (B.niels_mulIn hZ') as ⟨zz, hzz, hzz'⟩
  step with hadd zz zz hzz' hzz' as ⟨zz2, hzz2, hzz2'⟩
  step with hsub pp mm (B.red_mulIn hpp') (B.red_mulIn hmm') as ⟨a, ha, ha'⟩
  step with hadd pp mm hpp' hmm' as ⟨b, hb, hb'⟩
  step with hadd2 zz2 tt hzz2' htt' as ⟨c, hc, hc'⟩
  step with hsub zz2 tt (B.sum2_mulIn hzz2') (B.red_mulIn htt') as ⟨d, hd, hd'⟩
  refine ⟨a, b, c, d, rfl, ?_, B.red_mulIn ha', B.sum2_mulIn hb', hc', B.red_mulIn hd'⟩
  rw [ha, hb, hc, hd, hpp, hmm, hzz2, htt, hzz, hypx, hymx]
  rfl

end Curve25519Dalek.Backend

namespace Curve25519Dalek

namespace «Shared0EdwardsPointx86_64-tables».Insts

namespace «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»

theorem add_eq (self : edwards.EdwardsPoint.«x86_64-tables»)
    (other : ProjectiveNielsPoint.«x86_64-tables») :
    add self other = Backend.addProjectiveNiels Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«x86_64-tables»))
      self.X self.Y self.Z self.T other.Y_plus_X other.Y_minus_X other.Z other.T2d := rfl

/-- `Add<&ProjectiveNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.addProjectiveNiels`; limbs `< 2^52` and `< 2^54` in, `< 2^54` out. -/
@[step]
theorem add_spec (self : edwards.EdwardsPoint.«x86_64-tables»)
    (other : ProjectiveNielsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) :
    add self other ⦃ (r : CompletedPoint.«x86_64-tables») =>
      r.toCompleted = self.toExtended.addProjectiveNiels other.toProjectiveNiels ∧
        r.LimbsLt 54 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  obtain ⟨h5, h6, h7, h8⟩ := hother
  rw [add_eq]
  apply spec_mono (Backend.addProjectiveNiels_spec Backend.U64
    Backend.U64.add_spec Backend.U64.add_sum2_spec Backend.U64.sub_spec Backend.U64.mul_spec _ _ _ _
    _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«x86_64-tables».toCompleted_def,
    edwards.EdwardsPoint.«x86_64-tables».toExtended_def,
    ProjectiveNielsPoint.«x86_64-tables».toProjectiveNiels_def]; exact h, ha, hb, hc, hd⟩

/-- `Add<&ProjectiveNielsPoint> for &EdwardsPoint` adds the represented points. -/
theorem add_spec_point (self : edwards.EdwardsPoint.«x86_64-tables»)
    (other : ProjectiveNielsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    add self other ⦃ (r : CompletedPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (add_spec self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«x86_64-tables».onCurve_iff,
      CompletedPoint.«x86_64-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«x86_64-tables».toPoint_def,
      ProjectiveNielsPoint.«x86_64-tables».toPoint_def]
    exact ⟨Extended.addProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_addProjectiveNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
end «Shared0EdwardsPointx86_64-tables».Insts

namespace «Shared0EdwardsPointi686-tables».Insts

namespace «CoreOpsArithAddSharedAProjectiveNielsPointi686-tablesCompletedPointi686-tables»

theorem add_eq (self : edwards.EdwardsPoint.«i686-tables»)
    (other : ProjectiveNielsPoint.«i686-tables») :
    add self other = Backend.addProjectiveNiels Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«i686-tables»))
      self.X self.Y self.Z self.T other.Y_plus_X other.Y_minus_X other.Z other.T2d := rfl

/-- `Add<&ProjectiveNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.addProjectiveNiels`; limbs `< 2^26` and `< 2^27` in, `< 3 · 2^26` out. -/
@[step]
theorem add_spec (self : edwards.EdwardsPoint.«i686-tables»)
    (other : ProjectiveNielsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) :
    add self other ⦃ (r : CompletedPoint.«i686-tables») =>
      r.toCompleted = self.toExtended.addProjectiveNiels other.toProjectiveNiels ∧
        r.MulBounded ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  obtain ⟨h5, h6, h7, h8⟩ := hother
  rw [add_eq]
  apply spec_mono (Backend.addProjectiveNiels_spec Backend.U32
    Backend.U32.add_spec Backend.U32.add_sum2_spec Backend.U32.sub_spec Backend.U32.mul_spec _ _ _ _
    _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«i686-tables».toCompleted_def,
    edwards.EdwardsPoint.«i686-tables».toExtended_def,
    ProjectiveNielsPoint.«i686-tables».toProjectiveNiels_def]; exact h, ha, hb, hc, hd⟩

/-- `Add<&ProjectiveNielsPoint> for &EdwardsPoint` adds the represented points. -/
theorem add_spec_point (self : edwards.EdwardsPoint.«i686-tables»)
    (other : ProjectiveNielsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    add self other ⦃ (r : CompletedPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.MulBounded ⦄ :=
  spec_mono (add_spec self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«i686-tables».onCurve_iff,
      CompletedPoint.«i686-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«i686-tables».toPoint_def,
      ProjectiveNielsPoint.«i686-tables».toPoint_def]
    exact ⟨Extended.addProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_addProjectiveNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithAddSharedAProjectiveNielsPointi686-tablesCompletedPointi686-tables»
end «Shared0EdwardsPointi686-tables».Insts

namespace «Shared0EdwardsPointx86_64-no-tables».Insts

namespace «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»

theorem add_eq (self : edwards.EdwardsPoint.«x86_64-no-tables»)
    (other : ProjectiveNielsPoint.«x86_64-no-tables») :
    add self other = Backend.addProjectiveNiels Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«x86_64-no-tables»))
      self.X self.Y self.Z self.T other.Y_plus_X other.Y_minus_X other.Z other.T2d := rfl

/-- `Add<&ProjectiveNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.addProjectiveNiels`; limbs `< 2^52` and `< 2^54` in, `< 2^54` out. -/
@[step]
theorem add_spec (self : edwards.EdwardsPoint.«x86_64-no-tables»)
    (other : ProjectiveNielsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) :
    add self other ⦃ (r : CompletedPoint.«x86_64-no-tables») =>
      r.toCompleted = self.toExtended.addProjectiveNiels other.toProjectiveNiels ∧
        r.LimbsLt 54 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  obtain ⟨h5, h6, h7, h8⟩ := hother
  rw [add_eq]
  apply spec_mono (Backend.addProjectiveNiels_spec Backend.U64
    Backend.U64.add_spec Backend.U64.add_sum2_spec Backend.U64.sub_spec Backend.U64.mul_spec _ _ _ _
    _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«x86_64-no-tables».toCompleted_def,
    edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def,
    ProjectiveNielsPoint.«x86_64-no-tables».toProjectiveNiels_def]; exact h, ha, hb, hc, hd⟩

/-- `Add<&ProjectiveNielsPoint> for &EdwardsPoint` adds the represented points. -/
theorem add_spec_point (self : edwards.EdwardsPoint.«x86_64-no-tables»)
    (other : ProjectiveNielsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 54) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    add self other ⦃ (r : CompletedPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (add_spec self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«x86_64-no-tables».onCurve_iff,
      CompletedPoint.«x86_64-no-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def,
      ProjectiveNielsPoint.«x86_64-no-tables».toPoint_def]
    exact ⟨Extended.addProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_addProjectiveNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
end «Shared0EdwardsPointx86_64-no-tables».Insts

namespace «Shared0EdwardsPointi686-no-tables».Insts

namespace «CoreOpsArithAddSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»

theorem add_eq (self : edwards.EdwardsPoint.«i686-no-tables»)
    (other : ProjectiveNielsPoint.«i686-no-tables») :
    add self other = Backend.addProjectiveNiels Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«i686-no-tables»))
      self.X self.Y self.Z self.T other.Y_plus_X other.Y_minus_X other.Z other.T2d := rfl

/-- `Add<&ProjectiveNielsPoint> for &EdwardsPoint`: the mixed formula
`Extended.addProjectiveNiels`; limbs `< 2^26` and `< 2^27` in, `< 3 · 2^26` out. -/
@[step]
theorem add_spec (self : edwards.EdwardsPoint.«i686-no-tables»)
    (other : ProjectiveNielsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) :
    add self other ⦃ (r : CompletedPoint.«i686-no-tables») =>
      r.toCompleted = self.toExtended.addProjectiveNiels other.toProjectiveNiels ∧
        r.MulBounded ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  obtain ⟨h5, h6, h7, h8⟩ := hother
  rw [add_eq]
  apply spec_mono (Backend.addProjectiveNiels_spec Backend.U32
    Backend.U32.add_spec Backend.U32.add_sum2_spec Backend.U32.sub_spec Backend.U32.mul_spec _ _ _ _
    _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«i686-no-tables».toCompleted_def,
    edwards.EdwardsPoint.«i686-no-tables».toExtended_def,
    ProjectiveNielsPoint.«i686-no-tables».toProjectiveNiels_def]; exact h, ha, hb, hc, hd⟩

/-- `Add<&ProjectiveNielsPoint> for &EdwardsPoint` adds the represented points. -/
theorem add_spec_point (self : edwards.EdwardsPoint.«i686-no-tables»)
    (other : ProjectiveNielsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 27) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    add self other ⦃ (r : CompletedPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.MulBounded ⦄ :=
  spec_mono (add_spec self other hself hother) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«i686-no-tables».onCurve_iff,
      CompletedPoint.«i686-no-tables».toPoint_def, hr,
      edwards.EdwardsPoint.«i686-no-tables».toPoint_def,
      ProjectiveNielsPoint.«i686-no-tables».toPoint_def]
    exact ⟨Extended.addProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on hother_on,
      Extended.toPoint_addProjectiveNiels edwards_a_eq_neg_one hself_on hother_on, hb⟩

end «CoreOpsArithAddSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»
end «Shared0EdwardsPointi686-no-tables».Insts

end Curve25519Dalek
