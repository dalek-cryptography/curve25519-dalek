/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.CurveModels
public import Proofs.Helpers.Coords
public import Proofs.Helpers.Backend.U32
public import Proofs.Helpers.Backend.U64
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel

namespace Curve25519Dalek.Backend

variable (B : Backend)

/-- `ProjectivePoint::double` over a backend. -/
@[expose] def projectiveDouble {P : Type} (mk : B.F → B.F → B.F → B.F → P) (X Y Z : B.F) :
    Result P := do
  let XX ← B.square X
  let YY ← B.square Y
  let ZZ2 ← B.square2 Z
  let X_plus_Y ← B.add X Y
  let X_plus_Y_sq ← B.square X_plus_Y
  let YY_plus_XX ← B.add YY XX
  let YY_minus_XX ← B.sub YY XX
  let fe ← B.sub X_plus_Y_sq YY_plus_XX
  let fe1 ← B.sub ZZ2 YY_minus_XX
  ok (mk fe YY_plus_XX YY_minus_XX fe1)

/-- `projectiveDouble` computes `Projective.double` (the `a = -1` form of the formula). -/
theorem projectiveDouble_spec
    (hadd : B.AddSpec) (hsub : B.SubSpec) (hsq : B.SquareSpec) (hsq2 : B.Square2Spec)
    {P : Type} (mk : B.F → B.F → B.F → B.F → P) (X Y Z : B.F)
    (hX : B.Red X) (hY : B.Red Y) (hZ : B.Red Z) :
    B.projectiveDouble mk X Y Z ⦃ r => ∃ a b c d, r = mk a b c d ∧
      (⟨B.toField a, B.toField b, B.toField c, B.toField d⟩ : edwards.Completed) =
        (⟨B.toField X, B.toField Y, B.toField Z⟩ : edwards.Projective).double ∧
      B.MulIn a ∧ B.MulIn b ∧ B.MulIn c ∧ B.MulIn d ⦄ := by
  unfold projectiveDouble
  step with hsq X (B.red_sqIn hX) as ⟨xx, hxx, hxx'⟩
  step with hsq Y (B.red_sqIn hY) as ⟨yy, hyy, hyy'⟩
  step with hsq2 Z (B.red_sqIn hZ) as ⟨zz2, hzz2, hzz2'⟩
  step with hadd X Y hX hY as ⟨xy, hxy, hxy'⟩
  step with hsq xy (B.sum2_sqIn hxy') as ⟨xysq, hxysq, hxysq'⟩
  step with hadd yy xx hyy' hxx' as ⟨b, hb, hb'⟩
  step with hsub yy xx (B.red_mulIn hyy') (B.red_mulIn hxx') as ⟨c, hc, hc'⟩
  step with hsub xysq b (B.red_mulIn hxysq') (B.sum2_mulIn hb') as ⟨a, ha, ha'⟩
  step with hsub zz2 c (B.sum2_mulIn hzz2') (B.red_mulIn hc') as ⟨d, hd, hd'⟩
  refine ⟨a, b, c, d, rfl, ?_, B.red_mulIn ha', B.sum2_mulIn hb', B.red_mulIn hc',
    B.red_mulIn hd'⟩
  rw [ha, hd, hb, hc, hxysq, hzz2, hxy, hxx, hyy]
  ext <;> simp only [Projective.double, edwards_a_eq_neg_one] <;> ring

end Curve25519Dalek.Backend

namespace Curve25519Dalek.backend.serial.curve_models

namespace «ProjectivePointx86_64-tables»

theorem double_eq (self : ProjectivePoint.«x86_64-tables») :
    double self = Backend.projectiveDouble Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«x86_64-tables»))
      self.X self.Y self.Z := rfl

/-- `ProjectivePoint::double`: the "dbl-2008-bbjlp" formula `Projective.double`; limbs `< 2^52`
in, `< 2^54` out. -/
@[step]
theorem double_spec (self : ProjectivePoint.«x86_64-tables») (hself : self.LimbsLt 52) :
    double self ⦃ (r : CompletedPoint.«x86_64-tables») =>
      r.toCompleted = self.toProjective.double ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hself
  rw [double_eq]
  apply spec_mono (Backend.projectiveDouble_spec Backend.U64
    Backend.U64.add_spec Backend.U64.sub_spec Backend.U64.square_spec Backend.U64.square2_spec _ _ _
    _ h1 h2 h3)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«x86_64-tables».toCompleted_def,
    ProjectivePoint.«x86_64-tables».toProjective_def]; exact h, ha, hb, hc, hd⟩

/-- `ProjectivePoint::double` doubles the represented point. -/
theorem double_spec_point (self : ProjectivePoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    double self ⦃ (r : CompletedPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 2 • self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (double_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«x86_64-tables».onCurve_iff,
      CompletedPoint.«x86_64-tables».toPoint_def, hr,
      ProjectivePoint.«x86_64-tables».toPoint_def]
    exact ⟨Projective.double_onCurve hon,
      Projective.toPoint_double hon, hb⟩

end «ProjectivePointx86_64-tables»

namespace «ProjectivePointi686-tables»

theorem double_eq (self : ProjectivePoint.«i686-tables») :
    double self = Backend.projectiveDouble Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«i686-tables»))
      self.X self.Y self.Z := rfl

/-- `ProjectivePoint::double`: the "dbl-2008-bbjlp" formula `Projective.double`; limbs `< 2^26`
in, `< 3 · 2^26` out. -/
@[step]
theorem double_spec (self : ProjectivePoint.«i686-tables») (hself : self.LimbsLt 26) :
    double self ⦃ (r : CompletedPoint.«i686-tables») =>
      r.toCompleted = self.toProjective.double ∧ r.MulBounded ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hself
  rw [double_eq]
  apply spec_mono (Backend.projectiveDouble_spec Backend.U32
    Backend.U32.add_spec Backend.U32.sub_spec Backend.U32.square_spec Backend.U32.square2_spec _ _ _
    _ h1 h2 h3)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«i686-tables».toCompleted_def,
    ProjectivePoint.«i686-tables».toProjective_def]; exact h, ha, hb, hc, hd⟩

/-- `ProjectivePoint::double` doubles the represented point. -/
theorem double_spec_point (self : ProjectivePoint.«i686-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    double self ⦃ (r : CompletedPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = 2 • self.toPoint ∧ r.MulBounded ⦄ :=
  spec_mono (double_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«i686-tables».onCurve_iff,
      CompletedPoint.«i686-tables».toPoint_def, hr,
      ProjectivePoint.«i686-tables».toPoint_def]
    exact ⟨Projective.double_onCurve hon,
      Projective.toPoint_double hon, hb⟩

end «ProjectivePointi686-tables»

namespace «ProjectivePointx86_64-no-tables»

theorem double_eq (self : ProjectivePoint.«x86_64-no-tables») :
    double self = Backend.projectiveDouble Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«x86_64-no-tables»))
      self.X self.Y self.Z := rfl

/-- `ProjectivePoint::double`: the "dbl-2008-bbjlp" formula `Projective.double`; limbs `< 2^52`
in, `< 2^54` out. -/
@[step]
theorem double_spec (self : ProjectivePoint.«x86_64-no-tables») (hself : self.LimbsLt 52) :
    double self ⦃ (r : CompletedPoint.«x86_64-no-tables») =>
      r.toCompleted = self.toProjective.double ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hself
  rw [double_eq]
  apply spec_mono (Backend.projectiveDouble_spec Backend.U64
    Backend.U64.add_spec Backend.U64.sub_spec Backend.U64.square_spec Backend.U64.square2_spec _ _ _
    _ h1 h2 h3)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«x86_64-no-tables».toCompleted_def,
    ProjectivePoint.«x86_64-no-tables».toProjective_def]; exact h, ha, hb, hc, hd⟩

/-- `ProjectivePoint::double` doubles the represented point. -/
theorem double_spec_point (self : ProjectivePoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    double self ⦃ (r : CompletedPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 2 • self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (double_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«x86_64-no-tables».onCurve_iff,
      CompletedPoint.«x86_64-no-tables».toPoint_def, hr,
      ProjectivePoint.«x86_64-no-tables».toPoint_def]
    exact ⟨Projective.double_onCurve hon,
      Projective.toPoint_double hon, hb⟩

end «ProjectivePointx86_64-no-tables»

namespace «ProjectivePointi686-no-tables»

theorem double_eq (self : ProjectivePoint.«i686-no-tables») :
    double self = Backend.projectiveDouble Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : CompletedPoint.«i686-no-tables»))
      self.X self.Y self.Z := rfl

/-- `ProjectivePoint::double`: the "dbl-2008-bbjlp" formula `Projective.double`; limbs `< 2^26`
in, `< 3 · 2^26` out. -/
@[step]
theorem double_spec (self : ProjectivePoint.«i686-no-tables») (hself : self.LimbsLt 26) :
    double self ⦃ (r : CompletedPoint.«i686-no-tables») =>
      r.toCompleted = self.toProjective.double ∧ r.MulBounded ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hself
  rw [double_eq]
  apply spec_mono (Backend.projectiveDouble_spec Backend.U32
    Backend.U32.add_spec Backend.U32.sub_spec Backend.U32.square_spec Backend.U32.square2_spec _ _ _
    _ h1 h2 h3)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [CompletedPoint.«i686-no-tables».toCompleted_def,
    ProjectivePoint.«i686-no-tables».toProjective_def]; exact h, ha, hb, hc, hd⟩

/-- `ProjectivePoint::double` doubles the represented point. -/
theorem double_spec_point (self : ProjectivePoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    double self ⦃ (r : CompletedPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = 2 • self.toPoint ∧ r.MulBounded ⦄ :=
  spec_mono (double_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [CompletedPoint.«i686-no-tables».onCurve_iff,
      CompletedPoint.«i686-no-tables».toPoint_def, hr,
      ProjectivePoint.«i686-no-tables».toPoint_def]
    exact ⟨Projective.double_onCurve hon,
      Projective.toPoint_double hon, hb⟩

end «ProjectivePointi686-no-tables»

end Curve25519Dalek.backend.serial.curve_models
