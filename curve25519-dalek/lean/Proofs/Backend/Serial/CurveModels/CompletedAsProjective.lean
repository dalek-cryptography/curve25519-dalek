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

/-- `CompletedPoint::as_projective` over a backend. -/
@[expose] def completedAsProjective {P : Type} (mk : B.F → B.F → B.F → P) (X Y Z T : B.F) :
    Result P := do
  let fe ← B.mul X T
  let fe1 ← B.mul Y Z
  let fe2 ← B.mul Z T
  ok (mk fe fe1 fe2)

/-- `completedAsProjective` computes `Completed.toProjective`. -/
theorem completedAsProjective_spec
    (hmul : B.MulSpec)
    {P : Type} (mk : B.F → B.F → B.F → P) (X Y Z T : B.F)
    (hX : B.MulIn X) (hY : B.MulIn Y) (hZ : B.MulIn Z) (hT : B.MulIn T) :
    B.completedAsProjective mk X Y Z T ⦃ r => ∃ a b c, r = mk a b c ∧
      (⟨B.toField a, B.toField b, B.toField c⟩ : edwards.Projective) =
        (⟨B.toField X, B.toField Y, B.toField Z, B.toField T⟩ : edwards.Completed).toProjective ∧
      B.Red a ∧ B.Red b ∧ B.Red c ⦄ := by
  unfold completedAsProjective
  step with hmul X T hX hT as ⟨a, ha, ha'⟩
  step with hmul Y Z hY hZ as ⟨b, hb, hb'⟩
  step with hmul Z T hZ hT as ⟨c, hc, hc'⟩
  exact ⟨a, b, c, rfl, by rw [ha, hb, hc]; rfl, ha', hb', hc'⟩

end Curve25519Dalek.Backend

namespace Curve25519Dalek.backend.serial.curve_models

namespace «CompletedPointx86_64-tables»

theorem as_projective_eq (self : CompletedPoint.«x86_64-tables») :
    as_projective self = Backend.completedAsProjective Backend.U64
      (fun X Y Z => (⟨X, Y, Z⟩ : ProjectivePoint.«x86_64-tables»))
      self.X self.Y self.Z self.T := rfl

/-- `CompletedPoint::as_projective`: `(X T : Y Z : Z T)`, limbs `< 2^52`. -/
@[step]
theorem as_projective_spec (self : CompletedPoint.«x86_64-tables») (hself : self.LimbsLt 54) :
    as_projective self ⦃ (r : ProjectivePoint.«x86_64-tables») =>
      r.toProjective = self.toCompleted.toProjective ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  rw [as_projective_eq]
  apply spec_mono (Backend.completedAsProjective_spec Backend.U64
    Backend.U64.mul_spec _ _ _ _ _ h1 h2 h3 h4)
  rintro _ ⟨a, b, c, rfl, h, ha, hb, hc⟩
  exact ⟨by rw [ProjectivePoint.«x86_64-tables».toProjective_def,
    CompletedPoint.«x86_64-tables».toCompleted_def]; exact h, ha, hb, hc⟩

/-- `CompletedPoint::as_projective` represents the same point. -/
theorem as_projective_spec_point (self : CompletedPoint.«x86_64-tables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_projective_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«x86_64-tables».onCurve_iff,
      ProjectivePoint.«x86_64-tables».toPoint_def, hr,
      CompletedPoint.«x86_64-tables».toPoint_def]
    exact ⟨Completed.onCurve_toProjective hon, Completed.toPoint_toProjective hon, hb⟩

end «CompletedPointx86_64-tables»

namespace «CompletedPointi686-tables»

theorem as_projective_eq (self : CompletedPoint.«i686-tables») :
    as_projective self = Backend.completedAsProjective Backend.U32
      (fun X Y Z => (⟨X, Y, Z⟩ : ProjectivePoint.«i686-tables»))
      self.X self.Y self.Z self.T := rfl

/-- `CompletedPoint::as_projective`: `(X T : Y Z : Z T)`, limbs `< 2^26`. -/
@[step]
theorem as_projective_spec (self : CompletedPoint.«i686-tables») (hself : self.MulBounded) :
    as_projective self ⦃ (r : ProjectivePoint.«i686-tables») =>
      r.toProjective = self.toCompleted.toProjective ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  rw [as_projective_eq]
  apply spec_mono (Backend.completedAsProjective_spec Backend.U32
    Backend.U32.mul_spec _ _ _ _ _ h1 h2 h3 h4)
  rintro _ ⟨a, b, c, rfl, h, ha, hb, hc⟩
  exact ⟨by rw [ProjectivePoint.«i686-tables».toProjective_def,
    CompletedPoint.«i686-tables».toCompleted_def]; exact h, ha, hb, hc⟩

/-- `CompletedPoint::as_projective` represents the same point. -/
theorem as_projective_spec_point (self : CompletedPoint.«i686-tables») (hself : self.MulBounded)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_projective_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«i686-tables».onCurve_iff,
      ProjectivePoint.«i686-tables».toPoint_def, hr,
      CompletedPoint.«i686-tables».toPoint_def]
    exact ⟨Completed.onCurve_toProjective hon, Completed.toPoint_toProjective hon, hb⟩

end «CompletedPointi686-tables»

namespace «CompletedPointx86_64-no-tables»

theorem as_projective_eq (self : CompletedPoint.«x86_64-no-tables») :
    as_projective self = Backend.completedAsProjective Backend.U64
      (fun X Y Z => (⟨X, Y, Z⟩ : ProjectivePoint.«x86_64-no-tables»))
      self.X self.Y self.Z self.T := rfl

/-- `CompletedPoint::as_projective`: `(X T : Y Z : Z T)`, limbs `< 2^52`. -/
@[step]
theorem as_projective_spec (self : CompletedPoint.«x86_64-no-tables») (hself : self.LimbsLt 54) :
    as_projective self ⦃ (r : ProjectivePoint.«x86_64-no-tables») =>
      r.toProjective = self.toCompleted.toProjective ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  rw [as_projective_eq]
  apply spec_mono (Backend.completedAsProjective_spec Backend.U64
    Backend.U64.mul_spec _ _ _ _ _ h1 h2 h3 h4)
  rintro _ ⟨a, b, c, rfl, h, ha, hb, hc⟩
  exact ⟨by rw [ProjectivePoint.«x86_64-no-tables».toProjective_def,
    CompletedPoint.«x86_64-no-tables».toCompleted_def]; exact h, ha, hb, hc⟩

/-- `CompletedPoint::as_projective` represents the same point. -/
theorem as_projective_spec_point (self : CompletedPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_projective_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«x86_64-no-tables».onCurve_iff,
      ProjectivePoint.«x86_64-no-tables».toPoint_def, hr,
      CompletedPoint.«x86_64-no-tables».toPoint_def]
    exact ⟨Completed.onCurve_toProjective hon, Completed.toPoint_toProjective hon, hb⟩

end «CompletedPointx86_64-no-tables»

namespace «CompletedPointi686-no-tables»

theorem as_projective_eq (self : CompletedPoint.«i686-no-tables») :
    as_projective self = Backend.completedAsProjective Backend.U32
      (fun X Y Z => (⟨X, Y, Z⟩ : ProjectivePoint.«i686-no-tables»))
      self.X self.Y self.Z self.T := rfl

/-- `CompletedPoint::as_projective`: `(X T : Y Z : Z T)`, limbs `< 2^26`. -/
@[step]
theorem as_projective_spec (self : CompletedPoint.«i686-no-tables») (hself : self.MulBounded) :
    as_projective self ⦃ (r : ProjectivePoint.«i686-no-tables») =>
      r.toProjective = self.toCompleted.toProjective ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  rw [as_projective_eq]
  apply spec_mono (Backend.completedAsProjective_spec Backend.U32
    Backend.U32.mul_spec _ _ _ _ _ h1 h2 h3 h4)
  rintro _ ⟨a, b, c, rfl, h, ha, hb, hc⟩
  exact ⟨by rw [ProjectivePoint.«i686-no-tables».toProjective_def,
    CompletedPoint.«i686-no-tables».toCompleted_def]; exact h, ha, hb, hc⟩

/-- `CompletedPoint::as_projective` represents the same point. -/
theorem as_projective_spec_point (self : CompletedPoint.«i686-no-tables»)
    (hself : self.MulBounded)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_projective_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«i686-no-tables».onCurve_iff,
      ProjectivePoint.«i686-no-tables».toPoint_def, hr,
      CompletedPoint.«i686-no-tables».toPoint_def]
    exact ⟨Completed.onCurve_toProjective hon, Completed.toPoint_toProjective hon, hb⟩

end «CompletedPointi686-no-tables»

end Curve25519Dalek.backend.serial.curve_models
