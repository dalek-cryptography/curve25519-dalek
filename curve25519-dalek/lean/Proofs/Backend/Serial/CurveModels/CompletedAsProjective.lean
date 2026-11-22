/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.CurveModels
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

namespace «CompletedPoint64bit-tables»

theorem as_projective_eq (self : CompletedPoint.«64bit-tables») :
    as_projective self = Backend.completedAsProjective Backend.U64
      (fun X Y Z => (⟨X, Y, Z⟩ : ProjectivePoint.«64bit-tables»))
      self.X self.Y self.Z self.T := rfl

/-- `CompletedPoint::as_projective`: `(X T : Y Z : Z T)`, limbs `< 2^52`. -/
@[step]
theorem as_projective_toProjective (self : CompletedPoint.«64bit-tables») (hself : self.LimbsLt
    54) :
    as_projective self ⦃ (r : ProjectivePoint.«64bit-tables») =>
      r.toProjective = self.toCompleted.toProjective ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  rw [as_projective_eq]
  apply spec_mono (Backend.completedAsProjective_spec Backend.U64
    Backend.U64.mul_spec _ _ _ _ _ h1 h2 h3 h4)
  rintro _ ⟨a, b, c, rfl, h, ha, hb, hc⟩
  exact ⟨by rw [ProjectivePoint.«64bit-tables».toProjective_def,
    CompletedPoint.«64bit-tables».toCompleted_def]; exact h, ha, hb, hc⟩

/-- `CompletedPoint::as_projective` represents the same point. -/
theorem as_projective_spec (self : CompletedPoint.«64bit-tables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_projective_toProjective self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«64bit-tables».onCurve_iff,
      ProjectivePoint.«64bit-tables».toPoint_def, hr,
      CompletedPoint.«64bit-tables».toPoint_def]
    exact ⟨Completed.onCurve_toProjective hon, Completed.toPoint_toProjective hon, hb⟩

end «CompletedPoint64bit-tables»

namespace «CompletedPoint32bit-tables»

theorem as_projective_eq (self : CompletedPoint.«32bit-tables») :
    as_projective self = Backend.completedAsProjective Backend.U32
      (fun X Y Z => (⟨X, Y, Z⟩ : ProjectivePoint.«32bit-tables»))
      self.X self.Y self.Z self.T := rfl

/-- `CompletedPoint::as_projective`: `(X T : Y Z : Z T)`, limbs `< 2^26`. -/
@[step]
theorem as_projective_toProjective (self : CompletedPoint.«32bit-tables») (hself : self.MulBounded)
    :
    as_projective self ⦃ (r : ProjectivePoint.«32bit-tables») =>
      r.toProjective = self.toCompleted.toProjective ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  rw [as_projective_eq]
  apply spec_mono (Backend.completedAsProjective_spec Backend.U32
    Backend.U32.mul_spec _ _ _ _ _ h1 h2 h3 h4)
  rintro _ ⟨a, b, c, rfl, h, ha, hb, hc⟩
  exact ⟨by rw [ProjectivePoint.«32bit-tables».toProjective_def,
    CompletedPoint.«32bit-tables».toCompleted_def]; exact h, ha, hb, hc⟩

/-- `CompletedPoint::as_projective` represents the same point. -/
theorem as_projective_spec (self : CompletedPoint.«32bit-tables») (hself : self.MulBounded)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_projective_toProjective self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«32bit-tables».onCurve_iff,
      ProjectivePoint.«32bit-tables».toPoint_def, hr,
      CompletedPoint.«32bit-tables».toPoint_def]
    exact ⟨Completed.onCurve_toProjective hon, Completed.toPoint_toProjective hon, hb⟩

end «CompletedPoint32bit-tables»

namespace «CompletedPoint64bit-notables»

theorem as_projective_eq (self : CompletedPoint.«64bit-notables») :
    as_projective self = Backend.completedAsProjective Backend.U64
      (fun X Y Z => (⟨X, Y, Z⟩ : ProjectivePoint.«64bit-notables»))
      self.X self.Y self.Z self.T := rfl

/-- `CompletedPoint::as_projective`: `(X T : Y Z : Z T)`, limbs `< 2^52`. -/
@[step]
theorem as_projective_toProjective (self : CompletedPoint.«64bit-notables») (hself : self.LimbsLt
    54) :
    as_projective self ⦃ (r : ProjectivePoint.«64bit-notables») =>
      r.toProjective = self.toCompleted.toProjective ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  rw [as_projective_eq]
  apply spec_mono (Backend.completedAsProjective_spec Backend.U64
    Backend.U64.mul_spec _ _ _ _ _ h1 h2 h3 h4)
  rintro _ ⟨a, b, c, rfl, h, ha, hb, hc⟩
  exact ⟨by rw [ProjectivePoint.«64bit-notables».toProjective_def,
    CompletedPoint.«64bit-notables».toCompleted_def]; exact h, ha, hb, hc⟩

/-- `CompletedPoint::as_projective` represents the same point. -/
theorem as_projective_spec (self : CompletedPoint.«64bit-notables»)
    (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_projective_toProjective self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«64bit-notables».onCurve_iff,
      ProjectivePoint.«64bit-notables».toPoint_def, hr,
      CompletedPoint.«64bit-notables».toPoint_def]
    exact ⟨Completed.onCurve_toProjective hon, Completed.toPoint_toProjective hon, hb⟩

end «CompletedPoint64bit-notables»

namespace «CompletedPoint32bit-notables»

theorem as_projective_eq (self : CompletedPoint.«32bit-notables») :
    as_projective self = Backend.completedAsProjective Backend.U32
      (fun X Y Z => (⟨X, Y, Z⟩ : ProjectivePoint.«32bit-notables»))
      self.X self.Y self.Z self.T := rfl

/-- `CompletedPoint::as_projective`: `(X T : Y Z : Z T)`, limbs `< 2^26`. -/
@[step]
theorem as_projective_toProjective (self : CompletedPoint.«32bit-notables») (hself :
    self.MulBounded) :
    as_projective self ⦃ (r : ProjectivePoint.«32bit-notables») =>
      r.toProjective = self.toCompleted.toProjective ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  rw [as_projective_eq]
  apply spec_mono (Backend.completedAsProjective_spec Backend.U32
    Backend.U32.mul_spec _ _ _ _ _ h1 h2 h3 h4)
  rintro _ ⟨a, b, c, rfl, h, ha, hb, hc⟩
  exact ⟨by rw [ProjectivePoint.«32bit-notables».toProjective_def,
    CompletedPoint.«32bit-notables».toCompleted_def]; exact h, ha, hb, hc⟩

/-- `CompletedPoint::as_projective` represents the same point. -/
theorem as_projective_spec (self : CompletedPoint.«32bit-notables»)
    (hself : self.MulBounded)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_projective_toProjective self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«32bit-notables».onCurve_iff,
      ProjectivePoint.«32bit-notables».toPoint_def, hr,
      CompletedPoint.«32bit-notables».toPoint_def]
    exact ⟨Completed.onCurve_toProjective hon, Completed.toPoint_toProjective hon, hb⟩

end «CompletedPoint32bit-notables»

end Curve25519Dalek.backend.serial.curve_models
