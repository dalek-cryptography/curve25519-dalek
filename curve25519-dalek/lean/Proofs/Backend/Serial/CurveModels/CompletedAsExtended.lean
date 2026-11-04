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

namespace Curve25519Dalek.Backend

variable (B : Backend)

/-- `CompletedPoint::as_extended` over a backend. -/
@[expose] def completedAsExtended {P : Type} (mk : B.F → B.F → B.F → B.F → P)
    (X Y Z T : B.F) : Result P := do
  let fe ← B.mul X T
  let fe1 ← B.mul Y Z
  let fe2 ← B.mul Z T
  let fe3 ← B.mul X Y
  ok (mk fe fe1 fe2 fe3)

/-- `completedAsExtended` computes `Completed.toExtended`. -/
theorem completedAsExtended_spec
    (hmul : B.MulSpec)
    {P : Type} (mk : B.F → B.F → B.F → B.F → P) (X Y Z T : B.F)
    (hX : B.MulIn X) (hY : B.MulIn Y) (hZ : B.MulIn Z) (hT : B.MulIn T) :
    B.completedAsExtended mk X Y Z T ⦃ r => ∃ a b c d, r = mk a b c d ∧
      (⟨B.toField a, B.toField b, B.toField c, B.toField d⟩ : edwards.Extended) =
        (⟨B.toField X, B.toField Y, B.toField Z, B.toField T⟩ : edwards.Completed).toExtended ∧
      B.Red a ∧ B.Red b ∧ B.Red c ∧ B.Red d ⦄ := by
  unfold completedAsExtended
  step with hmul X T hX hT as ⟨a, ha, ha'⟩
  step with hmul Y Z hY hZ as ⟨b, hb, hb'⟩
  step with hmul Z T hZ hT as ⟨c, hc, hc'⟩
  step with hmul X Y hX hY as ⟨d, hd, hd'⟩
  exact ⟨a, b, c, d, rfl, by rw [ha, hb, hc, hd]; rfl, ha', hb', hc', hd'⟩

end Curve25519Dalek.Backend

namespace Curve25519Dalek.backend.serial.curve_models

namespace «CompletedPointx86_64-tables»

theorem as_extended_eq (self : CompletedPoint.«x86_64-tables») :
    as_extended self = Backend.completedAsExtended Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«x86_64-tables»))
      self.X self.Y self.Z self.T := rfl

/-- `CompletedPoint::as_extended`: `(X T : Y Z : Z T : X Y)`, limbs `< 2^52`. -/
@[step]
theorem as_extended_spec (self : CompletedPoint.«x86_64-tables») (hself : self.LimbsLt 54) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.toExtended = self.toCompleted.toExtended ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  rw [as_extended_eq]
  apply spec_mono (Backend.completedAsExtended_spec Backend.U64
    Backend.U64.mul_spec _ _ _ _ _ h1 h2 h3 h4)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [edwards.EdwardsPoint.«x86_64-tables».toExtended_def,
    CompletedPoint.«x86_64-tables».toCompleted_def]; exact h, ha, hb, hc, hd⟩

/-- `CompletedPoint::as_extended` represents the same point. -/
theorem as_extended_spec_point (self : CompletedPoint.«x86_64-tables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_extended_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«x86_64-tables».onCurve_iff,
      edwards.EdwardsPoint.«x86_64-tables».toPoint_def, hr,
      CompletedPoint.«x86_64-tables».toPoint_def]
    exact ⟨Completed.onCurve_toExtended hon, Completed.toPoint_toExtended hon, hb⟩

end «CompletedPointx86_64-tables»

namespace «CompletedPointi686-tables»

theorem as_extended_eq (self : CompletedPoint.«i686-tables») :
    as_extended self = Backend.completedAsExtended Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«i686-tables»))
      self.X self.Y self.Z self.T := rfl

/-- `CompletedPoint::as_extended`: `(X T : Y Z : Z T : X Y)`, limbs `< 2^26`. -/
@[step]
theorem as_extended_spec (self : CompletedPoint.«i686-tables») (hself : self.MulBounded) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.toExtended = self.toCompleted.toExtended ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  rw [as_extended_eq]
  apply spec_mono (Backend.completedAsExtended_spec Backend.U32
    Backend.U32.mul_spec _ _ _ _ _ h1 h2 h3 h4)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [edwards.EdwardsPoint.«i686-tables».toExtended_def,
    CompletedPoint.«i686-tables».toCompleted_def]; exact h, ha, hb, hc, hd⟩

/-- `CompletedPoint::as_extended` represents the same point. -/
theorem as_extended_spec_point (self : CompletedPoint.«i686-tables») (hself : self.MulBounded)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_extended_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«i686-tables».onCurve_iff,
      edwards.EdwardsPoint.«i686-tables».toPoint_def, hr,
      CompletedPoint.«i686-tables».toPoint_def]
    exact ⟨Completed.onCurve_toExtended hon, Completed.toPoint_toExtended hon, hb⟩

end «CompletedPointi686-tables»

namespace «CompletedPointx86_64-no-tables»

theorem as_extended_eq (self : CompletedPoint.«x86_64-no-tables») :
    as_extended self = Backend.completedAsExtended Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«x86_64-no-tables»))
      self.X self.Y self.Z self.T := rfl

/-- `CompletedPoint::as_extended`: `(X T : Y Z : Z T : X Y)`, limbs `< 2^52`. -/
@[step]
theorem as_extended_spec (self : CompletedPoint.«x86_64-no-tables») (hself : self.LimbsLt 54) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended = self.toCompleted.toExtended ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  rw [as_extended_eq]
  apply spec_mono (Backend.completedAsExtended_spec Backend.U64
    Backend.U64.mul_spec _ _ _ _ _ h1 h2 h3 h4)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def,
    CompletedPoint.«x86_64-no-tables».toCompleted_def]; exact h, ha, hb, hc, hd⟩

/-- `CompletedPoint::as_extended` represents the same point. -/
theorem as_extended_spec_point (self : CompletedPoint.«x86_64-no-tables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_extended_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«x86_64-no-tables».onCurve_iff,
      edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def, hr,
      CompletedPoint.«x86_64-no-tables».toPoint_def]
    exact ⟨Completed.onCurve_toExtended hon, Completed.toPoint_toExtended hon, hb⟩

end «CompletedPointx86_64-no-tables»

namespace «CompletedPointi686-no-tables»

theorem as_extended_eq (self : CompletedPoint.«i686-no-tables») :
    as_extended self = Backend.completedAsExtended Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«i686-no-tables»))
      self.X self.Y self.Z self.T := rfl

/-- `CompletedPoint::as_extended`: `(X T : Y Z : Z T : X Y)`, limbs `< 2^26`. -/
@[step]
theorem as_extended_spec (self : CompletedPoint.«i686-no-tables») (hself : self.MulBounded) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.toExtended = self.toCompleted.toExtended ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  rw [as_extended_eq]
  apply spec_mono (Backend.completedAsExtended_spec Backend.U32
    Backend.U32.mul_spec _ _ _ _ _ h1 h2 h3 h4)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [edwards.EdwardsPoint.«i686-no-tables».toExtended_def,
    CompletedPoint.«i686-no-tables».toCompleted_def]; exact h, ha, hb, hc, hd⟩

/-- `CompletedPoint::as_extended` represents the same point. -/
theorem as_extended_spec_point (self : CompletedPoint.«i686-no-tables») (hself : self.MulBounded)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_extended_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«i686-no-tables».onCurve_iff,
      edwards.EdwardsPoint.«i686-no-tables».toPoint_def, hr,
      CompletedPoint.«i686-no-tables».toPoint_def]
    exact ⟨Completed.onCurve_toExtended hon, Completed.toPoint_toExtended hon, hb⟩

end «CompletedPointi686-no-tables»

end Curve25519Dalek.backend.serial.curve_models
