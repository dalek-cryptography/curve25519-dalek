module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
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

namespace «CompletedPoint64bit-tables»

theorem as_extended_eq (self : CompletedPoint.«64bit-tables») :
    as_extended self = Backend.completedAsExtended Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«64bit-tables»))
      self.X self.Y self.Z self.T := rfl

/-- `CompletedPoint::as_extended`: `(X T : Y Z : Z T : X Y)`, limbs `< 2^52`. -/
@[step]
theorem as_extended_toExtended (self : CompletedPoint.«64bit-tables») (hself : self.LimbsLt 54) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.toExtended = self.toCompleted.toExtended ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  rw [as_extended_eq]
  apply spec_mono (Backend.completedAsExtended_spec Backend.U64
    Backend.U64.mul_spec _ _ _ _ _ h1 h2 h3 h4)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [edwards.EdwardsPoint.«64bit-tables».toExtended_def,
    CompletedPoint.«64bit-tables».toCompleted_def]; exact h, ha, hb, hc, hd⟩

/-- `CompletedPoint::as_extended` represents the same point. -/
theorem as_extended_spec (self : CompletedPoint.«64bit-tables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_extended_toExtended self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«64bit-tables».onCurve_iff,
      edwards.EdwardsPoint.«64bit-tables».toPoint_def, hr,
      CompletedPoint.«64bit-tables».toPoint_def]
    exact ⟨Completed.onCurve_toExtended hon, Completed.toPoint_toExtended hon, hb⟩

end «CompletedPoint64bit-tables»

namespace «CompletedPoint32bit-tables»

theorem as_extended_eq (self : CompletedPoint.«32bit-tables») :
    as_extended self = Backend.completedAsExtended Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«32bit-tables»))
      self.X self.Y self.Z self.T := rfl

/-- `CompletedPoint::as_extended`: `(X T : Y Z : Z T : X Y)`, limbs `< 2^26`. -/
@[step]
theorem as_extended_toExtended (self : CompletedPoint.«32bit-tables») (hself : self.MulBounded) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.toExtended = self.toCompleted.toExtended ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  rw [as_extended_eq]
  apply spec_mono (Backend.completedAsExtended_spec Backend.U32
    Backend.U32.mul_spec _ _ _ _ _ h1 h2 h3 h4)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [edwards.EdwardsPoint.«32bit-tables».toExtended_def,
    CompletedPoint.«32bit-tables».toCompleted_def]; exact h, ha, hb, hc, hd⟩

/-- `CompletedPoint::as_extended` represents the same point. -/
theorem as_extended_spec (self : CompletedPoint.«32bit-tables») (hself : self.MulBounded)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_extended_toExtended self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«32bit-tables».onCurve_iff,
      edwards.EdwardsPoint.«32bit-tables».toPoint_def, hr,
      CompletedPoint.«32bit-tables».toPoint_def]
    exact ⟨Completed.onCurve_toExtended hon, Completed.toPoint_toExtended hon, hb⟩

end «CompletedPoint32bit-tables»

namespace «CompletedPoint64bit-notables»

theorem as_extended_eq (self : CompletedPoint.«64bit-notables») :
    as_extended self = Backend.completedAsExtended Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«64bit-notables»))
      self.X self.Y self.Z self.T := rfl

/-- `CompletedPoint::as_extended`: `(X T : Y Z : Z T : X Y)`, limbs `< 2^52`. -/
@[step]
theorem as_extended_toExtended (self : CompletedPoint.«64bit-notables») (hself : self.LimbsLt 54)
    :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.toExtended = self.toCompleted.toExtended ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  rw [as_extended_eq]
  apply spec_mono (Backend.completedAsExtended_spec Backend.U64
    Backend.U64.mul_spec _ _ _ _ _ h1 h2 h3 h4)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [edwards.EdwardsPoint.«64bit-notables».toExtended_def,
    CompletedPoint.«64bit-notables».toCompleted_def]; exact h, ha, hb, hc, hd⟩

/-- `CompletedPoint::as_extended` represents the same point. -/
theorem as_extended_spec (self : CompletedPoint.«64bit-notables») (hself : self.LimbsLt 54)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_extended_toExtended self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«64bit-notables».onCurve_iff,
      edwards.EdwardsPoint.«64bit-notables».toPoint_def, hr,
      CompletedPoint.«64bit-notables».toPoint_def]
    exact ⟨Completed.onCurve_toExtended hon, Completed.toPoint_toExtended hon, hb⟩

end «CompletedPoint64bit-notables»

namespace «CompletedPoint32bit-notables»

theorem as_extended_eq (self : CompletedPoint.«32bit-notables») :
    as_extended self = Backend.completedAsExtended Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«32bit-notables»))
      self.X self.Y self.Z self.T := rfl

/-- `CompletedPoint::as_extended`: `(X T : Y Z : Z T : X Y)`, limbs `< 2^26`. -/
@[step]
theorem as_extended_toExtended (self : CompletedPoint.«32bit-notables») (hself : self.MulBounded) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.toExtended = self.toCompleted.toExtended ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨h1, h2, h3, h4⟩ := hself
  rw [as_extended_eq]
  apply spec_mono (Backend.completedAsExtended_spec Backend.U32
    Backend.U32.mul_spec _ _ _ _ _ h1 h2 h3 h4)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [edwards.EdwardsPoint.«32bit-notables».toExtended_def,
    CompletedPoint.«32bit-notables».toCompleted_def]; exact h, ha, hb, hc, hd⟩

/-- `CompletedPoint::as_extended` represents the same point. -/
theorem as_extended_spec (self : CompletedPoint.«32bit-notables») (hself : self.MulBounded)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_extended_toExtended self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«32bit-notables».onCurve_iff,
      edwards.EdwardsPoint.«32bit-notables».toPoint_def, hr,
      CompletedPoint.«32bit-notables».toPoint_def]
    exact ⟨Completed.onCurve_toExtended hon, Completed.toPoint_toExtended hon, hb⟩

end «CompletedPoint32bit-notables»

end Curve25519Dalek.backend.serial.curve_models
