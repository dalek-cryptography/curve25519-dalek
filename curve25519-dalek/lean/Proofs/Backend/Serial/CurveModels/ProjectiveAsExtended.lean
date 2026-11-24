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

/-- `ProjectivePoint::as_extended` over a backend. -/
@[expose] def projectiveAsExtended {P : Type} (mk : B.F → B.F → B.F → B.F → P) (X Y Z : B.F) :
    Result P := do
  let fe ← B.mul X Z
  let fe1 ← B.mul Y Z
  let fe2 ← B.square Z
  let fe3 ← B.mul X Y
  ok (mk fe fe1 fe2 fe3)

/-- `projectiveAsExtended` computes `Projective.toExtended`. -/
theorem projectiveAsExtended_spec
    (hmul : B.MulSpec) (hsq : B.SquareSpec)
    {P : Type} (mk : B.F → B.F → B.F → B.F → P) (X Y Z : B.F)
    (hX : B.Red X) (hY : B.Red Y) (hZ : B.Red Z) :
    B.projectiveAsExtended mk X Y Z ⦃ r => ∃ a b c d, r = mk a b c d ∧
      (⟨B.toField a, B.toField b, B.toField c, B.toField d⟩ : edwards.Extended) =
        (⟨B.toField X, B.toField Y, B.toField Z⟩ : edwards.Projective).toExtended ∧
      B.Red a ∧ B.Red b ∧ B.Red c ∧ B.Red d ⦄ := by
  unfold projectiveAsExtended
  step with hmul X Z (B.red_mulIn hX) (B.red_mulIn hZ) as ⟨a, ha, ha'⟩
  step with hmul Y Z (B.red_mulIn hY) (B.red_mulIn hZ) as ⟨b, hb, hb'⟩
  step with hsq Z (B.red_sqIn hZ) as ⟨c, hc, hc'⟩
  step with hmul X Y (B.red_mulIn hX) (B.red_mulIn hY) as ⟨d, hd, hd'⟩
  exact ⟨a, b, c, d, rfl, by rw [ha, hb, hc, hd]; rfl, ha', hb', hc', hd'⟩

end Curve25519Dalek.Backend

namespace Curve25519Dalek.backend.serial.curve_models

namespace «ProjectivePoint64bit-tables»

theorem as_extended_eq (self : ProjectivePoint.«64bit-tables») :
    as_extended self = Backend.projectiveAsExtended Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«64bit-tables»))
      self.X self.Y self.Z := rfl

/-- `ProjectivePoint::as_extended`: `(X Z : Y Z : Z² : X Y)`, limbs `< 2^52`. -/
@[step]
theorem as_extended_toExtended (self : ProjectivePoint.«64bit-tables») (hself : self.LimbsLt 52) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.toExtended = self.toProjective.toExtended ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hself
  rw [as_extended_eq]
  apply spec_mono (Backend.projectiveAsExtended_spec Backend.U64
    Backend.U64.mul_spec Backend.U64.square_spec _ _ _ _ h1 h2 h3)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [edwards.EdwardsPoint.«64bit-tables».toExtended_def,
    ProjectivePoint.«64bit-tables».toProjective_def]; exact h, ha, hb, hc, hd⟩

/-- `ProjectivePoint::as_extended` represents the same point. -/
theorem as_extended_spec (self : ProjectivePoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_extended_toExtended self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«64bit-tables».onCurve_iff,
      edwards.EdwardsPoint.«64bit-tables».toPoint_def, hr,
      ProjectivePoint.«64bit-tables».toPoint_def]
    exact ⟨Projective.onCurve_toExtended hon, Projective.toPoint_toExtended hon, hb⟩

end «ProjectivePoint64bit-tables»

namespace «ProjectivePoint32bit-tables»

theorem as_extended_eq (self : ProjectivePoint.«32bit-tables») :
    as_extended self = Backend.projectiveAsExtended Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«32bit-tables»))
      self.X self.Y self.Z := rfl

/-- `ProjectivePoint::as_extended`: `(X Z : Y Z : Z² : X Y)`, limbs `< 2^26`. -/
@[step]
theorem as_extended_toExtended (self : ProjectivePoint.«32bit-tables») (hself : self.LimbsLt 26) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.toExtended = self.toProjective.toExtended ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hself
  rw [as_extended_eq]
  apply spec_mono (Backend.projectiveAsExtended_spec Backend.U32
    Backend.U32.mul_spec Backend.U32.square_spec _ _ _ _ h1 h2 h3)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [edwards.EdwardsPoint.«32bit-tables».toExtended_def,
    ProjectivePoint.«32bit-tables».toProjective_def]; exact h, ha, hb, hc, hd⟩

/-- `ProjectivePoint::as_extended` represents the same point. -/
theorem as_extended_spec (self : ProjectivePoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_extended_toExtended self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«32bit-tables».onCurve_iff,
      edwards.EdwardsPoint.«32bit-tables».toPoint_def, hr,
      ProjectivePoint.«32bit-tables».toPoint_def]
    exact ⟨Projective.onCurve_toExtended hon, Projective.toPoint_toExtended hon, hb⟩

end «ProjectivePoint32bit-tables»

namespace «ProjectivePoint64bit-notables»

theorem as_extended_eq (self : ProjectivePoint.«64bit-notables») :
    as_extended self = Backend.projectiveAsExtended Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«64bit-notables»))
      self.X self.Y self.Z := rfl

/-- `ProjectivePoint::as_extended`: `(X Z : Y Z : Z² : X Y)`, limbs `< 2^52`. -/
@[step]
theorem as_extended_toExtended (self : ProjectivePoint.«64bit-notables») (hself : self.LimbsLt
    52) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.toExtended = self.toProjective.toExtended ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hself
  rw [as_extended_eq]
  apply spec_mono (Backend.projectiveAsExtended_spec Backend.U64
    Backend.U64.mul_spec Backend.U64.square_spec _ _ _ _ h1 h2 h3)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [edwards.EdwardsPoint.«64bit-notables».toExtended_def,
    ProjectivePoint.«64bit-notables».toProjective_def]; exact h, ha, hb, hc, hd⟩

/-- `ProjectivePoint::as_extended` represents the same point. -/
theorem as_extended_spec (self : ProjectivePoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_extended_toExtended self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«64bit-notables».onCurve_iff,
      edwards.EdwardsPoint.«64bit-notables».toPoint_def, hr,
      ProjectivePoint.«64bit-notables».toPoint_def]
    exact ⟨Projective.onCurve_toExtended hon, Projective.toPoint_toExtended hon, hb⟩

end «ProjectivePoint64bit-notables»

namespace «ProjectivePoint32bit-notables»

theorem as_extended_eq (self : ProjectivePoint.«32bit-notables») :
    as_extended self = Backend.projectiveAsExtended Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«32bit-notables»))
      self.X self.Y self.Z := rfl

/-- `ProjectivePoint::as_extended`: `(X Z : Y Z : Z² : X Y)`, limbs `< 2^26`. -/
@[step]
theorem as_extended_toExtended (self : ProjectivePoint.«32bit-notables») (hself : self.LimbsLt 26) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.toExtended = self.toProjective.toExtended ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hself
  rw [as_extended_eq]
  apply spec_mono (Backend.projectiveAsExtended_spec Backend.U32
    Backend.U32.mul_spec Backend.U32.square_spec _ _ _ _ h1 h2 h3)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [edwards.EdwardsPoint.«32bit-notables».toExtended_def,
    ProjectivePoint.«32bit-notables».toProjective_def]; exact h, ha, hb, hc, hd⟩

/-- `ProjectivePoint::as_extended` represents the same point. -/
theorem as_extended_spec (self : ProjectivePoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_extended_toExtended self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«32bit-notables».onCurve_iff,
      edwards.EdwardsPoint.«32bit-notables».toPoint_def, hr,
      ProjectivePoint.«32bit-notables».toPoint_def]
    exact ⟨Projective.onCurve_toExtended hon, Projective.toPoint_toExtended hon, hb⟩

end «ProjectivePoint32bit-notables»

end Curve25519Dalek.backend.serial.curve_models
