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

namespace «ProjectivePointx86_64-tables»

theorem as_extended_eq (self : ProjectivePoint.«x86_64-tables») :
    as_extended self = Backend.projectiveAsExtended Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«x86_64-tables»))
      self.X self.Y self.Z := rfl

/-- `ProjectivePoint::as_extended`: `(X Z : Y Z : Z² : X Y)`, limbs `< 2^52`. -/
@[step]
theorem as_extended_spec (self : ProjectivePoint.«x86_64-tables») (hself : self.LimbsLt 52) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.toExtended = self.toProjective.toExtended ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hself
  rw [as_extended_eq]
  apply spec_mono (Backend.projectiveAsExtended_spec Backend.U64
    Backend.U64.mul_spec Backend.U64.square_spec _ _ _ _ h1 h2 h3)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [edwards.EdwardsPoint.«x86_64-tables».toExtended_def,
    ProjectivePoint.«x86_64-tables».toProjective_def]; exact h, ha, hb, hc, hd⟩

/-- `ProjectivePoint::as_extended` represents the same point. -/
theorem as_extended_spec_point (self : ProjectivePoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_extended_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«x86_64-tables».onCurve_iff,
      edwards.EdwardsPoint.«x86_64-tables».toPoint_def, hr,
      ProjectivePoint.«x86_64-tables».toPoint_def]
    exact ⟨Projective.onCurve_toExtended hon, Projective.toPoint_toExtended hon, hb⟩

end «ProjectivePointx86_64-tables»

namespace «ProjectivePointi686-tables»

theorem as_extended_eq (self : ProjectivePoint.«i686-tables») :
    as_extended self = Backend.projectiveAsExtended Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«i686-tables»))
      self.X self.Y self.Z := rfl

/-- `ProjectivePoint::as_extended`: `(X Z : Y Z : Z² : X Y)`, limbs `< 2^26`. -/
@[step]
theorem as_extended_spec (self : ProjectivePoint.«i686-tables») (hself : self.LimbsLt 26) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.toExtended = self.toProjective.toExtended ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hself
  rw [as_extended_eq]
  apply spec_mono (Backend.projectiveAsExtended_spec Backend.U32
    Backend.U32.mul_spec Backend.U32.square_spec _ _ _ _ h1 h2 h3)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [edwards.EdwardsPoint.«i686-tables».toExtended_def,
    ProjectivePoint.«i686-tables».toProjective_def]; exact h, ha, hb, hc, hd⟩

/-- `ProjectivePoint::as_extended` represents the same point. -/
theorem as_extended_spec_point (self : ProjectivePoint.«i686-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_extended_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«i686-tables».onCurve_iff,
      edwards.EdwardsPoint.«i686-tables».toPoint_def, hr,
      ProjectivePoint.«i686-tables».toPoint_def]
    exact ⟨Projective.onCurve_toExtended hon, Projective.toPoint_toExtended hon, hb⟩

end «ProjectivePointi686-tables»

namespace «ProjectivePointx86_64-no-tables»

theorem as_extended_eq (self : ProjectivePoint.«x86_64-no-tables») :
    as_extended self = Backend.projectiveAsExtended Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«x86_64-no-tables»))
      self.X self.Y self.Z := rfl

/-- `ProjectivePoint::as_extended`: `(X Z : Y Z : Z² : X Y)`, limbs `< 2^52`. -/
@[step]
theorem as_extended_spec (self : ProjectivePoint.«x86_64-no-tables») (hself : self.LimbsLt 52) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended = self.toProjective.toExtended ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hself
  rw [as_extended_eq]
  apply spec_mono (Backend.projectiveAsExtended_spec Backend.U64
    Backend.U64.mul_spec Backend.U64.square_spec _ _ _ _ h1 h2 h3)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def,
    ProjectivePoint.«x86_64-no-tables».toProjective_def]; exact h, ha, hb, hc, hd⟩

/-- `ProjectivePoint::as_extended` represents the same point. -/
theorem as_extended_spec_point (self : ProjectivePoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_extended_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«x86_64-no-tables».onCurve_iff,
      edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def, hr,
      ProjectivePoint.«x86_64-no-tables».toPoint_def]
    exact ⟨Projective.onCurve_toExtended hon, Projective.toPoint_toExtended hon, hb⟩

end «ProjectivePointx86_64-no-tables»

namespace «ProjectivePointi686-no-tables»

theorem as_extended_eq (self : ProjectivePoint.«i686-no-tables») :
    as_extended self = Backend.projectiveAsExtended Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«i686-no-tables»))
      self.X self.Y self.Z := rfl

/-- `ProjectivePoint::as_extended`: `(X Z : Y Z : Z² : X Y)`, limbs `< 2^26`. -/
@[step]
theorem as_extended_spec (self : ProjectivePoint.«i686-no-tables») (hself : self.LimbsLt 26) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.toExtended = self.toProjective.toExtended ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hself
  rw [as_extended_eq]
  apply spec_mono (Backend.projectiveAsExtended_spec Backend.U32
    Backend.U32.mul_spec Backend.U32.square_spec _ _ _ _ h1 h2 h3)
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  exact ⟨by rw [edwards.EdwardsPoint.«i686-no-tables».toExtended_def,
    ProjectivePoint.«i686-no-tables».toProjective_def]; exact h, ha, hb, hc, hd⟩

/-- `ProjectivePoint::as_extended` represents the same point. -/
theorem as_extended_spec_point (self : ProjectivePoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    as_extended self ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_extended_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«i686-no-tables».onCurve_iff,
      edwards.EdwardsPoint.«i686-no-tables».toPoint_def, hr,
      ProjectivePoint.«i686-no-tables».toPoint_def]
    exact ⟨Projective.onCurve_toExtended hon, Projective.toPoint_toExtended hon, hb⟩

end «ProjectivePointi686-no-tables»

end Curve25519Dalek.backend.serial.curve_models
