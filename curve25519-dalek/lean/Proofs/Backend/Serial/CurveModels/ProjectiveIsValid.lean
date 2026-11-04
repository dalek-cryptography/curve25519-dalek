/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.CurveModels
import Mathlib.Tactic.LinearCombination
public import Proofs.Helpers.Coords
public import Proofs.Helpers.Backend.U32
public import Proofs.Helpers.Backend.U64
import Proofs.Helpers.Backend.U32.Bytes
import Proofs.Helpers.Backend.U64.Bytes
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel

namespace Curve25519Dalek.Backend

variable (B : Backend)

/-- `ValidityCheck for ProjectivePoint` over a backend. -/
@[expose] def projectiveIsValid (X Y Z : B.F) : Result Bool := do
  let XX ← B.square X
  let YY ← B.square Y
  let ZZ ← B.square Z
  let ZZZZ ← B.square ZZ
  let fe ← B.sub YY XX
  let lhs ← B.mul fe ZZ
  let fe1 ← B.constEdwardsD
  let fe2 ← B.mul XX YY
  let fe3 ← B.mul fe1 fe2
  let rhs ← B.add ZZZZ fe3
  B.eq lhs rhs

/-- `projectiveIsValid` checks the homogeneous curve equation. -/
theorem projectiveIsValid_spec
    (hadd : B.AddSpec) (hsub : B.SubSpec) (hmul : B.MulSpec) (hsq : B.SquareSpec) (heq : B.EqSpec)
    (hD : B.EdwardsDSpec)
    (X Y Z : B.F) (hX : B.Red X) (hY : B.Red Y) (hZ : B.Red Z) :
    B.projectiveIsValid X Y Z ⦃ (b : Bool) =>
      b = true ↔ (B.toField Y ^ 2 - B.toField X ^ 2) * B.toField Z ^ 2 =
        B.toField Z ^ 4 + d * B.toField X ^ 2 * B.toField Y ^ 2 ⦄ := by
  unfold projectiveIsValid
  step with hsq X (B.red_sqIn hX) as ⟨xx, hxx, hxx'⟩
  step with hsq Y (B.red_sqIn hY) as ⟨yy, hyy, hyy'⟩
  step with hsq Z (B.red_sqIn hZ) as ⟨zz, hzz, hzz'⟩
  step with hsq zz (B.red_sqIn hzz') as ⟨z4, hz4, hz4'⟩
  step with hsub yy xx (B.red_mulIn hyy') (B.red_mulIn hxx') as ⟨yx, hyx, hyx'⟩
  step with hmul yx zz (B.red_mulIn hyx') (B.red_mulIn hzz') as ⟨lhs, hlhs, _⟩
  apply spec_bind hD
  rintro dd ⟨hdd, hdd'⟩
  step with hmul xx yy (B.red_mulIn hxx') (B.red_mulIn hyy') as ⟨xy, hxy, hxy'⟩
  step with hmul dd xy (B.red_mulIn hdd') (B.red_mulIn hxy') as ⟨dxy, hdxy, hdxy'⟩
  step with hadd z4 dxy hz4' hdxy' as ⟨rhs, hrhs, _⟩
  apply spec_mono (heq lhs rhs)
  intro c hc
  rw [hc, hlhs, hrhs, hyx, hdxy, hxy, hz4, hzz, hxx, hyy, hdd]
  constructor <;> intro h <;> linear_combination h

end Curve25519Dalek.Backend

namespace Curve25519Dalek.backend.serial.curve_models

namespace ProjectivePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsValidityCheck

theorem is_valid_eq (self : ProjectivePoint.«x86_64-tables») :
    is_valid self = Backend.projectiveIsValid Backend.U64
      self.X self.Y self.Z := rfl

/-- `ValidityCheck for ProjectivePoint`: the homogeneous curve equation
`(Y² - X²) Z² = Z⁴ + d X² Y²` (it does not check `Z ≠ 0`); limbs `< 2^52`. -/
@[step]
theorem is_valid_spec (self : ProjectivePoint.«x86_64-tables») (hself : self.LimbsLt 52) :
    is_valid self ⦃ (b : Bool) =>
      b = true ↔ (self.Y.toField ^ 2 - self.X.toField ^ 2) * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hself
  rw [is_valid_eq]
  exact Backend.projectiveIsValid_spec Backend.U64
    Backend.U64.add_spec Backend.U64.sub_spec Backend.U64.mul_spec Backend.U64.square_spec
    Backend.U64.eq_spec Backend.U64.edwardsD_spec _ _ _ h1 h2 h3

/-- `ValidityCheck for ProjectivePoint` with `Z ≠ 0`: `OnCurve`. -/
theorem is_valid_spec_point (self : ProjectivePoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hZ : self.Z.toField ≠ 0) :
    is_valid self ⦃ (b : Bool) => b = true ↔ self.OnCurve ⦄ :=
  spec_mono (is_valid_spec self hself) fun b hb => by
    rw [hb, ProjectivePoint.«x86_64-tables».onCurve_iff_homogeneous, a_def, and_iff_right hZ]
    constructor <;> intro h <;> linear_combination h

end ProjectivePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsValidityCheck

namespace ProjectivePoint.«i686-tables».Insts.Curve25519_dalekTraitsValidityCheck

theorem is_valid_eq (self : ProjectivePoint.«i686-tables») :
    is_valid self = Backend.projectiveIsValid Backend.U32
      self.X self.Y self.Z := rfl

/-- `ValidityCheck for ProjectivePoint`: the homogeneous curve equation
`(Y² - X²) Z² = Z⁴ + d X² Y²` (it does not check `Z ≠ 0`); limbs `< 2^26`. -/
@[step]
theorem is_valid_spec (self : ProjectivePoint.«i686-tables») (hself : self.LimbsLt 26) :
    is_valid self ⦃ (b : Bool) =>
      b = true ↔ (self.Y.toField ^ 2 - self.X.toField ^ 2) * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hself
  rw [is_valid_eq]
  exact Backend.projectiveIsValid_spec Backend.U32
    Backend.U32.add_spec Backend.U32.sub_spec Backend.U32.mul_spec Backend.U32.square_spec
    Backend.U32.eq_spec Backend.U32.edwardsD_spec _ _ _ h1 h2 h3

/-- `ValidityCheck for ProjectivePoint` with `Z ≠ 0`: `OnCurve`. -/
theorem is_valid_spec_point (self : ProjectivePoint.«i686-tables») (hself : self.LimbsLt 26)
    (hZ : self.Z.toField ≠ 0) :
    is_valid self ⦃ (b : Bool) => b = true ↔ self.OnCurve ⦄ :=
  spec_mono (is_valid_spec self hself) fun b hb => by
    rw [hb, ProjectivePoint.«i686-tables».onCurve_iff_homogeneous, a_def, and_iff_right hZ]
    constructor <;> intro h <;> linear_combination h

end ProjectivePoint.«i686-tables».Insts.Curve25519_dalekTraitsValidityCheck

namespace ProjectivePoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsValidityCheck

theorem is_valid_eq (self : ProjectivePoint.«x86_64-no-tables») :
    is_valid self = Backend.projectiveIsValid Backend.U64
      self.X self.Y self.Z := rfl

/-- `ValidityCheck for ProjectivePoint`: the homogeneous curve equation
`(Y² - X²) Z² = Z⁴ + d X² Y²` (it does not check `Z ≠ 0`); limbs `< 2^52`. -/
@[step]
theorem is_valid_spec (self : ProjectivePoint.«x86_64-no-tables») (hself : self.LimbsLt 52) :
    is_valid self ⦃ (b : Bool) =>
      b = true ↔ (self.Y.toField ^ 2 - self.X.toField ^ 2) * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hself
  rw [is_valid_eq]
  exact Backend.projectiveIsValid_spec Backend.U64
    Backend.U64.add_spec Backend.U64.sub_spec Backend.U64.mul_spec Backend.U64.square_spec
    Backend.U64.eq_spec Backend.U64.edwardsD_spec _ _ _ h1 h2 h3

/-- `ValidityCheck for ProjectivePoint` with `Z ≠ 0`: `OnCurve`. -/
theorem is_valid_spec_point (self : ProjectivePoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hZ : self.Z.toField ≠ 0) :
    is_valid self ⦃ (b : Bool) => b = true ↔ self.OnCurve ⦄ :=
  spec_mono (is_valid_spec self hself) fun b hb => by
    rw [hb, ProjectivePoint.«x86_64-no-tables».onCurve_iff_homogeneous, a_def, and_iff_right hZ]
    constructor <;> intro h <;> linear_combination h

end ProjectivePoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsValidityCheck

namespace ProjectivePoint.«i686-no-tables».Insts.Curve25519_dalekTraitsValidityCheck

theorem is_valid_eq (self : ProjectivePoint.«i686-no-tables») :
    is_valid self = Backend.projectiveIsValid Backend.U32
      self.X self.Y self.Z := rfl

/-- `ValidityCheck for ProjectivePoint`: the homogeneous curve equation
`(Y² - X²) Z² = Z⁴ + d X² Y²` (it does not check `Z ≠ 0`); limbs `< 2^26`. -/
@[step]
theorem is_valid_spec (self : ProjectivePoint.«i686-no-tables») (hself : self.LimbsLt 26) :
    is_valid self ⦃ (b : Bool) =>
      b = true ↔ (self.Y.toField ^ 2 - self.X.toField ^ 2) * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hself
  rw [is_valid_eq]
  exact Backend.projectiveIsValid_spec Backend.U32
    Backend.U32.add_spec Backend.U32.sub_spec Backend.U32.mul_spec Backend.U32.square_spec
    Backend.U32.eq_spec Backend.U32.edwardsD_spec _ _ _ h1 h2 h3

/-- `ValidityCheck for ProjectivePoint` with `Z ≠ 0`: `OnCurve`. -/
theorem is_valid_spec_point (self : ProjectivePoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hZ : self.Z.toField ≠ 0) :
    is_valid self ⦃ (b : Bool) => b = true ↔ self.OnCurve ⦄ :=
  spec_mono (is_valid_spec self hself) fun b hb => by
    rw [hb, ProjectivePoint.«i686-no-tables».onCurve_iff_homogeneous, a_def, and_iff_right hZ]
    constructor <;> intro h <;> linear_combination h

end ProjectivePoint.«i686-no-tables».Insts.Curve25519_dalekTraitsValidityCheck

end Curve25519Dalek.backend.serial.curve_models
