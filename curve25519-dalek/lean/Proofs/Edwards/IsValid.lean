/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Mathlib.Tactic.LinearCombination
import Proofs.Backend.Serial.CurveModels.ProjectiveIsValid
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Edwards.AsProjective
import Proofs.Field.Eq
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsValidityCheck

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ValidityCheck for EdwardsPoint`: the homogeneous curve equation
`(Y² - X²) Z² = Z⁴ + d X² Y²` and `X Y = Z T` (it does not check `Z ≠ 0`);
limbs `< 2^52`. -/
@[step]
theorem is_valid_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52) :
    is_valid self ⦃ (b : Bool) =>
      b = true ↔ (self.Y.toField ^ 2 - self.X.toField ^ 2) * self.Z.toField ^ 2 =
          self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 ∧
        self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ⦄ := by
  unfold is_valid
  step as ⟨pp, hpp, hppb⟩
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  have hspec :=
    ProjectivePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsValidityCheck.is_valid_spec
  step with hspec as ⟨point_on_curve, hpoc⟩
  step as ⟨XY, hXY, hXY_lt⟩
  step as ⟨ZT, hZT, hZT_lt⟩
  step as ⟨on_segre_image, hseg⟩
  rw [ProjectivePoint.«x86_64-tables».toProjective_def,
    EdwardsPoint.«x86_64-tables».toExtended_def] at hpp
  simp only [Extended.toProjective, Projective.mk.injEq] at hpp
  obtain ⟨hpX, hpY, hpZ⟩ := hpp
  rw [hpX, hpY, hpZ] at hpoc
  rw [← toField_eq_toField_iff, toField_mul_of_mod hXY, toField_mul_of_mod hZT] at hseg
  split_ifs with hb
  · simp only [WP.spec_ok]
    rw [hseg]
    exact ⟨fun h => ⟨hpoc.mp hb, h⟩, fun h => h.2⟩
  · simp only [WP.spec_ok]
    exact iff_of_false Bool.false_ne_true fun h => hb (hpoc.mpr h.1)

/-- `ValidityCheck for EdwardsPoint` with `Z ≠ 0`: `OnCurve`. -/
theorem is_valid_spec_point (self : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hZ : self.Z.toField ≠ 0) :
    is_valid self ⦃ (b : Bool) => b = true ↔ self.OnCurve ⦄ :=
  spec_mono (is_valid_spec self hself) fun b hb => by
    rw [hb, EdwardsPoint.«x86_64-tables».onCurve_iff_homogeneous, a_def, and_iff_right hZ]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by linear_combination h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linear_combination h2, h1⟩

end EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsValidityCheck

namespace EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsValidityCheck

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ValidityCheck for EdwardsPoint`: the homogeneous curve equation
`(Y² - X²) Z² = Z⁴ + d X² Y²` and `X Y = Z T` (it does not check `Z ≠ 0`);
limbs `< 2^26`. -/
@[step]
theorem is_valid_spec (self : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26) :
    is_valid self ⦃ (b : Bool) =>
      b = true ↔ (self.Y.toField ^ 2 - self.X.toField ^ 2) * self.Z.toField ^ 2 =
          self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 ∧
        self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ⦄ := by
  unfold is_valid
  step as ⟨pp, hpp, hppb⟩
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  have hspec :=
    ProjectivePoint.«i686-tables».Insts.Curve25519_dalekTraitsValidityCheck.is_valid_spec
  step with hspec as ⟨point_on_curve, hpoc⟩
  step as ⟨XY, hXY, hXY_lt⟩
  step as ⟨ZT, hZT, hZT_lt⟩
  step as ⟨on_segre_image, hseg⟩
  rw [ProjectivePoint.«i686-tables».toProjective_def,
    EdwardsPoint.«i686-tables».toExtended_def] at hpp
  simp only [Extended.toProjective, Projective.mk.injEq] at hpp
  obtain ⟨hpX, hpY, hpZ⟩ := hpp
  rw [hpX, hpY, hpZ] at hpoc
  rw [← toField_eq_toField_iff, toField_mul_of_mod hXY, toField_mul_of_mod hZT] at hseg
  split_ifs with hb
  · simp only [WP.spec_ok]
    rw [hseg]
    exact ⟨fun h => ⟨hpoc.mp hb, h⟩, fun h => h.2⟩
  · simp only [WP.spec_ok]
    exact iff_of_false Bool.false_ne_true fun h => hb (hpoc.mpr h.1)

/-- `ValidityCheck for EdwardsPoint` with `Z ≠ 0`: `OnCurve`. -/
theorem is_valid_spec_point (self : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hZ : self.Z.toField ≠ 0) :
    is_valid self ⦃ (b : Bool) => b = true ↔ self.OnCurve ⦄ :=
  spec_mono (is_valid_spec self hself) fun b hb => by
    rw [hb, EdwardsPoint.«i686-tables».onCurve_iff_homogeneous, a_def, and_iff_right hZ]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by linear_combination h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linear_combination h2, h1⟩

end EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsValidityCheck

namespace EdwardsPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsValidityCheck

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ValidityCheck for EdwardsPoint`: the homogeneous curve equation
`(Y² - X²) Z² = Z⁴ + d X² Y²` and `X Y = Z T` (it does not check `Z ≠ 0`);
limbs `< 2^52`. -/
@[step]
theorem is_valid_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52) :
    is_valid self ⦃ (b : Bool) =>
      b = true ↔ (self.Y.toField ^ 2 - self.X.toField ^ 2) * self.Z.toField ^ 2 =
          self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 ∧
        self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ⦄ := by
  unfold is_valid
  step as ⟨pp, hpp, hppb⟩
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  have hspec :=
    ProjectivePoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsValidityCheck.is_valid_spec
  step with hspec as ⟨point_on_curve, hpoc⟩
  step as ⟨XY, hXY, hXY_lt⟩
  step as ⟨ZT, hZT, hZT_lt⟩
  step as ⟨on_segre_image, hseg⟩
  rw [ProjectivePoint.«x86_64-no-tables».toProjective_def,
    EdwardsPoint.«x86_64-no-tables».toExtended_def] at hpp
  simp only [Extended.toProjective, Projective.mk.injEq] at hpp
  obtain ⟨hpX, hpY, hpZ⟩ := hpp
  rw [hpX, hpY, hpZ] at hpoc
  rw [← toField_eq_toField_iff, toField_mul_of_mod hXY, toField_mul_of_mod hZT] at hseg
  split_ifs with hb
  · simp only [WP.spec_ok]
    rw [hseg]
    exact ⟨fun h => ⟨hpoc.mp hb, h⟩, fun h => h.2⟩
  · simp only [WP.spec_ok]
    exact iff_of_false Bool.false_ne_true fun h => hb (hpoc.mpr h.1)

/-- `ValidityCheck for EdwardsPoint` with `Z ≠ 0`: `OnCurve`. -/
theorem is_valid_spec_point (self : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hZ : self.Z.toField ≠ 0) :
    is_valid self ⦃ (b : Bool) => b = true ↔ self.OnCurve ⦄ :=
  spec_mono (is_valid_spec self hself) fun b hb => by
    rw [hb, EdwardsPoint.«x86_64-no-tables».onCurve_iff_homogeneous, a_def, and_iff_right hZ]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by linear_combination h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linear_combination h2, h1⟩

end EdwardsPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsValidityCheck

namespace EdwardsPoint.«i686-no-tables».Insts.Curve25519_dalekTraitsValidityCheck

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ValidityCheck for EdwardsPoint`: the homogeneous curve equation
`(Y² - X²) Z² = Z⁴ + d X² Y²` and `X Y = Z T` (it does not check `Z ≠ 0`);
limbs `< 2^26`. -/
@[step]
theorem is_valid_spec (self : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26) :
    is_valid self ⦃ (b : Bool) =>
      b = true ↔ (self.Y.toField ^ 2 - self.X.toField ^ 2) * self.Z.toField ^ 2 =
          self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 ∧
        self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ⦄ := by
  unfold is_valid
  step as ⟨pp, hpp, hppb⟩
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  have hspec :=
    ProjectivePoint.«i686-no-tables».Insts.Curve25519_dalekTraitsValidityCheck.is_valid_spec
  step with hspec as ⟨point_on_curve, hpoc⟩
  step as ⟨XY, hXY, hXY_lt⟩
  step as ⟨ZT, hZT, hZT_lt⟩
  step as ⟨on_segre_image, hseg⟩
  rw [ProjectivePoint.«i686-no-tables».toProjective_def,
    EdwardsPoint.«i686-no-tables».toExtended_def] at hpp
  simp only [Extended.toProjective, Projective.mk.injEq] at hpp
  obtain ⟨hpX, hpY, hpZ⟩ := hpp
  rw [hpX, hpY, hpZ] at hpoc
  rw [← toField_eq_toField_iff, toField_mul_of_mod hXY, toField_mul_of_mod hZT] at hseg
  split_ifs with hb
  · simp only [WP.spec_ok]
    rw [hseg]
    exact ⟨fun h => ⟨hpoc.mp hb, h⟩, fun h => h.2⟩
  · simp only [WP.spec_ok]
    exact iff_of_false Bool.false_ne_true fun h => hb (hpoc.mpr h.1)

/-- `ValidityCheck for EdwardsPoint` with `Z ≠ 0`: `OnCurve`. -/
theorem is_valid_spec_point (self : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hZ : self.Z.toField ≠ 0) :
    is_valid self ⦃ (b : Bool) => b = true ↔ self.OnCurve ⦄ :=
  spec_mono (is_valid_spec self hself) fun b hb => by
    rw [hb, EdwardsPoint.«i686-no-tables».onCurve_iff_homogeneous, a_def, and_iff_right hZ]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by linear_combination h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linear_combination h2, h1⟩

end EdwardsPoint.«i686-no-tables».Insts.Curve25519_dalekTraitsValidityCheck

end Curve25519Dalek.edwards
