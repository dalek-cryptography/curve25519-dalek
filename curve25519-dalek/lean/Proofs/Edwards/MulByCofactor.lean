/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Edwards.MulByPow2
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::mul_by_cofactor`: `8 • P`; limbs `< 2^52`. -/
@[step]
theorem mul_by_cofactor_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    mul_by_cofactor self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 8 • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_by_cofactor
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, by rw [hr]; rfl, hrb⟩

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::mul_by_cofactor`: `8 • P`; limbs `< 2^26`. -/
@[step]
theorem mul_by_cofactor_spec (self : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    mul_by_cofactor self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = 8 • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_by_cofactor
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, by rw [hr]; rfl, hrb⟩

end «EdwardsPointi686-tables»

namespace «EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::mul_by_cofactor`: `8 • P`; limbs `< 2^52`. -/
@[step]
theorem mul_by_cofactor_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    mul_by_cofactor self ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 8 • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_by_cofactor
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, by rw [hr]; rfl, hrb⟩

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::mul_by_cofactor`: `8 • P`; limbs `< 2^26`. -/
@[step]
theorem mul_by_cofactor_spec (self : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    mul_by_cofactor self ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = 8 • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_by_cofactor
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, by rw [hr]; rfl, hrb⟩

end «EdwardsPointi686-no-tables»

end Curve25519Dalek.edwards
