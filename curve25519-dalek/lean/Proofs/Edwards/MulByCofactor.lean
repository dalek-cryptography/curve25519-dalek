/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Edwards.MulByPow2
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace «EdwardsPoint64bit-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::mul_by_cofactor`: `8 • self`; limbs `< 2^52`. -/
@[step]
theorem mul_by_cofactor_spec (self : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    mul_by_cofactor self ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = 8 • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_by_cofactor
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, by rw [hr]; rfl, hrb⟩

end «EdwardsPoint64bit-tables»

namespace «EdwardsPoint32bit-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::mul_by_cofactor`: `8 • self`; limbs `< 2^26`. -/
@[step]
theorem mul_by_cofactor_spec (self : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    mul_by_cofactor self ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = 8 • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_by_cofactor
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, by rw [hr]; rfl, hrb⟩

end «EdwardsPoint32bit-tables»

namespace «EdwardsPoint64bit-notables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::mul_by_cofactor`: `8 • self`; limbs `< 2^52`. -/
@[step]
theorem mul_by_cofactor_spec (self : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    mul_by_cofactor self ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = 8 • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_by_cofactor
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, by rw [hr]; rfl, hrb⟩

end «EdwardsPoint64bit-notables»

namespace «EdwardsPoint32bit-notables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::mul_by_cofactor`: `8 • self`; limbs `< 2^26`. -/
@[step]
theorem mul_by_cofactor_spec (self : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    mul_by_cofactor self ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = 8 • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_by_cofactor
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, by rw [hr]; rfl, hrb⟩

end «EdwardsPoint32bit-notables»

end Curve25519Dalek.edwards
