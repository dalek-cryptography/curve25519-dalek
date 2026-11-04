/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
import Proofs.Backend.Serial.U32.Field.FromLimbs
import Proofs.Helpers.FieldElement2625
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open curve25519 (p a d A)
open curve25519 (lt_p_iff mod_p_fold mod_p_of_lt a_def d_eq_natCast)

namespace Curve25519Dalek.backend.serial.u32.constants

@[step]
theorem SQRT_AD_MINUS_ONE_spec :
    SQRT_AD_MINUS_ONE ⦃ (r : FieldElement2625) =>
      r.asNat < p ∧
      r.asNat ^ 2 % p = (a * d - 1).val ∧ r.LimbsLt 26 ⦄ := by
  unfold SQRT_AD_MINUS_ONE
  simp only [field.FieldElement2625.asNat_def]
  step*
  subst_vars
  simp only [Array.asNat2625_make]
  refine ⟨lt_p_iff.mpr (by decide), ?_, by decide⟩
  rw [← ZMod.val_natCast]
  refine congrArg ZMod.val ?_
  rw [a_def, neg_one_mul, ← neg_add', eq_neg_iff_add_eq_zero, d_eq_natCast]
  norm_cast
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero, mod_p_fold, mod_p_fold, mod_p_of_lt] <;>
    decide

/-- `SQRT_AD_MINUS_ONE` is RFC 9496's root `sqrtAdMinusOne` of `a d - 1` (not only a root). -/
theorem SQRT_AD_MINUS_ONE_spec_eq :
    SQRT_AD_MINUS_ONE ⦃ (r : FieldElement2625) =>
      r.asNat = curve25519.sqrtAdMinusOne ∧ r.LimbsLt 26 ⦄ := by
  unfold SQRT_AD_MINUS_ONE
  simp only [field.FieldElement2625.asNat_def]
  step*
  subst_vars
  simp only [Array.asNat2625_make]
  refine ⟨?_, by decide⟩
  rw [curve25519.sqrtAdMinusOne_def]
  decide

end Curve25519Dalek.backend.serial.u32.constants
