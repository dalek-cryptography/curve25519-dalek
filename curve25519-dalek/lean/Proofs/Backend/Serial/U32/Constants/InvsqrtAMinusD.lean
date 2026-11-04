/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
import Proofs.Backend.Serial.U32.Field.FromLimbs
import Proofs.Helpers.FieldElement2625
import Proofs.Helpers.ZMod
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open curve25519 (p a d A)
open curve25519 (p_pos lt_p_iff mod_p_fold mod_p_of_lt a_def d_eq_natCast)

namespace Curve25519Dalek.backend.serial.u32.constants

@[step]
theorem INVSQRT_A_MINUS_D_spec :
    INVSQRT_A_MINUS_D ⦃ (r : FieldElement2625) =>
      r.asNat < p ∧
      r.asNat ^ 2 * (a - d).val % p = 1 ∧ r.LimbsLt 26 ⦄ := by
  unfold INVSQRT_A_MINUS_D
  simp only [field.FieldElement2625.asNat_def]
  step*
  subst_vars
  simp only [Array.asNat2625_make]
  have : NeZero p := ⟨p_pos.ne'⟩
  refine ⟨lt_p_iff.mpr (by decide), ?_, by decide⟩
  rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val, eq_comm]
  refine ZMod.eq_val_of_natCast_eq (lt_p_iff.mpr (by decide)) ?_
  rw [a_def, ← neg_add', mul_neg, Nat.cast_one, eq_neg_iff_add_eq_zero, d_eq_natCast]
  norm_cast
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero, mod_p_fold, mod_p_fold, mod_p_fold,
    mod_p_of_lt] <;> decide

end Curve25519Dalek.backend.serial.u32.constants
