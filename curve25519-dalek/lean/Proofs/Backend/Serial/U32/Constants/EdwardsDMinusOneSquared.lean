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
open curve25519 (lt_p_iff mod_p_fold mod_p_of_lt d_eq_natCast)

namespace Curve25519Dalek.backend.serial.u32.constants

@[step]
theorem EDWARDS_D_MINUS_ONE_SQUARED_spec :
    EDWARDS_D_MINUS_ONE_SQUARED ⦃ (r : FieldElement2625) =>
      r.asNat = ((d - 1) ^ 2).val ∧ r.LimbsLt 26 ⦄ := by
  unfold EDWARDS_D_MINUS_ONE_SQUARED
  simp only [field.FieldElement2625.asNat_def]
  step*
  subst_vars
  simp only [Array.asNat2625_make]
  refine ⟨ZMod.eq_val_of_natCast_eq (lt_p_iff.mpr (by decide)) ?_, by decide⟩
  rw [d_eq_natCast, ← Nat.cast_pred (by decide), eq_comm]
  norm_cast
  apply ZMod.natCast_eq_natCast_of_mod_eq
  rw [mod_p_fold, mod_p_fold, mod_p_of_lt] <;> decide

end Curve25519Dalek.backend.serial.u32.constants
