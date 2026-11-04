/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.FromLimbs
import Proofs.Helpers.ZMod
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)
open curve25519 (p a d A)
open curve25519 (lt_p_iff mod_p_fold mod_p_of_lt d_eq_natCast)

namespace Curve25519Dalek.backend.serial.u64.constants

@[step]
theorem EDWARDS_D2_spec :
    EDWARDS_D2 ⦃ (r : FieldElement51) =>
      r.asNat = (2 * d).val ∧ r.LimbsLt 51 ⦄ := by
  unfold EDWARDS_D2
  simp only [field.FieldElement51.asNat_def, Array.asNat_def]
  step*
  subst_vars
  refine ⟨ZMod.eq_val_of_natCast_eq (lt_p_iff.mpr (by decide)) ?_, by decide⟩
  rw [d_eq_natCast, eq_comm]
  norm_cast
  apply ZMod.natCast_eq_natCast_of_mod_eq
  rw [mod_p_fold, mod_p_of_lt] <;> decide

end Curve25519Dalek.backend.serial.u64.constants
