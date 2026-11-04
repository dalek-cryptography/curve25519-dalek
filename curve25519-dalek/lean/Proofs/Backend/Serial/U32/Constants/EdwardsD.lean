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
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open curve25519 (p a d A)
open curve25519 (mod_p_of_lt d_eq_natCast)

namespace Curve25519Dalek.backend.serial.u32.constants

@[step]
theorem EDWARDS_D_spec :
    EDWARDS_D ⦃ (r : FieldElement2625) =>
      r.asNat = d.val ∧ r.LimbsLt 26 ⦄ := by
  unfold EDWARDS_D
  simp only [field.FieldElement2625.asNat_def]
  step*
  subst_vars
  simp only [Array.asNat2625_make]
  refine ⟨?_, by decide⟩
  rw [d_eq_natCast, ZMod.val_natCast, mod_p_of_lt] <;> decide

end Curve25519Dalek.backend.serial.u32.constants
