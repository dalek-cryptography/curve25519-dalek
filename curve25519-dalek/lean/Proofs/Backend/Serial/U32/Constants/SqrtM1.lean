/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
import Proofs.Backend.Serial.U32.Field.FromLimbs
import Proofs.Helpers.FieldElement2625
public import Curve25519.Basic
import Proofs.Helpers.Radix
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open curve25519 (p a d A)
open curve25519 (sqrtM1 sqrtM1_eq_limbs)

namespace Curve25519Dalek.backend.serial.u32.constants

@[step]
theorem SQRT_M1_spec :
    SQRT_M1 ⦃ (r : FieldElement2625) =>
      r.asNat = sqrtM1 ∧ r.LimbsLt 26 ⦄ := by
  unfold SQRT_M1
  simp only [field.FieldElement2625.asNat_def]
  step*
  subst_vars
  simp only [Array.asNat2625_make]
  refine ⟨?_, by decide⟩
  rw [sqrtM1_eq_limbs]
  decide

end Curve25519Dalek.backend.serial.u32.constants
