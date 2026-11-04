/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.FromLimbs
public import Curve25519.Basic
import Proofs.Helpers.Radix
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)
open curve25519 (p a d A)
open curve25519 (sqrtM1 sqrtM1_eq_limbs)

namespace Curve25519Dalek.backend.serial.u64.constants

@[step]
theorem SQRT_M1_spec :
    SQRT_M1 ⦃ (r : FieldElement51) =>
      r.asNat = sqrtM1 ∧ r.LimbsLt 51 ⦄ := by
  unfold SQRT_M1
  simp only [field.FieldElement51.asNat_def, Array.asNat_def]
  step*
  subst_vars
  refine ⟨?_, by decide⟩
  rw [sqrtM1_eq_limbs]
  decide

end Curve25519Dalek.backend.serial.u64.constants
