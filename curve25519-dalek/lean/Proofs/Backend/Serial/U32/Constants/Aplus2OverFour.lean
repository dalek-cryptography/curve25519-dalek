/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
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

namespace Curve25519Dalek.backend.serial.u32.constants

@[step]
theorem APLUS2_OVER_FOUR_spec :
    APLUS2_OVER_FOUR ⦃ (r : FieldElement2625) =>
      r.asNat * 4 = A + 2 ∧ r.LimbsLt 26 ⦄ := by
  unfold APLUS2_OVER_FOUR
  simp only [field.FieldElement2625.asNat_def]
  step*
  subst_vars
  simp only [Array.asNat2625_make]
  rw [curve25519.A_def]
  decide

end Curve25519Dalek.backend.serial.u32.constants
