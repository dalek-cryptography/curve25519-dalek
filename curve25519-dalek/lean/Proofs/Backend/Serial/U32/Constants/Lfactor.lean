/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar29
public import Curve25519.Basic
import Proofs.Helpers.Scalar29
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29 montgomeryRadix)

namespace Curve25519Dalek.backend.serial.u32.constants

theorem LFACTOR_spec :
    LFACTOR.val < 2 ^ 29 ∧ (LFACTOR.val * curve25519.L + 1) % 2 ^ 29 = 0 := by
  unfold LFACTOR
  rw [Nat.add_mod, Nat.mul_mod, scalar.L_mod_two_pow_29]
  decide

end Curve25519Dalek.backend.serial.u32.constants
