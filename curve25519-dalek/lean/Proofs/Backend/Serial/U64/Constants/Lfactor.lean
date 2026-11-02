/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Basic
import Proofs.Helpers.Radix
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)
open curve25519 (p a d A)
open curve25519 (L_mod_two_pow_52)

namespace Curve25519Dalek.backend.serial.u64.constants

theorem LFACTOR_spec :
    LFACTOR.val < 2 ^ 52 ∧ (LFACTOR.val * curve25519.L + 1) % 2 ^ 52 = 0 := by
  unfold LFACTOR
  rw [Nat.add_mod, Nat.mul_mod, L_mod_two_pow_52]
  decide

end Curve25519Dalek.backend.serial.u64.constants
