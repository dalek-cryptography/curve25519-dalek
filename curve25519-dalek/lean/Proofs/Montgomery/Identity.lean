/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Montgomery
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
public section

/-! # `Identity for MontgomeryPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity

/-- Thirty-two zero bytes have value `0`. -/
private theorem asNat_repeat_zero : (Array.repeat 32#usize 0#u8).asNat 8 = 0 := by
  rw [Array.asNat_eq_sum]
  exact Finset.sum_eq_zero fun i hi => by
    rw [Array.getElem!_repeat 0#u8 (by simpa using Finset.mem_range.mp hi)]
    rfl

/-- `Identity for MontgomeryPoint`: thirty-two zero bytes, the encoding of `u = 0`. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : MontgomeryPoint) => r.asNat = 0 ⦄ := by
  unfold identity
  step*
  rw [MontgomeryPoint.asNat_def]
  exact asNat_repeat_zero

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity
