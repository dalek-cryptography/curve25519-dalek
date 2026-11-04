/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Alessandro D'Angelo, Liao Zhang
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar52
public import Mathlib.Tactic.IntervalCases
import Proofs.Backend.Serial.U64.Scalar.Index
import Proofs.Backend.Serial.U64.Scalar.M
import Proofs.Helpers.AsNat
public import Curve25519.Basic
import Subtle
import Proofs.Helpers.StepSpecs
public import Mathlib.Tactic.Linarith
import Proofs.Helpers.Array
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

attribute [local step_post_simps] List.getElem!_cons_succ List.getElem!_cons_zero

open scoped Helpers.MakeStep

open scoped Helpers.MLtStep

private theorem square_coeffs_lt {a0 a1 a2 a3 a4 : ℕ} (ha0 : a0 < 2 ^ 52) (ha1 : a1 < 2 ^ 52)
    (ha2 : a2 < 2 ^ 52) (ha3 : a3 < 2 ^ 52) (ha4 : a4 < 2 ^ 52) :
    a0 * a0 < 2 ^ 107 ∧ a0 * 2 * a1 < 2 ^ 107 ∧ a0 * 2 * a2 + a1 * a1 < 2 ^ 107 ∧
    a0 * 2 * a3 + a1 * 2 * a2 < 2 ^ 107 ∧ a0 * 2 * a4 + a1 * 2 * a3 + a2 * a2 < 2 ^ 107 ∧
    a1 * 2 * a4 + a2 * 2 * a3 < 2 ^ 107 ∧ a2 * 2 * a4 + a3 * a3 < 2 ^ 107 ∧
    a3 * 2 * a4 < 2 ^ 107 ∧ a4 * a4 < 2 ^ 107 := by
  have h {x y : ℕ} (hx : x < 2 ^ 52) (hy : y < 2 ^ 52) : x * y < 2 ^ 104 :=
    (Nat.mul_lt_mul'' hx hy).trans_eq (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith [h ha0 ha0, h ha0 ha1, h ha0 ha2, h ha0 ha3, h ha0 ha4, h ha1 ha1, h ha1 ha2,
      h ha1 ha3, h ha1 ha4, h ha2 ha2, h ha2 ha3, h ha2 ha4, h ha3 ha3, h ha3 ha4, h ha4 ha4]

@[step]
theorem square_internal_spec (a : Scalar52) (ha : a.LimbsLt 52) :
    square_internal a ⦃ (r : Array U128 9#usize) =>
      r.asNat 52 = a.asNat ^ 2 ∧ ∀ i : ℕ, i < 9 → r[i]!.val < 2 ^ 107 ⦄ := by
  unfold square_internal
  obtain ⟨ha0, ha1, ha2, ha3, ha4⟩ := Nat.forall_lt_five.mp ha
  clear ha
  have hc := square_coeffs_lt ha0 ha1 ha2 ha3 ha4
  step*
  refine ⟨?_, fun k hk => ?_⟩
  · rw [Array.asNat_nine, Scalar52.asNat_def, Array.asNat_five]
    simp only [Array.getElem!_make, List.getElem!_cons_succ, List.getElem!_cons_zero, *]
    simp only [pow_mul']
    ring
  · interval_cases k <;>
      simp only [Array.getElem!_make, List.getElem!_cons_succ, List.getElem!_cons_zero, *]

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52
