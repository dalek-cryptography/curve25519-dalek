/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar29
public import Curve25519.Basic
import Proofs.Backend.Serial.U32.Scalar.M
import Proofs.Helpers.AsNat
import Proofs.Helpers.Scalar29
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
public section

/-! # `Scalar29::square_internal`

Squares nine radix-`2^29` limbs into seventeen coefficients, doubling the cross products. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29)

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

@[step]
theorem square_internal_spec (a : Scalar29) (ha : a.LimbsLt 29) :
    square_internal a ⦃ (r : Array U64 17#usize) =>
      r.asNat 29 = a.asNat ^ 2 ∧ ∀ i : ℕ, i < 17 → r[i]!.val < 2 ^ 62 ⦄ := by
  have h_a := ha
  clear ha
  simp only [Scalar29.LimbsLt, Array.getElem!_Nat_eq] at h_a
  unfold square_internal
  -- Normalize the fixed array lookups before symbolic execution.
  simp only [Scalar29.index_eq, Nat.reduceLT, Array.index_usize, Array.getElem?_Usize_eq,
    Array.make, Array.from_val, UScalar.ofNatCore_val_eq, List.getElem?_cons_zero,
    List.getElem?_cons_succ]
  -- Each coefficient contains at most five products bounded by `2^30 * 2^29`.
  repeat' first
    | (step -threadGrindState -grind -assumTac with m_spec as ⟨product, h_product⟩
       have h_product_bound : product.val ≤ 2 ^ 30 * (2 ^ 29 - 1) := by
         rw [h_product]
         apply Nat.mul_le_mul
         · first | assumption | exact (h_a _ (by decide)).le.trans (by decide)
         · exact Nat.le_pred_of_lt (h_a _ (by decide)))
    | (step -threadGrindState -grind -assumTac with U64.add_spec
         as ⟨sum, h_sum⟩ by
         clear! a
         grind only [U64.max_eq])
    | (step -threadGrindState -assumTac with U32.mul_spec as ⟨doubled, h_doubled⟩
       have h_doubled_bound : doubled.val ≤ 2 ^ 30 := by grind only)
  constructor
  · rw [Array.asNat_eq_sum, Scalar29.asNat_def, Array.asNat_eq_sum]
    simp only [UScalar.ofNatCore_val_eq, pow_mul]
    generalize (2 ^ 29 : Nat) = B
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Array.getElem!_Nat_eq, Array.from_val, List.getElem!_cons_zero,
      List.getElem!_cons_succ]
    simp only [*]
    ring
  · intro j hj
    interval_cases j <;>
      simp only [Array.getElem!_Nat_eq, Array.from_val, List.getElem!_cons_zero,
        List.getElem!_cons_succ] <;> omega

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29
