/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Liao Zhang
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
import Proofs.Helpers.Array
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

open scoped Helpers.IndexStep Helpers.UpdateStep

open scoped Helpers.MLtStep

private theorem mul_coeffs_lt {a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ} (ha0 : a0 < 2 ^ 52)
    (ha1 : a1 < 2 ^ 52) (ha2 : a2 < 2 ^ 52) (ha3 : a3 < 2 ^ 52) (ha4 : a4 < 2 ^ 52)
    (hb0 : b0 < 2 ^ 52) (hb1 : b1 < 2 ^ 52) (hb2 : b2 < 2 ^ 52) (hb3 : b3 < 2 ^ 52)
    (hb4 : b4 < 2 ^ 52) :
    a0 * b0 < 2 ^ 107 ∧ a0 * b1 + a1 * b0 < 2 ^ 107 ∧
    a0 * b2 + a1 * b1 + a2 * b0 < 2 ^ 107 ∧
    a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 < 2 ^ 107 ∧
    a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0 < 2 ^ 107 ∧
    a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1 < 2 ^ 107 ∧
    a2 * b4 + a3 * b3 + a4 * b2 < 2 ^ 107 ∧ a3 * b4 + a4 * b3 < 2 ^ 107 ∧
    a4 * b4 < 2 ^ 107 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> scalar_tac +nonLin

@[step]
theorem mul_internal_spec (a b : Scalar52) (ha : a.LimbsLt 52)
    (hb : b.LimbsLt 52) :
    mul_internal a b ⦃ (r : Array U128 9#usize) =>
      r.asNat 52 = a.asNat * b.asNat ∧ ∀ i : ℕ, i < 9 → r[i]!.val < 2 ^ 107 ⦄ := by
  unfold mul_internal
  obtain ⟨ha0, ha1, ha2, ha3, ha4⟩ := Nat.forall_lt_five.mp ha
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := Nat.forall_lt_five.mp hb
  clear ha hb
  have hc := mul_coeffs_lt ha0 ha1 ha2 ha3 ha4 hb0 hb1 hb2 hb3 hb4
  step*
  refine ⟨?_, fun k hk => ?_⟩
  · rw [Array.asNat_nine, Scalar52.asNat_def, Scalar52.asNat_def, Array.asNat_five,
      Array.asNat_five]
    simp (disch := decide) only [*]
    simp only [pow_mul']
    ring
  · interval_cases k <;> simp (disch := decide) only [*]

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52
