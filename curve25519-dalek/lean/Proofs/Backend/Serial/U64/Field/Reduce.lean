/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
public import Curve25519.Basic
public import Mathlib.Tactic.LinearCombination
import Proofs.Helpers.Limbs
import Subtle
import Proofs.Helpers.AsNat
import Proofs.Helpers.StepSpecs
import Aeneas.Tactic.Solver.ScalarTac.Init
import Proofs.Helpers.Array
import Proofs.Helpers.Bitwise
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

open scoped Helpers.IndexStep Helpers.UpdateStep Helpers.MaskStep
attribute [local scalar_tac_simps] Nat.shiftRight_eq_div_pow

@[local step]
private theorem reduce.LOW_51_BIT_MASK_spec :
    reduce.LOW_51_BIT_MASK ⦃ (r : U64) => r.val = 2 ^ 51 - 1 ⦄ := by
  unfold reduce.LOW_51_BIT_MASK
  step*

/-- The carry propagation of `reduce`, exactly: the top carry `a₄ / 2^51` re-enters the bottom limb
multiplied by `19 = 2^255 - p`, so `p` is subtracted `a₄ / 2^51` times. -/
private theorem reduce_asNat_add (a₀ a₁ a₂ a₃ a₄ : ℕ) :
    (a₀ % 2 ^ 51 + 19 * (a₄ / 2 ^ 51) + 2 ^ 51 * (a₁ % 2 ^ 51 + a₀ / 2 ^ 51)
      + 2 ^ 102 * (a₂ % 2 ^ 51 + a₁ / 2 ^ 51) + 2 ^ 153 * (a₃ % 2 ^ 51 + a₂ / 2 ^ 51)
      + 2 ^ 204 * (a₄ % 2 ^ 51 + a₃ / 2 ^ 51)) + p * (a₄ / 2 ^ 51)
      = a₀ + 2 ^ 51 * a₁ + 2 ^ 102 * a₂ + 2 ^ 153 * a₃ + 2 ^ 204 * a₄ := by
  have h₀ := Nat.div_add_mod a₀ (2 ^ 51)
  have h₁ := Nat.div_add_mod a₁ (2 ^ 51)
  have h₂ := Nat.div_add_mod a₂ (2 ^ 51)
  have h₃ := Nat.div_add_mod a₃ (2 ^ 51)
  have h₄ := Nat.div_add_mod a₄ (2 ^ 51)
  have hp := p_add_nineteen
  zify at *
  linear_combination h₀ + 2 ^ 51 * h₁ + 2 ^ 102 * h₂ + 2 ^ 153 * h₃ + 2 ^ 204 * h₄
    + (a₄ / 2 ^ 51 : ℤ) * hp

/-- Five limbs below `2^51 + 2^18` represent a number below `2 p`. -/
private theorem asNat_lt_two_mul_p {r₀ r₁ r₂ r₃ r₄ : ℕ} (h₀ : r₀ < 2 ^ 51 + 2 ^ 18)
    (h₁ : r₁ < 2 ^ 51 + 2 ^ 18) (h₂ : r₂ < 2 ^ 51 + 2 ^ 18) (h₃ : r₃ < 2 ^ 51 + 2 ^ 18)
    (h₄ : r₄ < 2 ^ 51 + 2 ^ 18) :
    r₀ + 2 ^ 51 * r₁ + 2 ^ 102 * r₂ + 2 ^ 153 * r₃ + 2 ^ 204 * r₄ < 2 * p := by
  have hp := p_add_nineteen
  omega

set_option linter.hashCommand false in
#decompose reduce reduce_eq
  letRange 10 15 => reduce.mask
  letRange 11 16 => reduce.carry

attribute [nolint docBlame] reduce.mask reduce.carry

/-- First phase of `reduce`: every limb is masked to its low 51 bits. -/
@[local step]
private theorem reduce.mask_spec (limbs : Array U64 5#usize) (i : U64) (hi : i = limbs[0]!) :
    reduce.mask limbs i ⦃ (r : Array U64 5#usize) =>
      r[0]!.val = limbs[0]!.val % 2 ^ 51 ∧ r[1]!.val = limbs[1]!.val % 2 ^ 51 ∧
      r[2]!.val = limbs[2]!.val % 2 ^ 51 ∧ r[3]!.val = limbs[3]!.val % 2 ^ 51 ∧
      r[4]!.val = limbs[4]!.val % 2 ^ 51 ⦄ := by
  unfold reduce.mask
  step*
  simp_lists [*]

/-- Second phase of `reduce`: each carry is added to the next limb, the top one times 19. -/
@[local step]
private theorem reduce.carry_spec (c0 c1 c2 c3 c4 : U64) (limbs5 : Array U64 5#usize)
    (h0 : limbs5[0]!.val < 2 ^ 51) (h1 : limbs5[1]!.val < 2 ^ 51) (h2 : limbs5[2]!.val < 2 ^ 51)
    (h3 : limbs5[3]!.val < 2 ^ 51) (h4 : limbs5[4]!.val < 2 ^ 51) (hc0 : c0.val < 2 ^ 13)
    (hc1 : c1.val < 2 ^ 13) (hc2 : c2.val < 2 ^ 13) (hc3 : c3.val < 2 ^ 13)
    (hc4 : c4.val < 2 ^ 13) :
    reduce.carry c0 c1 c2 c3 c4 limbs5 ⦃ (r : Array U64 5#usize) =>
      r[0]!.val = limbs5[0]!.val + 19 * c4.val ∧ r[1]!.val = limbs5[1]!.val + c0.val ∧
      r[2]!.val = limbs5[2]!.val + c1.val ∧ r[3]!.val = limbs5[3]!.val + c2.val ∧
      r[4]!.val = limbs5[4]!.val + c3.val ⦄ := by
  unfold reduce.carry
  step*
  agrind

/-- `reduce` exactly: `p` is subtracted `limbs[4] / 2^51` times, and the limbs are below
`2^51 + 2^18`. `reduce_spec` follows from this. -/
private theorem reduce_exact_spec (limbs : Array U64 5#usize) :
    reduce limbs ⦃ (r : FieldElement51) =>
      r.asNat + p * (limbs[4]!.val / 2 ^ 51) = FieldElement51.asNat limbs ∧
      ∀ i : ℕ, i < 5 → r[i]!.val < 2 ^ 51 + 2 ^ 18 ⦄ := by
  rw [reduce_eq]
  step*
  rw [FieldElement51.asNat_eq, FieldElement51.asNat_eq, Nat.forall_lt_five]
  simp only [*, Nat.shiftRight_eq_div_pow]
  refine ⟨reduce_asNat_add _ _ _ _ _, ?_, ?_, ?_, ?_, ?_⟩ <;> scalar_tac

@[step]
theorem reduce_spec (limbs : Array U64 5#usize) :
    reduce limbs ⦃ (r : FieldElement51) =>
      r.asNat % p = FieldElement51.asNat limbs % p ∧ r.LimbsLt 52 ∧
      r.asNat < 2 * p ⦄ := by
  step with reduce_exact_spec
  refine ⟨by grind [Nat.add_mul_mod_self_left], by grind, ?_⟩
  rw [asNat_eq]
  apply asNat_lt_two_mul_p <;> grind

end Curve25519Dalek.backend.serial.u64.field.FieldElement51
