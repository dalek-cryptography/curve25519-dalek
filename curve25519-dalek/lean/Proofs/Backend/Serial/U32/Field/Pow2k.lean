/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Proofs.Helpers.FieldElement2625
import Proofs.Backend.Serial.U32.Field.Square
public section

/-!
# Spec theorem for `pow2k`

`pow2k self k` computes `self ^ (2 ^ k)` for `k > 0` by repeated squaring: it squares `self` once
and then squares the result `k - 1` more times in a loop over the range `1..k`. Every squaring
returns a reduced field element, so every iteration meets the precondition of `square`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 320:4-327:5
-/

open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace Pow2k

/-- Loop invariant of `pow2k`, relative to the original input `x` and exponent `k`: the range ends
at `k`, its start `s` satisfies `1 ≤ s ≤ k`, the accumulator `z` is reduced (every limb below
`2 ^ 26`) and represents `x ^ (2 ^ s)` modulo `p`. -/
private def Invariant (x : FieldElement2625) (k : U32) (iter : core.ops.range.Range U32)
    (z : FieldElement2625) : Prop :=
  iter.end = k ∧
  1 ≤ iter.start.val ∧
  iter.start.val ≤ k.val ∧
  (∀ i : ℕ, i < 10 → z[i]!.val < 2 ^ 26) ∧
  z.asNat % p = x.asNat ^ (2 ^ iter.start.val) % p

end Pow2k


@[step]
private theorem pow2k_loop.body_spec (iter : core.ops.range.Range U32) (z : FieldElement2625)
    (x : FieldElement2625) (k : U32)
    (h_inv : Pow2k.Invariant x k iter z) :
    pow2k_loop.body iter z ⦃
      (result : ControlFlow (core.ops.range.Range U32 × FieldElement2625) FieldElement2625) =>
      match result with
      | .done z' =>
        iter.start.val = k.val ∧ z' = z ∧ Pow2k.Invariant x k iter z'
      | .cont (iter', z') =>
        Pow2k.Invariant x k iter' z' ∧ iter'.start.val = iter.start.val + 1 ⦄ := by
  rcases h_inv with ⟨h_end, h_start, h_le, h_red, h_val⟩
  unfold pow2k_loop.body
  step as ⟨o, iter', h_next, h_end'⟩
  by_cases hi : iter.start.val < iter.end.val
  · simp only [hi, ↓reduceIte] at h_next
    rcases h_next with ⟨h_o, h_adv⟩
    simp only [h_o]
    step with square_spec as ⟨z', h_val', h_red'⟩
    refine ⟨⟨h_end'.trans h_end, by omega, ?_, h_red', ?_⟩, h_adv⟩
    · rw [h_end] at hi
      omega
    · rw [h_val', Nat.pow_mod, h_val, ← Nat.pow_mod, ← pow_mul, h_adv, pow_succ]
  · simp only [hi, ↓reduceIte] at h_next
    rcases h_next with ⟨h_o, _⟩
    simp only [h_o, spec_ok]
    rw [h_end] at hi
    exact ⟨by omega, trivial, h_end, h_start, h_le, h_red, h_val⟩


@[step]
private theorem pow2k_loop_spec (iter : core.ops.range.Range U32) (z : FieldElement2625)
    (x : FieldElement2625) (k : U32)
    (h_inv : Pow2k.Invariant x k iter z) :
    pow2k_loop iter z ⦃ (result : FieldElement2625) =>
      (∀ i : ℕ, i < 10 → result[i]!.val < 2 ^ 26) ∧
      result.asNat % p = x.asNat ^ (2 ^ k.val) % p ⦄ := by
  unfold pow2k_loop
  refine loop.spec_decr_nat
    (fun state : core.ops.range.Range U32 × FieldElement2625 => k.val - state.1.start.val)
    (fun (iter, z) => Pow2k.Invariant x k iter z)
    _ _ _ ?_ h_inv
  rintro ⟨iter, z⟩ h_state
  apply spec_mono (pow2k_loop.body_spec iter z x k h_state)
  intro flow h_flow
  cases flow with
  | done result =>
    rcases h_flow with ⟨h_done, _, _, _, _, h_red, h_val⟩
    rw [h_done] at h_val
    exact ⟨h_red, h_val⟩
  | cont state =>
    rcases state with ⟨iter', z'⟩
    rcases h_flow with ⟨h_state', h_adv⟩
    have h_le := h_state'.2.2.1
    exact ⟨h_state', by dsimp only; omega⟩


@[step]
theorem pow2k_spec (self : FieldElement2625) (k : U32) (hk : 0 < k.val)
    (hself : self.LimbsLt 27) :
    pow2k self k ⦃ (r : FieldElement2625) =>
      r.asNat % p = self.asNat ^ 2 ^ k.val % p ∧ r.LimbsLt 26 ⦄ := by
  unfold pow2k
  step with massert_spec
  step as ⟨z, h_val, h_red⟩
  refine spec_mono (pow2k_loop_spec _ _ self k ⟨rfl, Nat.le_refl 1, hk, h_red, ?_⟩)
    fun r h => ⟨h.2, h.1⟩
  simpa only [UScalar.ofNatCore_val_eq, pow_one] using h_val


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625
