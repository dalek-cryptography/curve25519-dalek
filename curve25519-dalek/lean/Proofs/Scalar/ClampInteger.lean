/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar52
import Mathlib.Tactic.ReduceModChar
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar

/-- Clearing the low 3 bits of a byte. -/
private theorem and_248_add : ∀ x : ℕ, x < 2 ^ 8 → (x &&& 248) + x % 8 = x := by
  decide +kernel

/-- Clearing bit 7 and setting bit 6 of a byte. -/
private theorem and_127_or_64 : ∀ x : ℕ, x < 2 ^ 8 → (x &&& 127) ||| 64 = x % 64 + 64 := by
  decide +kernel

/-- The arithmetic of `clamp_integer`: the three byte updates, read on the value `X` of `bytes`
(low byte `x0`, top byte `x31`, other bytes `S`). -/
private theorem clamp_arith {X R A B S x0 x31 c0 c31 d31 : ℕ} (hx0 : x0 < 2 ^ 8)
    (hx31 : x31 < 2 ^ 8) (hc0 : c0 = x0 &&& 248) (hc31 : c31 = x31 &&& 127)
    (hd31 : d31 = c31 ||| 64) (hA : A + 2 ^ (8 * 0) * x0 = X + 2 ^ (8 * 0) * c0)
    (hB : B + 2 ^ (8 * 31) * x31 = A + 2 ^ (8 * 31) * c31)
    (hR : R + 2 ^ (8 * 31) * c31 = B + 2 ^ (8 * 31) * d31)
    (hX0 : X % 2 ^ (8 * 1) = 2 ^ (8 * 0) * x0) (hX : X = S + 2 ^ (8 * 31) * x31)
    (hS : S < 2 ^ (8 * 31)) :
    R + X % 8 = 2 ^ 254 + X % 2 ^ 254 := by
  have e0 := and_248_add x0 hx0
  have e31 := and_127_or_64 x31 hx31
  subst hc0 hc31 hd31
  norm_num at *
  omega

@[step]
theorem clamp_integer_spec (bytes : Array U8 32#usize) :
    clamp_integer bytes ⦃ (r : Array U8 32#usize) =>
      r.asNat 8 + bytes.asNat 8 % 8 = 2 ^ 254 + bytes.asNat 8 % 2 ^ 254 ⦄ := by
  unfold clamp_integer
  step with Array.index_usize_getElem!_spec as ⟨x0, hx0⟩
  step as ⟨c0, hc0, hc0bv⟩
  step as ⟨b1, hb1⟩
  step with Array.index_usize_getElem!_spec as ⟨x31, hx31⟩
  step as ⟨c31, hc31, hc31bv⟩
  step as ⟨b2, hb2⟩
  step with Array.index_usize_getElem!_spec as ⟨y31, hy31⟩
  step as ⟨d31, hd31, hd31bv⟩
  step as ⟨r, hr⟩
  have h31 : b1[31]! = bytes[31]! := by simp [hb1]
  have h31' : b2[31]! = c31 := by simp [hb2]
  have hA : b1.asNat 8 + 2 ^ (8 * 0) * bytes[0]!.val = bytes.asNat 8 + 2 ^ (8 * 0) * c0.val := by
    rw [hb1]
    exact Array.asNat_set_add 8 bytes 0#usize c0 (by simp)
  have hB : b2.asNat 8 + 2 ^ (8 * 31) * bytes[31]!.val
      = b1.asNat 8 + 2 ^ (8 * 31) * c31.val := by
    rw [hb2, ← h31]
    exact Array.asNat_set_add 8 b1 31#usize c31 (by simp)
  have hR : r.asNat 8 + 2 ^ (8 * 31) * c31.val = b2.asNat 8 + 2 ^ (8 * 31) * d31.val := by
    rw [hr, ← h31']
    exact Array.asNat_set_add 8 b2 31#usize d31 (by simp)
  have hX0 := Array.asNat_mod_pow_eq_sum 8 1 bytes (by simp) fun j _ => (bytes[j]!).hBounds
  rw [Finset.sum_range_one] at hX0
  have hS := Nat.sum_pow_mul_lt 8 31 (fun j => bytes[j]!.val) fun j _ => (bytes[j]!).hBounds
  have hX : bytes.asNat 8 = ∑ j ∈ Finset.range 31, 2 ^ (8 * j) * bytes[j]!.val
      + 2 ^ (8 * 31) * bytes[31]!.val := by
    rw [Array.asNat_eq_sum, show (32#usize).val = 31 + 1 from rfl, Finset.sum_range_succ]
  simp only [UScalar.val_and, UScalar.val_or] at hc0 hc31 hd31
  rw [hx0] at hc0
  rw [hx31, h31] at hc31
  rw [hy31, h31'] at hd31
  exact clamp_arith (bytes[0]!).hBounds (bytes[31]!).hBounds hc0 hc31 hd31 hA hB hR hX0 hX hS

end Curve25519Dalek.scalar
