/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Helpers.AsNat
import Proofs.Helpers.Limbs
public import Curve25519.Basic
import Subtle
import Proofs.Helpers.StepSpecs
import Mathlib.Tactic.ReduceModChar
import Proofs.Helpers.Array
import Proofs.Helpers.Bitwise
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Aeneas.Std.Array

/-- The `w` bytes of `a` from offset `o` form bytes `o, …, o + w - 1` of `a.asNat 8`. -/
private theorem sum_window_eq {n : Usize} (a : Array U8 n) (o w : ℕ) (h : o + w ≤ n.val) :
    ∑ j ∈ Finset.range w, 2 ^ (8 * j) * a[o + j]!.val
      = a.asNat 8 / 2 ^ (8 * o) % 2 ^ (8 * w) := by
  have hbyte : ∀ k : ℕ, a[k]!.val < 2 ^ 8 := fun k => by scalar_tac
  set M := ∑ j ∈ Finset.range w, 2 ^ (8 * j) * a[o + j]!.val
  set U := ∑ j ∈ Finset.range (n.val - (o + w)), 2 ^ (8 * j) * a[o + w + j]!.val
  have hL := Nat.sum_pow_mul_lt 8 o (fun k => a[k]!.val) fun k _ => hbyte k
  have hM : M < 2 ^ (8 * w) := Nat.sum_pow_mul_lt 8 w (fun j => a[o + j]!.val) fun j _ => hbyte _
  have hsplit : a.asNat 8 = ∑ k ∈ Finset.range o, 2 ^ (8 * k) * a[k]!.val
      + 2 ^ (8 * o) * (M + 2 ^ (8 * w) * U) := by
    rw [Array.asNat_eq_sum, show n.val = o + w + (n.val - (o + w)) by agrind,
      Finset.sum_range_add, Finset.sum_range_add]
    simp only [M, U, Finset.mul_sum, Nat.mul_add, Nat.pow_add, Nat.add_assoc]
    ring_nf
  rw [hsplit, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hL, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hM]

/-- A 51-bit limb read from 8 bytes at offset `o`, shifted right by `s`, is bits
`8 o + s, …, 8 o + s + 50` of `a.asNat 8`. -/
private theorem limb_of_window {n : Usize} (a : Array U8 n) (o s : ℕ) (h : o + 8 ≤ n.val)
    (hs : s + 51 ≤ 64) :
    (∑ j ∈ Finset.range 8, 2 ^ (8 * j) * a[o + j]!.val) / 2 ^ s % 2 ^ 51
      = a.asNat 8 / 2 ^ (8 * o + s) % 2 ^ 51 := by
  rw [sum_window_eq a o 8 h, show 8 * 8 = s + (64 - s) by agrind, Nat.pow_add,
    Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by agrind))]

/-- The low 51 bits of 8 bytes at offset `o` are bits `8 o, …, 8 o + 50` of `a.asNat 8`. -/
private theorem limb_of_window_zero {n : Usize} (a : Array U8 n) (o : ℕ) (h : o + 8 ≤ n.val) :
    (∑ j ∈ Finset.range 8, 2 ^ (8 * j) * a[o + j]!.val) % 2 ^ 51
      = a.asNat 8 / 2 ^ (8 * o) % 2 ^ 51 := by
  simpa using limb_of_window a o 0 h (by agrind)

private theorem getElem!_to_slice {α : Type} [Inhabited α] {n : Usize} (a : Array α n) (i : ℕ) :
    a.to_slice[i]! = a[i]! := by
  simp [Slice.getElem!_Nat_eq, Array.getElem!_Nat_eq, Array.val_to_slice]

end Aeneas.Std.Array

/-- Five 51-bit limbs of `x` reassemble `x % 2 ^ 255`. -/
private theorem Nat.limbs51_eq_mod (x : ℕ) :
    x % 2 ^ 51 + 2 ^ 51 * (x / 2 ^ 51 % 2 ^ 51) + 2 ^ 102 * (x / 2 ^ 102 % 2 ^ 51)
      + 2 ^ 153 * (x / 2 ^ 153 % 2 ^ 51) + 2 ^ 204 * (x / 2 ^ 204 % 2 ^ 51) = x % 2 ^ 255 := by
  rw [show 2 ^ 255 = 2 ^ 204 * 2 ^ 51 by norm_num, Nat.mod_mul,
    show 2 ^ 204 = 2 ^ 153 * 2 ^ 51 by norm_num, Nat.mod_mul,
    show 2 ^ 153 = 2 ^ 102 * 2 ^ 51 by norm_num, Nat.mod_mul,
    show 2 ^ 102 = 2 ^ 51 * 2 ^ 51 by norm_num, Nat.mod_mul]

/-- Or-ing a byte shifted to bit `s` of a 64-bit word above an accumulator below `2 ^ s` adds
it. -/
private theorem Nat.or_byte_shiftLeft_eq_add {acc b s : ℕ} (hacc : acc < 2 ^ s) (hb : b < 2 ^ 8)
    (hs : s + 8 ≤ 64) : acc ||| (b % 2 ^ 64) <<< s % U64.size = acc + 2 ^ s * b := by
  have hb' : b * 2 ^ s < 2 ^ 64 :=
    calc b * 2 ^ s < 2 ^ 8 * 2 ^ s := Nat.mul_lt_mul_of_pos_right hb (by positivity)
      _ = 2 ^ (s + 8) := by rw [← Nat.pow_add, Nat.add_comm]
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hs
  rw [Nat.mod_eq_of_lt (hb.trans (by norm_num)), U64.size_eq, Nat.mod_eq_of_lt (by
    rw [Nat.shiftLeft_eq]; exact hb'), Nat.or_shiftLeft_eq_add_pow_mul _ hacc]

/-- Eight bytes or-ed into a 64-bit word at bits `0, 8, …, 56`. -/
private theorem Nat.or_bytes_eq {b0 b1 b2 b3 b4 b5 b6 b7 : ℕ} (h0 : b0 < 2 ^ 8) (h1 : b1 < 2 ^ 8)
    (h2 : b2 < 2 ^ 8) (h3 : b3 < 2 ^ 8) (h4 : b4 < 2 ^ 8) (h5 : b5 < 2 ^ 8) (h6 : b6 < 2 ^ 8)
    (h7 : b7 < 2 ^ 8) :
    b0 % 2 ^ 64 ||| (b1 % 2 ^ 64) <<< 8 % U64.size ||| (b2 % 2 ^ 64) <<< 16 % U64.size |||
      (b3 % 2 ^ 64) <<< 24 % U64.size ||| (b4 % 2 ^ 64) <<< 32 % U64.size |||
      (b5 % 2 ^ 64) <<< 40 % U64.size ||| (b6 % 2 ^ 64) <<< 48 % U64.size |||
      (b7 % 2 ^ 64) <<< 56 % U64.size
      = b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3 + 2 ^ 32 * b4 + 2 ^ 40 * b5 + 2 ^ 48 * b6
        + 2 ^ 56 * b7 := by
  rw [Nat.mod_eq_of_lt (h0.trans (by norm_num)), Nat.or_byte_shiftLeft_eq_add h0 h1 (by norm_num),
    Nat.or_byte_shiftLeft_eq_add (by omega) h2 (by norm_num),
    Nat.or_byte_shiftLeft_eq_add (by omega) h3 (by norm_num),
    Nat.or_byte_shiftLeft_eq_add (by omega) h4 (by norm_num),
    Nat.or_byte_shiftLeft_eq_add (by omega) h5 (by norm_num),
    Nat.or_byte_shiftLeft_eq_add (by omega) h6 (by norm_num),
    Nat.or_byte_shiftLeft_eq_add (by omega) h7 (by norm_num)]

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.from_bytes

open scoped Helpers.IndexStep Helpers.UpdateStep

@[step]
theorem load8_at_spec (input : Slice U8) (i : Usize) (hi : i.val + 8 ≤ input.length) :
    load8_at input i ⦃ (r : U64) =>
      r.val = ∑ j ∈ Finset.range 8, 2 ^ (8 * j) * input[i.val + j]!.val ⦄ := by
  unfold load8_at
  step*
  simp only [*, UScalar.val_or, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.add_zero]
  rw [Nat.or_bytes_eq (UScalar.hBounds _) (UScalar.hBounds _) (UScalar.hBounds _)
    (UScalar.hBounds _) (UScalar.hBounds _) (UScalar.hBounds _) (UScalar.hBounds _)
    (UScalar.hBounds _)]
  ring
end Curve25519Dalek.backend.serial.u64.field.FieldElement51.from_bytes

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

open scoped Helpers.MaskStep

@[step]
theorem from_bytes_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (r : FieldElement51) =>
      r.asNat = bytes.asNat 8 % 2 ^ 255 ∧ r.LimbsLt 51 ⦄ := by
  unfold from_bytes
  step as ⟨two_pow_51, h_two_pow_51⟩
  step as ⟨mask, h_mask⟩
  have h_mask' : mask.val = 2 ^ 51 - 1 := by scalar_tac
  step*
  unfold FieldElement51.LimbsLt
  rw [FieldElement51.asNat_eq, Nat.forall_lt_five]
  simp only [Array.getElem!_Nat_eq, Array.make_val, List.getElem!_cons_zero,
    List.getElem!_cons_succ]
  simp only [*, Nat.shiftRight_eq_div_pow, Array.getElem!_to_slice]
  rw [Array.limb_of_window_zero bytes 0 (by simp),
    Array.limb_of_window bytes 6 3 (by simp) (by norm_num),
    Array.limb_of_window bytes 12 6 (by simp) (by norm_num),
    Array.limb_of_window bytes 19 1 (by simp) (by norm_num),
    Array.limb_of_window bytes 24 12 (by simp) (by norm_num)]
  simp only [Nat.reduceMul, Nat.reduceAdd, pow_zero, Nat.div_one]
  exact ⟨Nat.limbs51_eq_mod _, Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity),
    Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity)⟩
end Curve25519Dalek.backend.serial.u64.field.FieldElement51
