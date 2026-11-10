/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.Array
public import Aeneas.Data.BitVec
public import Aeneas.Std.Scalar.Notations
public section

/-! # Lemmas about little-endian byte lists and byte arrays -/

open Aeneas Aeneas.Std

/-- The little-endian bytes of a bit vector, read in radix `256`, give back its value. -/
theorem BitVec.ofDigits_toLEBytes {w : ℕ} (v : BitVec w) :
    Nat.ofDigits 256 (v.toLEBytes.map BitVec.toNat) = v.toNat := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rw [BitVec.toLEBytes]
    split_ifs with hw
    · have hv := v.isLt
      have hlt : v.toNat / 2 ^ 8 < 2 ^ (w - 8) := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
        exact lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega))
      simp only [List.map_cons, Nat.ofDigits_cons, ih (w - 8) (by omega), BitVec.toNat_setWidth,
        BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hlt]
      omega
    · have hw0 : w = 0 := by omega
      subst hw0
      simp [BitVec.toNat_of_zero_length]

/-- Copying a list `l` to the front of a zero list. -/
theorem List.setSlice!_replicate_zero {α : Type} (n : ℕ) (z : α) (l : List α)
    (hl : l.length ≤ n) :
    (List.replicate n z).setSlice! 0 l = l ++ List.replicate (n - l.length) z := by
  simp [List.setSlice!, Nat.min_eq_left hl, List.take_of_length_le]

/-- A byte shifted by fewer than 8 bytes fits in 64 bits. -/
theorem Nat.byte_mul_two_pow_lt {x k : ℕ} (hx : x < 2 ^ 8) (hk : k < 8) :
    x * 2 ^ (8 * k) < 2 ^ 64 :=
  calc x * 2 ^ (8 * k) < 2 ^ 8 * 2 ^ (8 * k) := Nat.mul_lt_mul_of_pos_right hx (by positivity)
    _ = 2 ^ (8 * (k + 1)) := by ring
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)

namespace Aeneas.Std.Array

/-- A byte array holding the little-endian bytes of `v` followed by zeros has value `v`. -/
theorem asNat_setSlice!_toLEBytes {n : Usize} (a : Array U8 n) {w : ℕ} (v : BitVec w)
    (hw : (w + 7) / 8 ≤ n.val)
    (h : a.val = (List.replicate n.val 0#u8).setSlice! 0 (v.toLEBytes.map UScalar.mk)) :
    a.asNat 8 = v.toNat := by
  rw [Array.asNat_def, h, List.setSlice!_replicate_zero _ _ _ (by simpa using hw)]
  have h0 : (0#u8).val = 0 := rfl
  simp only [List.map_append, List.map_replicate, h0, Nat.ofDigits_append_replicate_zero]
  rw [List.map_map]
  exact BitVec.ofDigits_toLEBytes v

end Aeneas.Std.Array
