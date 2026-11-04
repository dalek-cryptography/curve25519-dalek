/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Lim Jin Xing, Oliver Butterley
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar52
public import Defs.FieldElement51
public import Defs.Scalar
import Proofs.Helpers.Montgomery
import Mathlib.Tactic.LinearCombination
import Proofs.Helpers.Limbs
import Proofs.Helpers.Array
import Proofs.Helpers.Bitwise
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- Bytes 0–6 (and 13–19): a limb and the low 4 bits of the next one. -/
private theorem to_bytes.bytes_low (l0 l1 : U64) (h0 : l0.val < 2 ^ 52) :
    l0.val >>> 0 % 2 ^ 8 + 2 ^ 8 * (l0.val >>> 8 % 2 ^ 8) + 2 ^ 16 * (l0.val >>> 16 % 2 ^ 8)
      + 2 ^ 24 * (l0.val >>> 24 % 2 ^ 8) + 2 ^ 32 * (l0.val >>> 32 % 2 ^ 8)
      + 2 ^ 40 * (l0.val >>> 40 % 2 ^ 8)
      + 2 ^ 48 * ((l0.val >>> 48 ||| l1.val <<< 4 % U64.size) % 2 ^ 8)
      = l0.val + 2 ^ 52 * (l1.val % 2 ^ 4) := by
  have hs := Nat.sum_shiftRight_mod l0.val 0 8 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.pow_zero,
    Nat.one_mul, Nat.zero_add] at hs
  rw [hs, Nat.shiftRight_or_shiftLeft_mod _ ?_ (U64.two_pow_dvd_size ?_), Nat.shiftRight_zero,
    Nat.mul_add, ← Nat.add_assoc, Nat.mod_add_div]
  · ring
  · exact h0
  · norm_num

/-- Bytes 7–12 (and 20–25): a limb without its low 4 bits. -/
private theorem to_bytes.bytes_high (l1 : U64) (h1 : l1.val < 2 ^ 52) :
    l1.val >>> 4 % 2 ^ 8 + 2 ^ 8 * (l1.val >>> 12 % 2 ^ 8) + 2 ^ 16 * (l1.val >>> 20 % 2 ^ 8)
      + 2 ^ 24 * (l1.val >>> 28 % 2 ^ 8) + 2 ^ 32 * (l1.val >>> 36 % 2 ^ 8)
      + 2 ^ 40 * (l1.val >>> 44 % 2 ^ 8)
      = l1.val / 2 ^ 4 := by
  have hs := Nat.sum_shiftRight_mod l1.val 4 8 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd,
    Nat.pow_zero, Nat.one_mul, Nat.zero_add] at hs
  rw [hs]
  exact Nat.shiftRight_mod_eq_of_lt h1

/-- Bytes 26–31: the top limb, which has at most 48 bits. -/
private theorem to_bytes.bytes_top (l4 : U64) (h4 : l4.val < 2 ^ 48) :
    l4.val >>> 0 % 2 ^ 8 + 2 ^ 8 * (l4.val >>> 8 % 2 ^ 8) + 2 ^ 16 * (l4.val >>> 16 % 2 ^ 8)
      + 2 ^ 24 * (l4.val >>> 24 % 2 ^ 8) + 2 ^ 32 * (l4.val >>> 32 % 2 ^ 8)
      + 2 ^ 40 * (l4.val >>> 40 % 2 ^ 8)
      = l4.val := by
  have hs := Nat.sum_shiftRight_mod l4.val 0 8 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.pow_zero,
    Nat.one_mul, Nat.zero_add] at hs
  rw [hs, Nat.shiftRight_zero, Nat.mod_eq_of_lt h4]

/-- A top limb of weight `2 ^ 208` in a number below `2 ^ 256` has at most 48 bits. -/
private theorem top_limb_lt {r x : ℕ} (h : r + 2 ^ 208 * x < 2 ^ 256) : x < 2 ^ 48 := by
  omega

/-- The 32 bytes written by `to_bytes` spell out the five 52-bit limbs. -/
private theorem to_bytes.bytes_eq (l0 l1 l2 l3 l4 : U64) (h0 : l0.val < 2 ^ 52)
    (h1 : l1.val < 2 ^ 52) (h2 : l2.val < 2 ^ 52) (h3 : l3.val < 2 ^ 52) (h4 : l4.val < 2 ^ 48) :
    l0.val >>> 0 % 2 ^ 8 + 2 ^ 8 * (l0.val >>> 8 % 2 ^ 8 + 2 ^ 8 * (l0.val >>> 16 % 2 ^ 8
      + 2 ^ 8 * (l0.val >>> 24 % 2 ^ 8 + 2 ^ 8 * (l0.val >>> 32 % 2 ^ 8
      + 2 ^ 8 * (l0.val >>> 40 % 2 ^ 8
      + 2 ^ 8 * ((l0.val >>> 48 ||| l1.val <<< 4 % U64.size) % 2 ^ 8 + 2 ^ 8 * (l1.val >>> 4 % 2 ^ 8
      + 2 ^ 8 * (l1.val >>> 12 % 2 ^ 8 + 2 ^ 8 * (l1.val >>> 20 % 2 ^ 8
      + 2 ^ 8 * (l1.val >>> 28 % 2 ^ 8 + 2 ^ 8 * (l1.val >>> 36 % 2 ^ 8
      + 2 ^ 8 * (l1.val >>> 44 % 2 ^ 8 + 2 ^ 8 * (l2.val >>> 0 % 2 ^ 8
      + 2 ^ 8 * (l2.val >>> 8 % 2 ^ 8 + 2 ^ 8 * (l2.val >>> 16 % 2 ^ 8
      + 2 ^ 8 * (l2.val >>> 24 % 2 ^ 8 + 2 ^ 8 * (l2.val >>> 32 % 2 ^ 8
      + 2 ^ 8 * (l2.val >>> 40 % 2 ^ 8
      + 2 ^ 8 * ((l2.val >>> 48 ||| l3.val <<< 4 % U64.size) % 2 ^ 8 + 2 ^ 8 * (l3.val >>> 4 % 2 ^ 8
      + 2 ^ 8 * (l3.val >>> 12 % 2 ^ 8 + 2 ^ 8 * (l3.val >>> 20 % 2 ^ 8
      + 2 ^ 8 * (l3.val >>> 28 % 2 ^ 8 + 2 ^ 8 * (l3.val >>> 36 % 2 ^ 8
      + 2 ^ 8 * (l3.val >>> 44 % 2 ^ 8 + 2 ^ 8 * (l4.val >>> 0 % 2 ^ 8
      + 2 ^ 8 * (l4.val >>> 8 % 2 ^ 8 + 2 ^ 8 * (l4.val >>> 16 % 2 ^ 8
      + 2 ^ 8 * (l4.val >>> 24 % 2 ^ 8 + 2 ^ 8 * (l4.val >>> 32 % 2 ^ 8
      + 2 ^ 8 * (l4.val >>> 40 % 2 ^ 8)))))))))))))))))))))))))))))))
      = l0.val + 2 ^ 52 * l1.val + 2 ^ 104 * l2.val + 2 ^ 156 * l3.val + 2 ^ 208 * l4.val := by
  have g0 := to_bytes.bytes_low l0 l1 h0
  have g1 := to_bytes.bytes_high l1 h1
  have g2 := to_bytes.bytes_low l2 l3 h2
  have g3 := to_bytes.bytes_high l3 h3
  have g4 := to_bytes.bytes_top l4 h4
  have d1 := Nat.div_add_mod l1.val (2 ^ 4)
  have d3 := Nat.div_add_mod l3.val (2 ^ 4)
  zify at g0 g1 g2 g3 g4 d1 d3 ⊢
  linear_combination g0 + 2 ^ 56 * g1 + 2 ^ 104 * g2 + 2 ^ 160 * g3 + 2 ^ 208 * g4
    + 2 ^ 52 * d1 + 2 ^ 156 * d3

@[step]
theorem to_bytes_spec (self : Scalar52) (hself : self.LimbsLt 52)
    (hself' : self.asNat < 2 ^ 256) :
    to_bytes self ⦃ (r : Array U8 32#usize) =>
      r.asNat 8 = self.asNat ⦄ := by
  rw [Scalar52.asNat_eq] at hself'
  have h4 := top_limb_lt hself'
  unfold Scalar52.LimbsLt at hself
  rw [Nat.forall_lt_five] at hself
  simp (disch := simp) only [Array.getElem!_Nat_eq, getElem!_pos] at hself h4
  obtain ⟨h0, h1, h2, h3, -⟩ := hself
  unfold to_bytes
  step*
  subst_vars
  rw [Scalar52.asNat_eq]
  simp (disch := simp) only [Array.getElem!_Nat_eq, getElem!_pos]
  simp only [Array.asNat_def, Array.set_val_eq, Array.repeat_val, UScalar.ofNatCore_val_eq,
    List.replicate_succ, List.replicate_zero, List.set_cons_zero, List.set_cons_succ,
    List.map_cons, List.map_nil, Nat.ofDigits_cons, Nat.ofDigits_nil]
  simp only [*, UScalar.cast_val_eq, UScalar.val_or, UScalarTy.U8_numBits_eq]
  exact to_bytes.bytes_eq _ _ _ _ _ h0 h1 h2 h3 h4

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52
