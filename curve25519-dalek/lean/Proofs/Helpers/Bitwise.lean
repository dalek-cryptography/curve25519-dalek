/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Aeneas.Std.Scalar.Bitwise
import Aeneas.Tactic.Conv.Bvify.Bvify
import Aeneas.Tactic.Conv.Zify
import Aeneas.Tactic.Step.StepStar
import Mathlib.Tactic.LinearCombination
public section

/-! # Lemmas about bitwise operations

Masks, shifts and ors, on machine integers and on natural numbers.

`X / 2 ^ (64 * u) % 2 ^ 64` is limb `u` of `X`. The window of `w` bits of `X` at bit `64 * u + b` is
read from limb `u` alone when `b + w ≤ 64` (`Nat.window_in_limb`), and from limbs `u` and `u + 1`
otherwise (`Nat.window_across`). The other lemmas cut a number into bytes or limbs: a run of digits
is read with shifts, and two words are joined with a shift and an or. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Aeneas.Std

/-- Masking with `2 ^ n - 1` keeps the low `n` bits. Activated with
`open scoped Helpers.MaskStep` (see `Proofs.Helpers.StepSpecs`). -/
theorem UScalar.and_two_pow_sub_one_spec {ty : UScalarTy} (x m : UScalar ty) (n : ℕ)
    (hm : m.val = 2 ^ n - 1) :
    lift (x &&& m) ⦃ (r : UScalar ty) => r.val = x.val % 2 ^ n ⦄ := by
  step*
  simp only [*, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod]

/-- A power of two up to `2 ^ 64` divides the size of `U64`. -/
theorem U64.two_pow_dvd_size {n : ℕ} (hn : n ≤ 64) : 2 ^ n ∣ U64.size := by
  rw [show U64.size = 2 ^ 64 by simp [U64.size, U64.numBits]]
  exact Nat.pow_dvd_pow 2 hn

end Aeneas.Std

namespace Nat

/-- Or-ing in a value shifted above all bits of `acc` is addition. -/
theorem or_shiftLeft_eq_add_pow_mul {acc k : ℕ} (b : ℕ) (hacc : acc < 2 ^ k) :
    acc ||| b <<< k = acc + 2 ^ k * b := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hacc, Nat.shiftLeft_eq, Nat.mul_comm,
    Nat.add_comm]

/-- The bits of `x` from bit `a` on, when there are at most `n` of them. -/
theorem shiftRight_mod_eq_of_lt {x a n : ℕ} (hx : x < 2 ^ (a + n)) :
    x >>> a % 2 ^ n = x / 2 ^ a := by
  rw [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt]
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos a), ← Nat.pow_add, Nat.add_comm]
  exact hx

/-- The bits of `x` from bit `a` on, split at bit `a + n`. -/
theorem shiftRight_mod_add_mul_div (x a n : ℕ) :
    x >>> a % 2 ^ n + 2 ^ n * (x / 2 ^ (a + n)) = x / 2 ^ a := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.mod_add_div]

/-- The bits of `x` from bit `a` on (fewer than `b` of them) or-ed with `y` shifted up by `b`, cut
to `m + b` bits: the shifted `y` may first be reduced modulo any multiple `M` of `2 ^ (m + b)`. -/
theorem shiftRight_or_shiftLeft_mod {x a b m M : ℕ} (y : ℕ) (hx : x < 2 ^ (a + b))
    (hM : 2 ^ (m + b) ∣ M) :
    (x >>> a ||| y <<< b % M) % 2 ^ (m + b) = x / 2 ^ a + 2 ^ b * (y % 2 ^ m) := by
  have hlt : x / 2 ^ a < 2 ^ b := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos a), ← Nat.pow_add, Nat.add_comm]
    exact hx
  rw [Nat.or_mod_two_pow, Nat.mod_mod_of_dvd _ hM, ← Nat.or_mod_two_pow, Nat.mul_comm,
    ← Nat.shiftLeft_eq, Nat.add_comm (x / 2 ^ a), Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.or_comm]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftRight,
    Nat.testBit_shiftLeft, Nat.testBit_div_two_pow]
  by_cases hi : i < m + b
  · by_cases hb : b ≤ i
    · have hbm : i - b < m := by omega
      simp [hi, hb, hbm, Nat.add_comm a i]
    · simp [hi, hb, Nat.add_comm a i]
  · have hbm : ¬ i - b < m := by omega
    have hxa : x.testBit (a + i) = false :=
      Nat.testBit_lt_two_pow (hx.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hi, hbm, Nat.add_comm i a, hxa]

/-- `k` digits in radix `2 ^ w` of `x`, from bit `a` on, give the next `w * k` bits of `x`. -/
theorem sum_shiftRight_mod (x a w k : ℕ) :
    ∑ j ∈ Finset.range k, 2 ^ (w * j) * (x >>> (a + w * j) % 2 ^ w) = x >>> a % 2 ^ (w * k) := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Nat.pow_add, Nat.mod_mul, Nat.shiftRight_add,
      Nat.shiftRight_eq_div_pow (x >>> a)]

/-! ## Windows of bits of a number stored in 64-bit limbs -/

/-- A window of bits inside one limb. -/
theorem window_in_limb (X u b w : ℕ) (h : b + w ≤ 64) :
    X / 2 ^ (64 * u) % 2 ^ 64 / 2 ^ b % 2 ^ w = X / 2 ^ (64 * u + b) % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < w
  · have hib : i + b < 64 := by omega
    simp only [hi, hib, decide_true, Bool.true_and]
    congr 1
    omega
  · simp [hi]

/-- A window of bits across two limbs: the high bits of limb `u` or-ed with the low bits of limb
`u + 1` shifted up. -/
theorem window_across (X u b w : ℕ) (hb : b < 64) (hw : w ≤ 64) :
    (X / 2 ^ (64 * u) % 2 ^ 64 / 2 ^ b ||| X / 2 ^ (64 * (u + 1)) % 2 ^ 64 * 2 ^ (64 - b) % 2 ^ 64)
      % 2 ^ w = X / 2 ^ (64 * u + b) % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_or,
    Nat.testBit_mul_two_pow]
  by_cases hi : i < w
  · have hi64 : i < 64 := by omega
    simp only [hi, hi64, decide_true, Bool.true_and]
    by_cases hib : i + b < 64
    · have hnb : ¬ 64 - b ≤ i := by omega
      simp only [hib, hnb, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.or_false]
      congr 1
      omega
    · have hnb : 64 - b ≤ i := by omega
      have hlt : i - (64 - b) < 64 := by omega
      simp only [hib, hnb, hlt, decide_true, decide_false, Bool.true_and, Bool.false_and,
        Bool.false_or]
      congr 1
      omega
  · simp [hi]

/-- A window `Y % 2 ^ w` (plus a carry `c`) at bit `pos`, recoded as the digit `d` and the carry
`c'` into the next window. -/
theorem two_pow_mul_window_eq {Y c c' w pos : ℕ} {d : ℤ}
    (hd : d + 2 ^ w * c' = ((c + Y % 2 ^ w : ℕ) : ℤ)) :
    (2 : ℤ) ^ pos * (c + Y : ℕ) = 2 ^ pos * d + 2 ^ (pos + w) * (c' + Y / 2 ^ w : ℕ) := by
  have hY := Nat.mod_add_div Y (2 ^ w)
  zify at hY
  push_cast at hd ⊢
  rw [pow_add]
  linear_combination (-(2 : ℤ) ^ pos) * hd - (2 : ℤ) ^ pos * hY

end Nat
