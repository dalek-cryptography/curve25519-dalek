/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Aeneas.Std.Scalar.Notations
public import Curve25519.Edwards.Basic
public import Defs.Array
import Proofs.Helpers.AsInt
public section

/-! # The value of the top digits of a signed-digit recoding

The scalar multiplications run Horner's rule over the signed digits of a scalar from the top
down: the `256` digits of a non-adjacent form (`non_adjacent_form`) in base `2`, or the `64`
digits of `as_radix_16` in base `16`. After the digits `d[e], …` the accumulator represents
`nafTail d e • P` (resp. `radix16Tail d e • P`). Also the sum of a `zipWith` as a sum over
indices, for the multiscalar multiplications. -/

open Aeneas Aeneas.Std

namespace Curve25519Dalek

/-- The value `∑_{k < 256 - e} 2^k d[e + k]` of the digits `d[e], …, d[255]`. -/
def nafTail (d : Array I8 256#usize) (e : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (256 - e), 2 ^ k * d[e + k]!.val

theorem nafTail_eq (d : Array I8 256#usize) (e : ℕ) (he : e < 256) :
    nafTail d e = d[e]!.val + 2 * nafTail d (e + 1) := by
  unfold nafTail
  rw [show 256 - e = 256 - (e + 1) + 1 by omega, Finset.sum_range_succ', Finset.mul_sum,
    pow_zero, one_mul, add_zero, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_succ, show e + (k + 1) = e + 1 + k by omega]
  ring

/-- All digits are summed from `e = 0`: the value `asInt 1` of the digits. -/
theorem nafTail_zero (d : Array I8 256#usize) : nafTail d 0 = d.asInt 1 := by
  rw [Array.asInt_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zero_add, one_mul]

/-- If the digits from `e` on vanish, so does their value. -/
theorem nafTail_eq_zero (d : Array I8 256#usize) (e : ℕ)
    (h : ∀ k, e ≤ k → k < 256 → d[k]!.val = 0) : nafTail d e = 0 :=
  Finset.sum_eq_zero fun k hk => by
    rw [h (e + k) (Nat.le_add_right e k) (by have := Finset.mem_range.mp hk; omega), mul_zero]

/-- The value `∑_{k < 64 - e} 16^k d[e + k]` of the radix-`16` digits `d[e], …, d[63]`. -/
def radix16Tail (d : Array I8 64#usize) (e : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (64 - e), 16 ^ k * d[e + k]!.val

theorem radix16Tail_eq (d : Array I8 64#usize) (e : ℕ) (he : e < 64) :
    radix16Tail d e = d[e]!.val + 16 * radix16Tail d (e + 1) := by
  unfold radix16Tail
  rw [show 64 - e = 64 - (e + 1) + 1 by omega, Finset.sum_range_succ', Finset.mul_sum,
    pow_zero, one_mul, add_zero, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_succ, show e + (k + 1) = e + 1 + k by omega]
  ring

theorem radix16Tail_zero (d : Array I8 64#usize) : radix16Tail d 0 = d.asInt 4 := by
  rw [Array.asInt_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zero_add, pow_mul]
  norm_num

theorem radix16Tail_sixtyFour (d : Array I8 64#usize) : radix16Tail d 64 = 0 := by
  simp [radix16Tail]

/-- The sum of `zipWith f l₁ l₂` is the sum of `f l₁[k] l₂[k]` over the indices of the shorter
list. -/
theorem sum_zipWith_eq {α β G : Type} [Inhabited α] [Inhabited β] [AddCommMonoid G]
    (f : α → β → G) (l₁ : List α) (l₂ : List β) :
    (List.zipWith f l₁ l₂).sum =
      ∑ k ∈ Finset.range (min l₁.length l₂.length), f l₁[k]! l₂[k]! := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp
    | cons b l₂ =>
      rw [List.zipWith_cons_cons, List.sum_cons, ih, List.length_cons, List.length_cons,
        Nat.add_min_add_right, Finset.sum_range_succ']
      simp [add_comm]

/-! ### Adding a signed digit -/

theorem sub_nsmul_eq (P Q : curve25519.edwards.Point) (n : ℕ) (d : ℤ)
    (h : (n : ℤ) = -d) : P - n • Q = P + d • Q := by
  rw [← natCast_zsmul, h, neg_zsmul, sub_neg_eq_add]

theorem add_nsmul_eq (P Q : curve25519.edwards.Point) (n : ℕ) (d : ℤ)
    (h : (n : ℤ) = d) : P + n • Q = P + d • Q := by
  rw [← natCast_zsmul, h]

/-- The digit `d` of a NAF of width `w ≤ 8` is odd and `|d| < 2^(w-1)`: its absolute value as a
`Usize` selects `|d| • P` from a table of odd multiples. -/
theorem naf_digit_abs {d : ℤ} {w : ℕ} (hw : w ≤ 8) (hd : d % 2 = 1 ∧ 2 * |d| < 2 ^ w) :
    |d| % 2 = 1 ∧ 2 * |d| < 2 ^ w ∧ -128 < d ∧ d < 128 := by
  have h8 : (2 : ℤ) ^ w ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) hw
  refine ⟨?_, hd.2, ?_, ?_⟩
  · rcases abs_cases d with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega
  · have := neg_abs_le d; omega
  · have := le_abs_self d; omega

/-- One step of Horner's rule in base `2` over several points. -/
theorem horner2 (n e : ℕ) (d : ℕ → Array I8 256#usize) (P : ℕ → curve25519.edwards.Point)
    (he : e < 256) :
    2 • (∑ k ∈ Finset.range n, nafTail (d k) (e + 1) • P k) +
      ∑ k ∈ Finset.range n, (d k)[e]!.val • P k =
      ∑ k ∈ Finset.range n, nafTail (d k) e • P k := by
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nafTail_eq _ _ he, ← natCast_zsmul, smul_smul, ← add_smul, add_comm]
  push_cast
  ring_nf

/-! ### The length of a width-`5` non-adjacent form -/

section NafLength

variable (d : Array I8 256#usize)

/-- The value `∑_{k < e} 2^k d[k]` of the lowest `e` digits. -/
private def nafPrefix (e : ℕ) : ℤ := ∑ k ∈ Finset.range e, 2 ^ k * d[k]!.val

/-- Below a nonzero digit at `e` the four digits `e - 4, …, e - 1` vanish, so the prefix up to `e`
is the prefix up to `e - 4`. -/
private theorem nafPrefix_eq_of_ne_zero
    (hnaf : ∀ i : ℕ, i < 256 → ∀ j : ℕ, j < 256 → i < j → j < i + 5 → d[i]!.val ≠ 0 → d[j]!.val = 0)
    {e : ℕ} (he : e < 256) (hd : d[e]!.val ≠ 0) : nafPrefix d e = nafPrefix d (e - 4) := by
  unfold nafPrefix
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.sub_le e 4), add_eq_left]
  refine Finset.sum_eq_zero fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
  have hz : d[k]!.val = 0 := by
    by_contra hne
    exact hd (hnaf k (by omega) e he hk2 (by omega) hne)
  rw [hz, mul_zero]

/-- The lowest `e` digits of a width-`5` NAF have absolute value `< 2^(e + 3)`. -/
private theorem abs_nafPrefix_lt
    (hdig : ∀ i : ℕ, i < 256 → d[i]!.val ≠ 0 → d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ 5)
    (hnaf : ∀ i : ℕ, i < 256 → ∀ j : ℕ, j < 256 → i < j → j < i + 5 → d[i]!.val ≠ 0 →
      d[j]!.val = 0) :
    ∀ e ≤ 256, |nafPrefix d e| < 2 ^ (e + 3) := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he
    rcases e with _ | e
    · simp [nafPrefix]
    have hsucc : nafPrefix d (e + 1) = nafPrefix d e + 2 ^ e * d[e]!.val := by
      simp only [nafPrefix, Finset.sum_range_succ]
    by_cases hde : d[e]!.val = 0
    · rw [hsucc, hde, mul_zero, add_zero]
      calc |nafPrefix d e| < 2 ^ (e + 3) := ih e (by omega) (by omega)
        _ ≤ 2 ^ (e + 1 + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    · have h15 : |d[e]!.val| ≤ 15 := by have := (hdig e (by omega) hde).2; omega
      rw [hsucc, nafPrefix_eq_of_ne_zero d hnaf (by omega) hde]
      have hlow : |nafPrefix d (e - 4)| < 2 ^ e := by
        rcases Nat.lt_or_ge e 4 with h4 | h4
        · rw [show e - 4 = 0 by omega]
          simp only [nafPrefix, Finset.range_zero, Finset.sum_empty, abs_zero]
          positivity
        · have := ih (e - 4) (by omega) (by omega)
          rw [show e - 4 + 3 = e - 1 by omega] at this
          exact lt_of_lt_of_le this (pow_le_pow_right₀ (by norm_num) (by omega))
      have hd' : |2 ^ e * d[e]!.val| ≤ 2 ^ e * 15 := by
        rw [abs_mul, abs_pow, abs_two]
        gcongr
      calc |nafPrefix d (e - 4) + 2 ^ e * d[e]!.val|
          ≤ |nafPrefix d (e - 4)| + |2 ^ e * d[e]!.val| := abs_add_le _ _
        _ < 2 ^ e + 2 ^ e * 15 := by linarith
        _ = 2 ^ (e + 1 + 3) := by rw [show e + 1 + 3 = e + 4 by omega, pow_add]; ring

/-- In a width-`5` non-adjacent form (the digit properties of `non_adjacent_form`) of a value
`x < 2^n`, the digits above index `n` vanish. -/
theorem naf5_digits_eq_zero_of_lt {x n : ℕ} (hval : d.asInt 1 = x) (hx : x < 2 ^ n)
    (hdig : ∀ i : ℕ, i < 256 → d[i]!.val ≠ 0 → d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ 5)
    (hnaf : ∀ i : ℕ, i < 256 → ∀ j : ℕ, j < 256 → i < j → j < i + 5 → d[i]!.val ≠ 0 →
      d[j]!.val = 0) :
    ∀ k, n < k → k < 256 → d[k]!.val = 0 := by
  by_contra hcon
  push Not at hcon
  -- the highest nonzero digit `m`, above `n`
  let S := (Finset.range 256).filter fun k => n < k ∧ d[k]!.val ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨k, hk, hk', hne⟩ := hcon
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk', hk, hne⟩⟩
  set m := S.max' hS with hm
  obtain ⟨hm256, hnm, hdm⟩ : m < 256 ∧ n < m ∧ d[m]!.val ≠ 0 := by
    have := Finset.mem_filter.mp (S.max'_mem hS)
    exact ⟨Finset.mem_range.mp this.1, this.2.1, this.2.2⟩
  have habove : ∀ j, m < j → j < 256 → d[j]!.val = 0 := by
    intro j hj hj'
    by_contra hne
    have : j ≤ m := S.le_max' j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj', by omega, hne⟩)
    omega
  -- `x = 2^m d[m] + P(m - 4)` with `|P(m - 4)| < 2^(m - 1)`
  have hx' : (x : ℤ) = nafPrefix d (m - 4) + 2 ^ m * d[m]!.val := by
    rw [← hval, Array.asInt_eq_sum, ← nafPrefix_eq_of_ne_zero d hnaf hm256 hdm]
    simp only [one_mul]
    rw [show (256#usize).val = m + 1 + (256 - (m + 1)) by simp; omega, Finset.sum_range_add,
      Finset.sum_range_succ]
    rw [Finset.sum_eq_zero (s := Finset.range (256 - (m + 1))) fun j _ => by
      rw [habove (m + 1 + j) (by omega) (by simp at *; omega), mul_zero]]
    simp only [nafPrefix, add_zero]
  have hlow : |nafPrefix d (m - 4)| < 2 ^ (m - 1) := by
    rcases Nat.lt_or_ge m 4 with h4 | h4
    · rw [show m - 4 = 0 by omega]
      simp only [nafPrefix, Finset.range_zero, Finset.sum_empty, abs_zero]
      positivity
    · have := abs_nafPrefix_lt d hdig hnaf (m - 4) (by omega)
      rwa [show m - 4 + 3 = m - 1 by omega] at this
  have hpow : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ', show m - 1 + 1 = m by omega]
  have hodd := (hdig m hm256 hdm).1
  rcases lt_or_gt_of_ne hdm with hneg | hpos
  · -- a negative top digit makes `x` negative
    have : nafPrefix d (m - 4) + 2 ^ m * d[m]!.val < 0 := by
      have h1 : 2 ^ m * d[m]!.val ≤ -2 ^ m := by
        have : d[m]!.val ≤ -1 := by omega
        nlinarith [pow_pos (two_pos (α := ℤ)) m]
      have h2 := (abs_lt.mp hlow).2
      have h3 : (0 : ℤ) < 2 ^ (m - 1) := by positivity
      linarith
    rw [← hx'] at this
    exact absurd this (not_lt.mpr (Int.natCast_nonneg x))
  · -- a positive top digit makes `x > 2^(m - 1) ≥ 2^n`
    have h1 : 2 ^ m ≤ 2 ^ m * d[m]!.val := by
      nlinarith [pow_pos (two_pos (α := ℤ)) m]
    have h2 : (2 : ℤ) ^ n ≤ 2 ^ (m - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have := (abs_lt.mp hlow).1
    have hxz : (2 : ℤ) ^ n < x := by rw [hx']; linarith
    exact absurd hx (by exact_mod_cast hxz.le.not_gt)

end NafLength

end Curve25519Dalek
