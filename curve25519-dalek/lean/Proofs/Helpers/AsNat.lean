/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.Array
public import Aeneas.Std.Scalar.Notations
import Aeneas.Tactic.Step.Step
public section

/-! # Lemmas about `Array.asNat`

The value of an array as little-endian digits in radix `2 ^ bits`: as a sum (`asNat_eq_sum`),
unfolded for five and nine digits, its bounds, its digits, its injectivity, and how it changes
when a digit is set. -/

open Aeneas Aeneas.Std

/-! ## Digits of natural numbers -/

namespace Nat

/-- A little-endian number with `k` digits below `2 ^ bits` is below `2 ^ (bits * k)`. -/
theorem sum_pow_mul_lt (bits k : ℕ) (x : ℕ → ℕ) (hx : ∀ j < k, x j < 2 ^ bits) :
    ∑ j ∈ Finset.range k, 2 ^ (bits * j) * x j < 2 ^ (bits * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_succ, Nat.pow_add]
    calc ∑ j ∈ Finset.range k, 2 ^ (bits * j) * x j + 2 ^ (bits * k) * x k
        < 2 ^ (bits * k) + 2 ^ (bits * k) * x k :=
          Nat.add_lt_add_right (ih fun j hj => hx j (by omega)) _
      _ = 2 ^ (bits * k) * (x k + 1) := by ring
      _ ≤ 2 ^ (bits * k) * 2 ^ bits := Nat.mul_le_mul_left _ (hx k (by omega))

/-- Digit `j` of a number written with digits below `b`. -/
theorem ofDigits_div_pow_mod (b : ℕ) (L : List ℕ) (hL : ∀ d ∈ L, d < b) (j : ℕ) :
    Nat.ofDigits b L / b ^ j % b = L[j]! := by
  induction L generalizing j with
  | nil => simp
  | cons d L ih =>
    have hd : d < b := hL d List.mem_cons_self
    have hb : 0 < b := by omega
    rw [Nat.ofDigits_cons]
    cases j with
    | zero => simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    | succ j =>
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hb,
        Nat.div_eq_of_lt hd, Nat.zero_add, ih (fun d' hd' => hL d' (List.mem_cons_of_mem _ hd'))]
      simp

/-- The first `k` digits of `x` in radix `b` give `x % b ^ k`. -/
theorem sum_digits_eq_mod (b k x : ℕ) :
    ∑ j ∈ Finset.range k, b ^ j * (x / b ^ j % b) = x % b ^ k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih => rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ]

end Nat

namespace Aeneas.Std.Array

/-! ## The value as a sum -/

/-- `asNat` as a weighted sum of the digits. -/
theorem asNat_eq_sum {ty : UScalarTy} {n : Usize} (bits : ℕ) (a : Array (UScalar ty) n) :
    a.asNat bits = ∑ i ∈ Finset.range n.val, 2 ^ (bits * i) * a[i]!.val := by
  have h : a.val.length = n.val := by simp
  simp only [Array.asNat_def, Array.getElem!_Nat_eq]
  rw [← h]
  generalize a.val = l
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp [Nat.ofDigits, ih, pow_succ, pow_mul, Finset.mul_sum]
    ring_nf

/-- `asNat` of five digits, unfolded. -/
theorem asNat_five {ty : UScalarTy} (bits : ℕ) (a : Array (UScalar ty) 5#usize) :
    a.asNat bits = a[0]!.val + 2 ^ bits * a[1]!.val + 2 ^ (2 * bits) * a[2]!.val
      + 2 ^ (3 * bits) * a[3]!.val + 2 ^ (4 * bits) * a[4]!.val := by
  have h : a.val.length = 5 := by simp
  simp only [Array.asNat_def, Array.getElem!_Nat_eq]
  generalize a.val = l at h ⊢
  match l, h with
  | [x0, x1, x2, x3, x4], _ =>
    simp only [Nat.ofDigits, List.map_cons, List.map_nil, Nat.cast_id, List.getElem!_cons_zero,
      List.getElem!_cons_succ]
    ring

/-- `asNat` of nine digits, unfolded. -/
theorem asNat_nine {ty : UScalarTy} (bits : ℕ) (a : Array (UScalar ty) 9#usize) :
    a.asNat bits = a[0]!.val + 2 ^ bits * a[1]!.val + 2 ^ (2 * bits) * a[2]!.val
      + 2 ^ (3 * bits) * a[3]!.val + 2 ^ (4 * bits) * a[4]!.val + 2 ^ (5 * bits) * a[5]!.val
      + 2 ^ (6 * bits) * a[6]!.val + 2 ^ (7 * bits) * a[7]!.val
      + 2 ^ (8 * bits) * a[8]!.val := by
  have h : a.val.length = 9 := by simp
  simp only [Array.asNat_def, Array.getElem!_Nat_eq]
  generalize a.val = l at h ⊢
  match l, h with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8], _ =>
    simp only [Nat.ofDigits, List.map_cons, List.map_nil, Nat.cast_id, List.getElem!_cons_zero,
      List.getElem!_cons_succ]
    ring

/-- Grouping the digits of an array into `m` blocks of `w` digits. -/
theorem asNat_eq_sum_blocks {ty : UScalarTy} {n : Usize} (bits w m : ℕ) (a : Array (UScalar ty) n)
    (h : w * m = n.val) :
    a.asNat bits = ∑ k ∈ Finset.range m,
      2 ^ (bits * w * k) * ∑ j ∈ Finset.range w, 2 ^ (bits * j) * a[w * k + j]!.val := by
  rw [asNat_eq_sum, ← h]
  clear h
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, Finset.mul_sum]
    refine congrArg (_ + ·) (Finset.sum_congr rfl fun j _ => ?_)
    rw [← Nat.mul_assoc, ← Nat.pow_add]
    ring_nf

/-- Limbs of `8 * bits` bits, each made of the next 8 digits of `b` (and zero limbs above), have the
value of `b`. -/
theorem asNat_limbs_eq {tyL tyB : UScalarTy} {n m : Usize} (bits k : ℕ)
    (L : Array (UScalar tyL) n) (b : Array (UScalar tyB) m) (hm : m.val = 8 * k) (hk : k ≤ n.val)
    (hL : ∀ i < n.val, L[i]!.val < 2 ^ (8 * bits))
    (hLb : ∀ i < k, ∀ j : ℕ, j < 8 → L[i]!.val / 2 ^ (bits * j) % 2 ^ bits = b[8 * i + j]!.val)
    (hz : ∀ i, k ≤ i → i < n.val → L[i]!.val = 0) :
    L.asNat (8 * bits) = b.asNat bits := by
  rw [asNat_eq_sum_blocks bits 8 k b (by rw [hm]), asNat_eq_sum,
    ← Finset.sum_range_add_sum_Ico _ hk]
  have h0 : ∑ i ∈ Finset.Ico k n.val, 2 ^ (8 * bits * i) * L[i]!.val = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_Ico] at hi
      rw [hz i hi.1 hi.2, Nat.mul_zero]
  rw [h0, Nat.add_zero, Nat.mul_comm 8 bits]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  refine congrArg (2 ^ (bits * 8 * i) * ·) ?_
  have hsum := Nat.sum_digits_eq_mod (2 ^ bits) 8 L[i]!.val
  rw [← pow_mul, Nat.mod_eq_of_lt (by rw [Nat.mul_comm]; exact hL i (hi'.trans_le hk))] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← pow_mul, hLb i hi' j (Finset.mem_range.mp hj)]

/-! ## Bounds and digits -/

/-- An array with digits below `2 ^ bits` represents a number below `2 ^ (bits * n)`. -/
theorem asNat_lt {ty : UScalarTy} {n : Usize} (bits : ℕ) (a : Array (UScalar ty) n)
    (h : ∀ i < n.val, a[i]!.val < 2 ^ bits) :
    a.asNat bits < 2 ^ (bits * n.val) := by
  rw [asNat_eq_sum]
  exact Nat.sum_pow_mul_lt bits n.val (fun j => a[j]!.val) h

/-- The value modulo `2 ^ (bits * m)` of an array with digits below `2 ^ bits` is given by its first
`m` digits. -/
theorem asNat_mod_pow_eq_sum {ty : UScalarTy} {n : Usize} (bits m : ℕ) (a : Array (UScalar ty) n)
    (hmn : m ≤ n.val) (ha : ∀ j < n.val, a[j]!.val < 2 ^ bits) :
    a.asNat bits % 2 ^ (bits * m) = ∑ j ∈ Finset.range m, 2 ^ (bits * j) * a[j]!.val := by
  have hdvd : 2 ^ (bits * m) ∣ ∑ j ∈ Finset.Ico m n.val, 2 ^ (bits * j) * a[j]!.val :=
    Finset.dvd_sum fun j hj => Dvd.dvd.mul_right
      (Nat.pow_dvd_pow 2 (Nat.mul_le_mul_left _ (Finset.mem_Ico.mp hj).1)) _
  obtain ⟨c, hc⟩ := hdvd
  have hlt := Nat.sum_pow_mul_lt bits m (fun j => a[j]!.val) fun j hj => ha j (by omega)
  rw [asNat_eq_sum, ← Finset.sum_range_add_sum_Ico _ hmn, hc, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hlt]

/-- Modulo any `m` dividing the radix `2^bits`, the value of a nonempty array is that of its first
digit (e.g. the parity of a byte string is the parity of its first byte). -/
theorem asNat_mod_of_dvd {ty : UScalarTy} {n : Usize} (bits : ℕ) {m : ℕ} (hm : m ∣ 2 ^ bits)
    (a : Array (UScalar ty) n) (hn : 0 < n.val) : a.asNat bits % m = a[0]!.val % m := by
  have h : a.val.length = n.val := by simp
  simp only [Array.asNat_def, Array.getElem!_Nat_eq]
  generalize a.val = l at h ⊢
  match l, h with
  | [], h => simp at h; scalar_tac
  | x :: l, _ =>
    obtain ⟨k, hk⟩ := hm
    simp only [List.map_cons, Nat.ofDigits_cons, List.getElem!_cons_zero]
    rw [hk, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- Digit `j` of an array whose digits are below `2 ^ bits`. -/
theorem asNat_div_pow_mod {ty : UScalarTy} {n : Usize} (bits : ℕ) (a : Array (UScalar ty) n)
    (ha : ∀ i < n.val, a[i]!.val < 2 ^ bits) (j : ℕ) :
    a.asNat bits / 2 ^ (bits * j) % 2 ^ bits = a[j]!.val := by
  have hL : ∀ d ∈ a.val.map (·.val), d < 2 ^ bits := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    simp only [List.length_map, List.getElem_map] at hi ⊢
    have := ha i (by simpa using hi)
    rwa [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some] at this
  rw [Array.asNat_def, pow_mul, Nat.ofDigits_div_pow_mod _ _ hL j, Array.getElem!_Nat_eq]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map]
  by_cases hj : j < a.val.length
  · rw [List.getElem?_eq_getElem hj]
    rfl
  · rw [List.getElem?_eq_none (Nat.not_lt.mp hj), Option.map_none, Option.getD_none,
      Option.getD_none, UScalar.default_val]
    rfl

/-- The last digit of an array whose digits are below `2 ^ bits` is its value divided by
`2 ^ (bits * (n - 1))`. -/
theorem getElem!_last_eq_asNat_div {ty : UScalarTy} {n : Usize} (bits : ℕ)
    (a : Array (UScalar ty) n) (ha : ∀ i < n.val, a[i]!.val < 2 ^ bits) (hn : 0 < n.val) :
    a[n.val - 1]!.val = a.asNat bits / 2 ^ (bits * (n.val - 1)) := by
  have hpow : bits * (n.val - 1) + bits = bits * n.val := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
  rw [← asNat_div_pow_mod bits a ha (n.val - 1), Nat.mod_eq_of_lt]
  apply Nat.div_lt_of_lt_mul
  rw [← Nat.pow_add, hpow]
  exact asNat_lt bits a ha

/-- An array of `n`-bit scalars is determined by its value in radix `2 ^ n`. -/
theorem eq_of_asNat_eq {ty : UScalarTy} {n : Usize} {a b : Array (UScalar ty) n}
    (h : a.asNat ty.numBits = b.asNat ty.numBits) : a = b := by
  have hlt : ∀ (l : List (UScalar ty)), ∀ x ∈ l.map (·.val), x < 2 ^ ty.numBits := by
    intro l x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
    exact y.hBounds
  have hbits : ty.numBits ≠ 0 := by
    rcases System.Platform.numBits_eq with hnb | hnb <;> cases ty <;> simp [hnb]
  have hmap := Nat.ofDigits_inj_of_len_eq (Nat.one_lt_two_pow hbits)
    (by simp) (hlt a.val) (hlt b.val) (by rwa [asNat_def, asNat_def] at h)
  exact Array.ext a b
    (List.map_injective_iff.mpr (fun x y hxy => UScalar.eq_of_val_eq hxy) hmap)

/-- `asNat` is additive limb by limb, with a sum on both sides. -/
theorem asNat_add_eq_add {ty : UScalarTy} {n : Usize} (bits : ℕ) (a b c d : Array (UScalar ty) n)
    (h : ∀ i < n.val, a[i]!.val + b[i]!.val = c[i]!.val + d[i]!.val) :
    a.asNat bits + b.asNat bits = c.asNat bits + d.asNat bits := by
  simp only [asNat_eq_sum, ← Finset.sum_add_distrib, ← mul_add]
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

/-- `asNat` is additive limb by limb. -/
theorem asNat_add_eq {ty : UScalarTy} {n : Usize} (bits : ℕ) (a b c : Array (UScalar ty) n)
    (h : ∀ i < n.val, a[i]!.val + b[i]!.val = c[i]!.val) :
    a.asNat bits + b.asNat bits = c.asNat bits := by
  simp only [asNat_eq_sum, ← Finset.sum_add_distrib, ← mul_add]
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

/-! ## Setting a digit -/

/-- The digit sum of the first `k + 1` digits after setting digit `k` to `x`. -/
theorem sum_range_succ_set {ty : UScalarTy} {n : Usize} (bits : ℕ) (a : Array (UScalar ty) n)
    (k : Usize) (x : UScalar ty) (hk : k.val < n.val) :
    ∑ j ∈ Finset.range (k.val + 1), 2 ^ (bits * j) * (a.set k x)[j]!.val
      = ∑ j ∈ Finset.range k.val, 2 ^ (bits * j) * a[j]!.val + 2 ^ (bits * k.val) * x.val := by
  rw [Finset.sum_range_succ, Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by simpa using hk⟩]
  refine congrArg (· + _) (Finset.sum_congr rfl fun j hj => ?_)
  rw [Array.getElem!_Nat_set_ne _ _ _ _ (Nat.ne_of_gt (Finset.mem_range.mp hj))]

/-- Setting digit `k` changes the value by the difference of the digits, weighted by
`2 ^ (bits * k)`. -/
theorem asNat_set_add {ty : UScalarTy} {n : Usize} (bits : ℕ) (a : Array (UScalar ty) n)
    (k : Usize) (x : UScalar ty) (hk : k.val < n.val) :
    (a.set k x).asNat bits + 2 ^ (bits * k.val) * a[k.val]!.val
      = a.asNat bits + 2 ^ (bits * k.val) * x.val := by
  have hmem : k.val ∈ Finset.range n.val := Finset.mem_range.mpr hk
  rw [asNat_eq_sum, asNat_eq_sum, ← Finset.add_sum_erase _ _ hmem,
    ← Finset.add_sum_erase _ _ hmem,
    Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by simpa using hk⟩]
  have hrest : ∑ j ∈ (Finset.range n.val).erase k.val, 2 ^ (bits * j) * (a.set k x)[j]!.val
      = ∑ j ∈ (Finset.range n.val).erase k.val, 2 ^ (bits * j) * a[j]!.val :=
    Finset.sum_congr rfl fun j hj => by
      rw [Array.getElem!_Nat_set_ne _ _ _ _ (Ne.symm (Finset.ne_of_mem_erase hj))]
  rw [hrest]
  ring

/-- An array that is the concatenation of two byte arrays `b ++ c`: `b` holds its value modulo
`2 ^ (8 |b|)`, `c` the quotient. -/
theorem asNat_append_eq {n m k : Usize} (a : Array U8 n) (b : Array U8 m) (c : Array U8 k)
    (h : a.val = b.val ++ c.val) :
    b.asNat 8 = a.asNat 8 % 2 ^ (8 * m.val) ∧ c.asNat 8 = a.asNat 8 / 2 ^ (8 * m.val) := by
  have hb := asNat_lt 8 b (fun i _ => (b[i]!).hBounds)
  have hsplit : a.asNat 8 = b.asNat 8 + 2 ^ (8 * m.val) * c.asNat 8 := by
    rw [asNat_def, asNat_def, asNat_def, h, List.map_append, Nat.ofDigits_append, List.length_map,
      Array.length_eq, ← pow_mul]
  have hpos : 0 < 2 ^ (8 * m.val) := Nat.two_pow_pos _
  refine ⟨?_, ?_⟩
  · rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  · rw [hsplit, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hb, zero_add]

end Aeneas.Std.Array
