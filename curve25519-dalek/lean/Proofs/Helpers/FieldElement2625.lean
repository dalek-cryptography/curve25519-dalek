/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga, Wojciech Aleksander Wołoszyn
-/
module
public import Defs.FieldElement2625
public import Aeneas
public import Proofs.Helpers.Array
public section

/-! # Lemmas about `FieldElement2625` values

Forms of `Array.asNat2625`: the weight `2^⌈i · 51 / 2⌉` of limb `i` is `limbWeight i =
2^(26 ⌈i/2⌉ + 25 ⌊i/2⌋)` (`asNat2625_eq_sum`), the radix of limb `i` is `limbRadix i =
2^(26 - i % 2)`, and the ten terms written out (`asNat_expand`, `asNat2625_make`). Also the
arithmetic facts used by the proofs of `backend/serial/u32/field.rs`. -/

open Aeneas Aeneas.Std Finset curve25519

/-! ## Arrays -/

namespace Aeneas.Std

/-- Overwriting all ten elements of `a` with those of `b` gives `b`. -/
theorem Array.set_getElem_ten {α : Type} (a b : Array α 10#usize) :
    (((((((((a.set 0#usize b.val[0]).set 1#usize b.val[1]).set 2#usize b.val[2]).set 3#usize
      b.val[3]).set 4#usize b.val[4]).set 5#usize b.val[5]).set 6#usize b.val[6]).set 7#usize
      b.val[7]).set 8#usize b.val[8]).set 9#usize b.val[9] = b := by
  ext : 1
  simp only [Array.set_val_eq]
  apply List.ext_getElem (by simp)
  intro i h _
  have hi : i < 10 := by simpa using h
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | omega | simp

/-- A ten-element array rebuilt from its own elements is the array itself. -/
theorem Array.make_getElem_ten {α : Type} (a : Array α 10#usize)
    (h : [a.val[0], a.val[1], a.val[2], a.val[3], a.val[4], a.val[5], a.val[6], a.val[7],
      a.val[8], a.val[9]].length = (10#usize).val) :
    Array.make 10#usize [a.val[0], a.val[1], a.val[2], a.val[3], a.val[4], a.val[5], a.val[6],
      a.val[7], a.val[8], a.val[9]] h = a := by
  ext : 1
  rw [Array.make_val]
  apply List.ext_getElem (by simp)
  intro i h _
  have hi : i < 10 := by simpa using h
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | omega | rfl

end Aeneas.Std

/-! ## Limb weights -/

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- The radix of limb `i`: `2^26` for even `i`, `2^25` for odd `i`. -/
@[expose] def limbRadix (i : Nat) : Nat := 2 ^ (26 - i % 2)

/-- The weight of limb `i`: `2^(26 ⌈i/2⌉ + 25 ⌊i/2⌋)`, the product of the radices below it. -/
@[expose] def limbWeight (i : Nat) : Nat := 2 ^ (26 * ((i + 1) / 2) + 25 * (i / 2))

/-- Unfolds `limbRadix` for `scalar_tac` and `agrind`, so that `step` can discharge
preconditions stated with it. Not a `simp` lemma, so that `simp` keeps `limbRadix` folded. -/
@[scalar_tac_simps, agrind =]
theorem limbRadix_eq (i : Nat) : limbRadix i = 2 ^ (26 - i % 2) := rfl

/-- Unfolds `limbWeight` for `scalar_tac` and `agrind`. Not a `simp` lemma, so that `simp` keeps
`limbWeight` folded. -/
@[scalar_tac_simps, agrind =]
theorem limbWeight_eq (i : Nat) : limbWeight i = 2 ^ (26 * ((i + 1) / 2) + 25 * (i / 2)) := rfl

/-- The weight of limb `i + 1` is the weight of limb `i` times its radix. -/
theorem limbWeight_succ (i : Nat) :
    limbWeight (i + 1) = limbRadix i * limbWeight i := by
  unfold limbRadix limbWeight
  rewrite [← Nat.pow_add, Nat.pow_right_inj (by decide)]
  omega

/-- `limbWeight i` is the weight `2^⌈i · 51 / 2⌉` of the Rust comment. -/
theorem limbWeight_eq_ceilDiv (i : ℕ) : limbWeight i = 2 ^ (i * 51 ⌈/⌉ 2) := by
  rw [Nat.ceilDiv_eq_add_pred_div, limbWeight]
  congr 1
  omega

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace Aeneas.Std

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `asNat2625` with the weights `limbWeight i`. -/
theorem Array.asNat2625_eq_sum {ty : UScalarTy} (a : Array (UScalar ty) 10#usize) :
    a.asNat2625 = ∑ i ∈ range 10, limbWeight i * a[i]!.val := by
  rw [Array.asNat2625_def]
  exact sum_congr rfl fun i _ => by rw [limbWeight_eq_ceilDiv, Nat.mul_comm]

/-- Two arrays of ten limbs with pointwise-equal limb values have equal values. -/
theorem Array.asNat2625_congr {ty ty' : UScalarTy}
    (x : Array (UScalar ty) 10#usize) (y : Array (UScalar ty') 10#usize)
    (h : ∀ i : ℕ, i < 10 → x[i]!.val = y[i]!.val) :
    x.asNat2625 = y.asNat2625 := by
  rw [Array.asNat2625_eq_sum, Array.asNat2625_eq_sum]
  exact sum_congr rfl fun i hi => by rw [mem_range] at hi; rw [h i hi]

/-- The value of ten limbs written out as its ten weighted limbs. -/
theorem Array.asNat2625_expand {ty : UScalarTy} (x : Array (UScalar ty) 10#usize) :
    x.asNat2625 =
      x[0]!.val + 2 ^ 26 * x[1]!.val + 2 ^ 51 * x[2]!.val + 2 ^ 77 * x[3]!.val +
        2 ^ 102 * x[4]!.val + 2 ^ 128 * x[5]!.val + 2 ^ 153 * x[6]!.val +
        2 ^ 179 * x[7]!.val + 2 ^ 204 * x[8]!.val + 2 ^ 230 * x[9]!.val := by
  simp only [Array.asNat2625_eq_sum, limbWeight, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  norm_num

/-- The value of a ten-element `Array.make` written out as its weighted entries. -/
theorem Array.asNat2625_make {ty : UScalarTy} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : UScalar ty)
    (hl : [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].length = (10#usize).val) :
    (Array.make 10#usize [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] hl).asNat2625 =
      a0.val + 2 ^ 26 * a1.val + 2 ^ 51 * a2.val + 2 ^ 77 * a3.val + 2 ^ 102 * a4.val +
        2 ^ 128 * a5.val + 2 ^ 153 * a6.val + 2 ^ 179 * a7.val + 2 ^ 204 * a8.val +
        2 ^ 230 * a9.val := by
  rw [Array.asNat2625_expand]
  simp [Array.make, Array.getElem!_Nat_eq]

end Aeneas.Std

/-! ## `FieldElement2625` -/

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

attribute [simp, scalar_tac_simps, grind =, agrind =] asNat_def

/-- The value of a field element written out as its ten weighted limbs. -/
theorem asNat_expand (x : FieldElement2625) :
    x.asNat =
      x[0]!.val + 2 ^ 26 * x[1]!.val + 2 ^ 51 * x[2]!.val + 2 ^ 77 * x[3]!.val +
        2 ^ 102 * x[4]!.val + 2 ^ 128 * x[5]!.val + 2 ^ 153 * x[6]!.val +
        2 ^ 179 * x[7]!.val + 2 ^ 204 * x[8]!.val + 2 ^ 230 * x[9]!.val := by
  rw [asNat_def, Array.asNat2625_expand]

open Result Aeneas.Std.WP in
/-- At an in-bounds index, `Array.index_usize` on a field element returns the limb. -/
theorem index_usize_eq (a : FieldElement2625) (j : Usize) (h_j : j.val < 10) :
    Array.index_usize a j = ok a[j.val]! := by
  have h : j.val < a.val.length := by simp [h_j]
  simp [Array.index_usize, Array.getElem!_Nat_eq, List.getElem?_eq_getElem h]

/-- A common bound on the ten entries of an `Array.make` bounds every entry; this discharges the
limb precondition of `reduce`. -/
theorem getElem!_make_le {ty : UScalarTy} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : UScalar ty)
    (hl : [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].length = (10#usize).val) (B : Nat)
    (h0 : a0.val ≤ B) (h1 : a1.val ≤ B) (h2 : a2.val ≤ B) (h3 : a3.val ≤ B)
    (h4 : a4.val ≤ B) (h5 : a5.val ≤ B) (h6 : a6.val ≤ B) (h7 : a7.val ≤ B)
    (h8 : a8.val ≤ B) (h9 : a9.val ≤ B) :
    ∀ i : ℕ, i < 10 →
      (Array.make 10#usize [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] hl)[i]!.val ≤ B := by
  intro i hi
  rewrite [← Finset.mem_range] at hi
  fin_cases hi <;> simpa [Array.make, Array.getElem!_Nat_eq]

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-! ## Arithmetic -/

/-- Disjoint `|||` is addition: the low operand fits under the shift. -/
theorem Nat.or_mul_two_pow_eq_add_of_lt {a b i : Nat} (h : a < 2 ^ i) :
    a ||| b * 2 ^ i = a + b * 2 ^ i := by
  rw [Nat.lor_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt h, Nat.add_comm]

/-- Adding a low part `m < l` to a multiple of `l` commutes with reduction modulo `k * l`. -/
theorem Nat.add_mul_mod_mul_right_of_lt {m n k l : Nat} (hm : m < l) :
    (m + n * l) % (k * l) = m + n * l % (k * l) := by
  by_cases hk : 0 < k
  · have hlt : m + n * l % (k * l) < k * l := by
      rw [Nat.mul_mod_mul_right]
      calc m + n % k * l
          < l + n % k * l := Nat.add_lt_add_right hm _
        _ = (n % k + 1) * l := by ring
        _ ≤ k * l := Nat.mul_le_mul_right _ (Nat.mod_lt n hk)
    have hmk : m < k * l := Nat.lt_of_lt_of_le hm (Nat.le_mul_of_pos_left l hk)
    rw [Nat.add_mod, Nat.mod_eq_of_lt hmk, Nat.mod_eq_of_lt hlt]
  · simp [Nat.eq_zero_of_not_pos hk]

/-- Adding a low part `m < l` to a multiple of `l` commutes with reduction modulo `l * k`. -/
theorem Nat.add_mul_mod_mul_left_of_lt {m n k l : Nat} (hm : m < l) :
    (m + l * n) % (l * k) = m + l * n % (l * k) := by
  simp only [Nat.mul_comm]
  exact Nat.add_mul_mod_mul_right_of_lt hm

/-- `a % m · n + b % n < m · n`. -/
theorem Nat.lt_mod_mul_add_mod {a b m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    a % m * n + b % n < m * n := by
  calc
    _ ≤ (m - 1) * n + b % n :=
      by rewrite [Nat.add_le_add_iff_right, Nat.mul_le_mul_right_iff hn]
         apply Nat.le_sub_one_of_lt; exact Nat.mod_lt _ hm
    _ < (m - 1) * n + n :=
      by rewrite [Nat.add_lt_add_iff_left]; exact Nat.mod_lt _ hn
    _ = m * n :=
      by rw [Nat.sub_mul, Nat.one_mul, Nat.sub_add_cancel (by exact Nat.le_mul_of_pos_left _ hm)]

/-- Sums over a finset agree up to `d` when the summands agree except at a subset whose combined
contribution differs by `d`. -/
theorem Finset.sum_eq_sum_add_of_subset {ι M : Type*} [AddCommMonoid M] {s : Finset ι}
    {f g : ι → M} {t : Finset ι} (d : M) (ht : t ⊆ s) (heq : ∀ j ∈ s, j ∉ t → f j = g j)
    (hd : ∑ j ∈ t, f j = (∑ j ∈ t, g j) + d) :
    ∑ j ∈ s, f j = (∑ j ∈ s, g j) + d := by
  classical
  have : ∀ x ∈ s \ t, f x = g x := by
    intro x hx
    exact heq x (by rw [mem_sdiff] at hx; exact hx.1) (by rw [mem_sdiff] at hx; exact hx.2)
  calc
    _ = (∑ j ∈ s \ t, f j) + ∑ j ∈ t, f j := (sum_sdiff (by exact ht)).symm
    _ = (∑ j ∈ s \ t, g j) + ∑ j ∈ t, f j := by rw [sum_congr (rfl) ‹_›]
    _ = (∑ j ∈ s \ t, g j) + (∑ j ∈ t, g j) + d := by rw [hd, ← add_assoc]
    _ = (∑ j ∈ s, g j) + d := by rw [sum_sdiff (by exact ht)]
