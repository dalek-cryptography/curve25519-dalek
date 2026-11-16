/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Aeneas.Std.Array.ArraySlice
public import Aeneas.Std.Scalar.Notations
import Aeneas.Tactic.Step.StepStar
public section

/-! # Lemmas about Aeneas arrays and slices

Reads and updates described with `getElem!` (opt-in `step` specs, see `Proofs.Helpers.StepSpecs`),
the entries of array literals and of `Array.repeat`, rebuilding an array from its entries, and
properties of the entries carried through `set`. -/

open Aeneas Aeneas.Std

namespace Aeneas.Std.Array

/-- `index_usize` with the result as `getElem!`, which `simp_lists` and `agrind` handle well on
chains of `set`. Activated with `open scoped Helpers.IndexStep Helpers.UpdateStep`. -/
theorem index_usize_getElem!_spec {α : Type} [Inhabited α] {n : Usize} (v : Array α n) (i : Usize)
    (hi : i.val < n.val) :
    v.index_usize i ⦃ (x : α) => x = v[i.val]! ⦄ := by
  step*
  simp_lists [*]

/-- `Slice.index_usize` with the result as `getElem!`. Activated with
`open scoped Helpers.IndexStep Helpers.UpdateStep`. -/
theorem _root_.Aeneas.Std.Slice.index_usize_getElem!_spec {α : Type} [Inhabited α] (s : Slice α)
    (i : Usize) (hi : i.val < s.length) :
    s.index_usize i ⦃ (x : α) => x = s[i.val]! ⦄ := by
  step*
  simp_lists [*]

/-- `update` described elementwise with `getElem!`, which `agrind` can chain through several
updates. Activated with `open scoped Helpers.IndexStep Helpers.UpdateStep`. -/
theorem update_getElem!_spec {α : Type} [Inhabited α] {n : Usize} (v : Array α n) (i : Usize)
    (x : α) (hi : i.val < n.val) :
    v.update i x ⦃ (nv : Array α n) => nv[i.val]! = x ∧ ∀ j ≠ i.val, nv[j]! = v[j]! ⦄ := by
  step*
  subst_vars
  exact ⟨Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by simpa using hi⟩,
    fun j hj => Array.getElem!_Nat_set_ne _ _ _ _ (Ne.symm hj)⟩

/-- The entries of an array literal `Array.make n l`. -/
theorem getElem!_make {α : Type} [Inhabited α] {n : Usize} (l : List α) (hl : l.length = n.val)
    (i : ℕ) : (Array.make n l hl)[i]! = l[i]! := by
  simp only [Array.getElem!_Nat_eq, Array.make_val]

/-- `index_usize` on an array literal `Array.make n l`, with the result as `l[i]!`. -/
theorem index_usize_make_spec {α : Type} [Inhabited α] {n : Usize} (l : List α)
    (hl : l.length = n.val) (i : Usize) (hi : i.val < n.val) :
    (Array.make n l hl).index_usize i ⦃ (x : α) => x = l[i.val]! ⦄ := by
  step*
  simp_lists [*, Array.make_val]

/-- The entries of `Array.repeat n x` below `n`. -/
theorem getElem!_repeat {α : Type} [Inhabited α] {n : Usize} (x : α) {j : ℕ} (hj : j < n.val) :
    (Array.repeat n x)[j]! = x := by
  rw [Array.getElem!_Nat_eq, Array.repeat_val, List.getElem!_replicate _ hj]

/-- Checked indexing into the underlying list of an `Std.Array` agrees with `getElem!`. Unlike
`List.Inhabited_getElem_eq_getElem!` (a `def`) this can be used by `simp`. -/
theorem getElem_val_eq_getElem! {α : Type} [Inhabited α] {N : Usize} (a : Std.Array α N)
    (j : Nat) (h : j < (↑a : List α).length) : (↑a : List α)[j] = a[j]! := by
  rw [Array.getElem!_Nat_eq, List.Inhabited_getElem_eq_getElem! _ _ h]

/-- Overwriting all five elements of `a` with those of `b` gives `b`. -/
theorem set_getElem_five {α : Type} (a b : Array α 5#usize) :
    ((((a.set 0#usize b.val[0]).set 1#usize b.val[1]).set 2#usize b.val[2]).set 3#usize
      b.val[3]).set 4#usize b.val[4] = b := by
  ext : 1
  simp only [Array.set_val_eq]
  apply List.ext_getElem (by simp)
  grind

/-- Arrays are equal when their slices are. -/
theorem eq_of_to_slice_eq {α : Type} {n : Usize} {a b : Array α n}
    (h : a.to_slice = b.to_slice) : a = b := by
  have hval := congrArg Slice.val h
  simp only [Array.val_to_slice] at hval
  exact Array.ext a b hval

/-- A bound on five limbs, unfolded into its five instances (for `simp_lists`). -/
theorem _root_.Nat.forall_lt_five {P : ℕ → Prop} :
    (∀ i : ℕ, i < 5 → P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 := by
  constructor
  · intro h
    exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i hi
    match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4

/-- Setting entry `i` extends a property of the entries below `i` to the entries below `i + 1`. -/
theorem _root_.Aeneas.Std.Slice.forall_lt_succ_set {α : Type} [Inhabited α] {P : ℕ → α → Prop}
    {s : Slice α} {i : Usize} {x : α} (hs : ∀ k < i.val, P k s[k]!) (hx : P i.val x)
    (hi : i.val < s.length) :
    ∀ k < i.val + 1, P k (s.set i x)[k]! := by
  intro k hk
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
  · rw [Slice.getElem!_Nat_set_ne _ _ _ _ (Nat.ne_of_gt h)]
    exact hs k h
  · rw [Slice.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, hi⟩]
    exact hx

/-- Setting entry `k1 = k - 1` keeps the entries below `k1` and extends a property of the entries
from `k` on to the entries from `k1` on. -/
theorem _root_.Aeneas.Std.Slice.forall_ge_pred_set {α : Type} [Inhabited α] {P : ℕ → α → Prop}
    {s : Slice α} {k1 : Usize} {x : α} {k m : ℕ} (hkk : k1.val + 1 = k) (hk1 : k1.val < s.length)
    (hh : ∀ j < m, k ≤ j → P j s[j]!) (hx : P k1.val x) :
    (∀ j < k1.val, (s.set k1 x)[j]! = s[j]!) ∧ ∀ j < m, k1.val ≤ j → P j (s.set k1 x)[j]! := by
  refine ⟨fun j hj => Slice.getElem!_Nat_set_ne _ _ _ _ (Nat.ne_of_gt hj), fun j hj hkj => ?_⟩
  rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
  · rw [Slice.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, hk1⟩]
    exact hx
  · rw [Slice.getElem!_Nat_set_ne _ _ _ _ (Nat.ne_of_lt hlt)]
    exact hh j hj (hkk ▸ hlt)

/-- Indexing an array with `..` (`RangeFull`) gives the whole array as a slice. -/
@[step]
theorem index_rangeFull_spec {T : Type} {N : Usize} (a : Array T N) :
    core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFullSlice T))
      a () ⦃ (s : Slice T) => s = a.to_slice ⦄ := by
  simp [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index]

end Aeneas.Std.Array
