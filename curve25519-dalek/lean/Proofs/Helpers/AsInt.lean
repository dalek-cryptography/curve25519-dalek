/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.Array
import Proofs.Helpers.Array
import Aeneas.Tactic.Misc.FCongr.FCongr
public section

/-! # Lemmas about `Array.asInt` -/

open Aeneas Aeneas.Std

namespace Aeneas.Std.Array

/-- `asInt` as a weighted sum of the digits. -/
theorem asInt_eq_sum {ty : IScalarTy} {n : Usize} (bits : ℕ) (a : Array (IScalar ty) n) :
    a.asInt bits = ∑ i ∈ Finset.range n.val, 2 ^ (bits * i) * a[i]!.val := by
  have h : a.val.length = n.val := by simp
  simp only [Array.asInt_def, Array.getElem!_Nat_eq]
  rw [← h]
  generalize a.val = l
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.map_cons, List.foldr_cons, ih, List.getElem!_cons_succ, List.getElem!_cons_zero,
      Finset.mul_sum]
    rw [Nat.mul_zero, pow_zero, one_mul, add_comm]
    fcongr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.mul_succ, pow_add]
    ring

/-- Setting digit `k` changes `asInt` by the change of the digit, weighted by `2 ^ (bits * k)`. -/
theorem asInt_set {ty : IScalarTy} {n : Usize} (bits : ℕ) (a : Array (IScalar ty) n) (k : Usize)
    (x : IScalar ty) (hk : k.val < n.val) :
    (a.set k x).asInt bits = a.asInt bits + 2 ^ (bits * k.val) * (x.val - a[k.val]!.val) := by
  have hmem : k.val ∈ Finset.range n.val := Finset.mem_range.mpr hk
  rw [asInt_eq_sum, asInt_eq_sum, ← Finset.add_sum_erase _ _ hmem,
    ← Finset.add_sum_erase _ _ hmem,
    Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by simpa using hk⟩]
  have hrest : ∑ j ∈ (Finset.range n.val).erase k.val, 2 ^ (bits * j) * (a.set k x)[j]!.val
      = ∑ j ∈ (Finset.range n.val).erase k.val, 2 ^ (bits * j) * a[j]!.val :=
    Finset.sum_congr rfl fun j hj => by
      rw [Array.getElem!_Nat_set_ne _ _ _ _ (Ne.symm (Finset.ne_of_mem_erase hj))]
  rw [hrest]
  ring

/-- An array of zero digits has value `0`. -/
theorem asInt_repeat_zero {ty : IScalarTy} {n : Usize} (bits : ℕ) (z : IScalar ty)
    (hz : z.val = 0) :
    (Array.repeat n z).asInt bits = 0 := by
  rw [asInt_eq_sum]
  exact Finset.sum_eq_zero fun j hj => by
    rw [getElem!_repeat z (Finset.mem_range.mp hj), hz, mul_zero]

end Aeneas.Std.Array
