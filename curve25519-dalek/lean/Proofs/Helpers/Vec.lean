/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Aeneas.Std.Alloc.Vec
public section

/-! # Lemmas about Aeneas vectors

The entries of a vector after `push` (in the form of `Vec.push_spec`'s postcondition), described
with `getElem!`. -/

open Aeneas Aeneas.Std

namespace Aeneas.Std.alloc.vec.Vec

variable {α : Type}

theorem length_of_val_eq_append {v v1 : Vec α} {x : α} (h : v1.val = v.val ++ [x]) :
    v1.length = v.length + 1 := by
  rw [Vec.length, h, List.length_append, List.length_singleton]

variable [Inhabited α]

theorem getElem!_of_val_eq_append_of_lt {v v1 : Vec α} {x : α} (h : v1.val = v.val ++ [x])
    {k : ℕ} (hk : k < v.length) : v1[k]! = v[k]! := by
  rw [Vec.getElem!_Nat_eq, Vec.getElem!_Nat_eq, h, List.getElem!_eq_getElem?_getD,
    List.getElem!_eq_getElem?_getD, List.getElem?_append_left hk]

theorem getElem!_of_val_eq_append_length {v v1 : Vec α} {x : α} (h : v1.val = v.val ++ [x]) :
    v1[v.length]! = x := by
  rw [Vec.getElem!_Nat_eq, h, List.getElem!_eq_getElem?_getD,
    List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

theorem getElem!_slice (v : Vec α) (k : ℕ) : v.slice[k]! = v[k]! := by
  rw [Vec.getElem!_Nat_eq, Slice.getElem!_Nat_eq]
  rfl

theorem getElem!_mk (s : Slice α) (k : ℕ) : ({ slice := s } : Vec α)[k]! = s[k]! := by
  rw [Vec.getElem!_Nat_eq, Slice.getElem!_Nat_eq]
  rfl

/-- Pushing `x` extends a property of the entries below the length to the new entry. -/
theorem forall_lt_of_val_eq_append {P : ℕ → α → Prop} {v v1 : Vec α} {x : α}
    (h : v1.val = v.val ++ [x]) (hv : ∀ k < v.length, P k v[k]!) (hx : P v.length x) :
    ∀ k < v.length + 1, P k v1[k]! := by
  intro k hk
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
  · rw [getElem!_of_val_eq_append_of_lt h hlt]
    exact hv k hlt
  · rw [getElem!_of_val_eq_append_length h]
    exact hx

end Aeneas.Std.alloc.vec.Vec
