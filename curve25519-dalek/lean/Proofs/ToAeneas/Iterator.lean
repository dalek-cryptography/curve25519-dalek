/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Aeneas.Std.Core.Iter
public import Aeneas.Std.WP
public import Aeneas.Std.Alloc.Vec.IntoIter
public section

/-! # Finite iterators (staged for Aeneas)

Specs of functions that consume a generic iterator (`Product`, `Sum`) assume that it yields a
given list of items and then stops. `Yields` lives in the namespace of Aeneas's `Iterator`, so
that it can be written `iterInst.Yields`. Functions that take an `IntoIterator` (the multiscalar
multiplications) assume that `into_iter` returns such an iterator (`IntoIterator.Yields`).

`Yields` is not vacuous: the iterator over a list yields that list (`ofList_yields`), and so does
`Vec::into_iter` (`IntoIteratorVec_yields`).

Staged here for upstreaming to Aeneas: it depends only on Aeneas's model of Rust iterators. -/

open Aeneas Aeneas.Std Aeneas.Std.WP

/-- Calling `next` repeatedly, starting from `it`, returns the items `xs` in order, then `none`. -/
inductive Aeneas.Std.core.iter.traits.iterator.Iterator.Yields {I T : Type}
    (inst : core.iter.traits.iterator.Iterator I T) : I → List T → Prop
  | nil {it : I} :
      inst.next it ⦃ (o : Option T) (_ : I) => o = none ⦄ → Yields inst it []
  | cons {it it' : I} {x : T} {xs : List T} :
      inst.next it ⦃ (o : Option T) (it1 : I) => o = some x ∧ it1 = it' ⦄ →
      Yields inst it' xs → Yields inst it (x :: xs)

/-- `into_iter x` returns an iterator that yields the items `xs` in order, then stops. -/
@[expose] def Aeneas.Std.core.iter.traits.collect.IntoIterator.Yields {S T I : Type}
    (inst : core.iter.traits.collect.IntoIterator S T I) (x : S) (xs : List T) : Prop :=
  inst.into_iter x ⦃ (it : I) => inst.iteratorInst.Yields it xs ⦄

namespace Aeneas.Std.core.iter.traits.iterator.Iterator

/-- The iterator over a list: its state is the list of remaining items. -/
def ofList (T : Type) : core.iter.traits.iterator.Iterator (List T) T where
  next l := Result.ok (l.head?, l.tail)

/-- The list iterator yields its list. -/
theorem ofList_yields {T : Type} (l : List T) : (ofList T).Yields l l := by
  induction l with
  | nil => exact .nil (by simp [ofList, spec_ok])
  | cons x xs ih => exact .cons (by simp [ofList, spec_ok]) ih

end Aeneas.Std.core.iter.traits.iterator.Iterator

namespace Aeneas.Std.core.iter.traits.collect

/-- The iterator of a vector yields its entries. -/
theorem IteratorVecIntoIter_yields {T : Type} (l : List T) (v : alloc.vec.Vec T)
    (hv : v.val = l) :
    (core.iter.traits.iterator.IteratorVecIntoIter T).Yields v l := by
  induction l generalizing v with
  | nil =>
    refine .nil ?_
    change alloc.vec.into_iter.IteratorIntoIter.next v ⦃ _ => _ ⦄
    unfold alloc.vec.into_iter.IteratorIntoIter.next
    split
    · simp only [WP.spec_ok]
      rfl
    · rename_i h; rw [hv] at h; cases h
  | cons x xs ih =>
    have hlen : xs.length ≤ Usize.max := by
      have := v.property; rw [hv] at this; simp at this; omega
    refine .cons (it' := alloc.vec.Vec.from xs hlen) ?_ (ih _ (alloc.vec.Vec.from_val xs hlen))
    change alloc.vec.into_iter.IteratorIntoIter.next v ⦃ _ => _ ⦄
    unfold alloc.vec.into_iter.IteratorIntoIter.next
    split
    · rename_i h; rw [hv] at h; cases h
    · rename_i hd tl h
      rw [hv] at h
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      simp only [WP.spec_ok]
      exact ⟨rfl, rfl⟩

/-- `Vec::into_iter` yields the entries of the vector. -/
theorem IntoIteratorVec_yields {T : Type} (v : alloc.vec.Vec T) :
    (IntoIteratorVec T).Yields v v.val := by
  change alloc.vec.IntoIteratorVec.into_iter v ⦃ _ => _ ⦄
  unfold alloc.vec.IntoIteratorVec.into_iter
  exact (WP.spec_ok
    (p := fun it => (core.iter.traits.iterator.IteratorVecIntoIter T).Yields it v.val) v).mpr
    (IteratorVecIntoIter_yields v.val v rfl)

end Aeneas.Std.core.iter.traits.collect
