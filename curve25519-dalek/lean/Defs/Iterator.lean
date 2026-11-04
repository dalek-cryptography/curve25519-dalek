/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Aeneas.Std.Core.Iter
public import Aeneas.Std.WP
public section

/-! # Finite iterators (audited)

Specs of functions that consume a generic iterator (`Product`, `Sum`) assume that it yields a
given list of items and then stops. `Yields` lives in the namespace of Aeneas's `Iterator`, so
that it can be written `iterInst.Yields`. Functions that take an `IntoIterator` (the multiscalar
multiplications) assume that `into_iter` returns such an iterator (`IntoIterator.Yields`).
`Proofs/Helpers/Iterator.lean` shows that `Yields` holds for a concrete iterator. -/

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
