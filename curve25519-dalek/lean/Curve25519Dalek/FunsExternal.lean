/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Zhang-Liao, Alessandro D'Angelo,
  Hoang Le Truong, Markus Ferdinand Dablander
-/
-- [curve25519_dalek]: external functions.
module
public import Aeneas
public import Curve25519Dalek.Types
public import Subtle.Contract
public import Zeroize.Contract
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open Curve25519Dalek

/-- [alloc::vec::{impl core::iter::traits::collect::IntoIterator<&'a T, core::slice::iter::Iter<'a,
    T>> for &'a alloc::vec::Vec<T>}::into_iter]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 4088:4-4088:40
    Name pattern: [alloc::vec::{core::iter::traits::collect::IntoIterator<&'a
    alloc::vec::Vec<@T>, &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter]
    Visibility: public -/
@[rust_fun
  "alloc::vec::{core::iter::traits::collect::IntoIterator<&'a alloc::vec::Vec<@T>, &'a @T, \
    core::slice::iter::Iter<'a, @T>>}::into_iter"]
opaque SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
  {T : Type} (A : Type) : alloc.vec.Vec T → Result (core.slice.iter.Iter T)

/-! ## Contracts

The behaviour of the `opaque` function above, as stated in the Rust standard library
documentation: a predicate `….Contract : Prop`, and one axiom (`RustAx.alloc`) stating it. The
axiom is the only trusted addition of this file; the theorem `…_spec` used by the proofs is its
projection. -/

/-- `<&Vec<T> as IntoIterator>::into_iter` (alloc/src/vec/mod.rs,
`impl<'a, T, A: Allocator> IntoIterator for &'a Vec<T, A>`): "Creates an iterator from a value."
Body: `self.iter()`, the slice iterator over the vector's elements, starting at index `0`; never
fails. `A` is the allocator type parameter. -/
@[nolint defsWithUnderscore]
def SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter.Contract : Prop :=
  ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T),
    SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter A v ⦃
      (it : core.slice.iter.Iter T) => it = ⟨v.deref, 0⟩ ⦄

/-- The specification of the `alloc` functions used: one field per function, the predicates
above. -/
structure alloc.Contract : Prop where
  sharedVec_into_iter :
    SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter.Contract

/-- The single trusted assumption about `alloc`: its functions meet their contracts. -/
axiom RustAx.alloc : alloc.Contract

/-- `SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter` meets its contract
(`RustAx.alloc`). -/
@[step]
theorem SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter_spec {T : Type}
    (A : Type) (v : alloc.vec.Vec T) :
    SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter A v ⦃
      (it : core.slice.iter.Iter T) => it = ⟨v.deref, 0⟩ ⦄ :=
  RustAx.alloc.sharedVec_into_iter A v

/-! ## Specs of the library functions modelled by Aeneas

`core::array::from_fn`, `Result::map`, `usize::div_ceil`,
`<&mut [T; N] as IntoIterator>::into_iter`, `<T as Borrow<T>>::borrow` and `Vec::is_empty` are
defined in Aeneas's standard library; these are their specs in the form the proofs use, proved
from those definitions. -/

/-- `core::array::from_fn`: element `i` satisfies `post i`, for a closure with state invariant
`inv`. -/
theorem core.array.from_fn_spec {T F : Type} (N : Std.Usize)
    (inst : core.ops.function.FnMut F Std.Usize T) (f : F)
    (inv : ℕ → F → Prop) (post : ℕ → T → Prop) (h0 : inv 0 f)
    (h : ∀ (i : Std.Usize) (g : F), i.val < N.val → inv i.val g →
      inst.call_mut g i ⦃ (x : T) (g' : F) => post i.val x ∧ inv (i.val + 1) g' ⦄) :
    core.array.from_fn N inst f ⦃ (a : Array T N) =>
      ∀ (i : ℕ) (hi : i < a.val.length), post i a.val[i] ⦄ :=
  core.array.from_fn.spec N inst f inv post h0 h

/-- `Result::map`: `Ok x` becomes `Ok` of the closure's result, `Err e` stays, for a closure that
succeeds on the `Ok` value. -/
theorem core.result.Result.map_spec {T E U F : Type} (inst : core.ops.function.FnOnce F T U)
    (r : core.result.Result T E) (f : F)
    (h : ∀ x, r = .Ok x → ∃ y, inst.call_once f x = ok y) :
    core.result.Result.map inst r f ⦃ (r' : core.result.Result U E) =>
      (∀ x, r = .Ok x → ∃ y, inst.call_once f x = ok y ∧ r' = .Ok y) ∧
      (∀ e, r = .Err e → r' = .Err e) ⦄ := by
  cases r with
  | Ok x =>
    obtain ⟨y, hy⟩ := h x rfl
    simp [core.result.Result.map, hy]
  | Err e => simp [core.result.Result.map]

/-- `usize::div_ceil`: the quotient rounded up, for a nonzero divisor. -/
@[step]
theorem core.num.Usize.div_ceil_spec (self rhs : Std.Usize) (hrhs : rhs.val ≠ 0) :
    core.num.Usize.div_ceil self rhs ⦃ (r : Std.Usize) =>
      r.val = (self.val + rhs.val - 1) / rhs.val ⦄ := by
  unfold core.num.Usize.div_ceil
  exact UScalar.div_ceil.spec self rhs hrhs

/-- `<&mut [T; N] as IntoIterator>::into_iter`: an iterator over the whole array from index `0`;
the backward function writes the iterator's slice back. -/
@[step]
theorem MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec {T : Type}
    {N : Std.Usize} (a : Array T N) :
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter a ⦃
      (it : core.slice.iter.IterMut T) (back : core.slice.iter.IterMut T → Array T N) =>
      it.slice.val = a.val ∧ it.i = 0 ∧
      ∀ it' : core.slice.iter.IterMut T, it'.slice.length = N.val →
        (back it').val = it'.slice.val ⦄ :=
  core.slice.MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter.spec a

/-- `<T as Borrow<T>>::borrow`: returns its argument. -/
@[step]
theorem core.borrow.Borrow.Blanket.borrow_spec {T : Type} (x : T) :
    core.borrow.Borrow.Blanket.borrow x ⦃ (y : T) => y = x ⦄ :=
  core.borrow.Borrow.Blanket.borrow.spec x

/-- `Vec::is_empty`: `true` iff the vector has no elements. -/
@[step]
theorem alloc.vec.Vec.is_empty_spec {T : Type} (v : alloc.vec.Vec T) :
    alloc.vec.Vec.is_empty v ⦃ (b : Bool) => b = decide (v.length = 0) ⦄ := by
  simp [alloc.vec.Vec.is_empty]
