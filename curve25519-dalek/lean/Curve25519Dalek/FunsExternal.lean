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

/-- [core::array::from_fn]:
    Source: '/rustc/library/core/src/array/mod.rs', lines 110:0-112:52
    Name pattern: [core::array::from_fn]
    Visibility: public -/
@[rust_fun "core::array::from_fn"]
opaque core.array.from_fn
  {T : Type} {F : Type} (N : Std.Usize) (opsfunctionFnMutFTupleUsizeTInst :
  core.ops.function.FnMut F Std.Usize T) :
  F → Result (Array T N)

/-- [core::array::{impl core::iter::traits::collect::IntoIterator<&'a mut T,
    core::slice::iter::IterMut<'a, T>> for &'a mut [T; N]}::into_iter]:
    Source: '/rustc/library/core/src/array/mod.rs', lines 376:4-376:40
    Name pattern: [core::array::{core::iter::traits::collect::IntoIterator<&'a mut [@T; @N],
    &'a mut @T, core::slice::iter::IterMut<'a, @T>>}::into_iter]
    Visibility: public -/
@[rust_fun
  "core::array::{core::iter::traits::collect::IntoIterator<&'a mut [@T; @N], &'a mut @T, \
    core::slice::iter::IterMut<'a, @T>>}::into_iter"]
opaque MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
  {T : Type} {N : Std.Usize} :
  Array T N → Result ((core.slice.iter.IterMut T) × (core.slice.iter.IterMut
    T → Array T N))

/-- [core::num::{usize}::div_ceil]:
    Source: '/rustc/library/core/src/num/uint_macros.rs', lines 3787:8-3787:54
    Name pattern: [core::num::{usize}::div_ceil]
    Visibility: public -/
@[rust_fun "core::num::{usize}::div_ceil"]
opaque core.num.Usize.div_ceil : Std.Usize → Std.Usize → Result Std.Usize

/-- [core::result::{core::result::Result<T, E>}::map]:
    Source: '/rustc/library/core/src/result.rs', lines 832:4-834:53
    Name pattern: [core::result::{core::result::Result<@T, @E>}::map]
    Visibility: public -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map"]
opaque core.result.Result.map
  {T : Type} {E : Type} {U : Type} {F : Type} (opsfunctionFnOnceFTupleTUInst :
  core.ops.function.FnOnce F T U) :
  core.result.Result T E → F → Result (core.result.Result U E)

/-- [alloc::vec::{alloc::vec::Vec<T>}::is_empty]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 3125:4-3125:40
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::is_empty]
    Visibility: public -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::is_empty"]
opaque alloc.vec.Vec.is_empty
  {T : Type} (A : Type) : alloc.vec.Vec T → Result Bool

/-- [core::borrow::{impl core::borrow::Borrow<T> for T}::borrow]:
    Source: '/rustc/library/core/src/borrow.rs', lines 214:4-214:26
    Name pattern: [core::borrow::{core::borrow::Borrow<@T, @T>}::borrow]
    Visibility: public -/
@[rust_fun "core::borrow::{core::borrow::Borrow<@T, @T>}::borrow"]
opaque core.borrow.Borrow.Blanket.borrow {T : Type} : T → Result T

/-! ## Contracts

The behaviour of the `opaque` functions above, as stated in the Rust standard library
documentation: one predicate `….Contract : Prop` per function, and one axiom per crate
(`RustAx.core`, `RustAx.alloc`) stating all of them. The axioms are the only trusted
additions of this file; the theorems `…_spec` used by the proofs are their projections. -/

/-- `core::array::from_fn`: "Creates an array of type `[T; N]`, where each element `T` is the
returned value from `cb` using that element's index." The closure is called on the indices
`0, 1, …, N-1` in order, each call receiving the closure state left by the previous one. Stated
with an invariant `inv` on the closure state and a property `post` of each element. -/
@[nolint defsWithUnderscore]
def core.array.from_fn.Contract : Prop :=
  ∀ {T F : Type} (N : Std.Usize) (inst : core.ops.function.FnMut F Std.Usize T) (f : F)
    (inv : ℕ → F → Prop) (post : ℕ → T → Prop) (h0 : inv 0 f)
    (h : ∀ (i : Std.Usize) (g : F), i.val < N.val → inv i.val g →
      inst.call_mut g i ⦃ (x : T) (g' : F) => post i.val x ∧ inv (i.val + 1) g' ⦄),
    core.array.from_fn N inst f ⦃ (a : Array T N) =>
      ∀ (i : ℕ) (hi : i < a.val.length), post i a.val[i] ⦄

/-- `Result::map` (core/src/result.rs): "Maps a `Result<T, E>` to `Result<U, E>` by applying a
function to a contained `Ok` value, leaving an `Err` value untouched." Conditional on the closure
succeeding on the `Ok` value. -/
def core.result.Result.map.Contract : Prop :=
  ∀ {T E U F : Type} (inst : core.ops.function.FnOnce F T U) (r : core.result.Result T E) (f : F)
    (h : ∀ x, r = .Ok x → ∃ y, inst.call_once f x = ok y),
    core.result.Result.map inst r f ⦃ (r' : core.result.Result U E) =>
      (∀ x, r = .Ok x → ∃ y, inst.call_once f x = ok y ∧ r' = .Ok y) ∧
      (∀ e, r = .Err e → r' = .Err e) ⦄

/-- `usize::div_ceil` (core/src/num/uint_macros.rs): "Calculates the quotient of `self` and `rhs`,
rounding the result towards positive infinity. Panics if `rhs` is zero." -/
@[nolint defsWithUnderscore]
def core.num.Usize.div_ceil.Contract : Prop :=
  ∀ (self rhs : Std.Usize) (hrhs : rhs.val ≠ 0),
    core.num.Usize.div_ceil self rhs ⦃ (r : Std.Usize) =>
      r.val = (self.val + rhs.val - 1) / rhs.val ⦄

/-- `<&mut [T; N] as IntoIterator>::into_iter`: a mutable iterator over the whole array, starting
at index `0`; the backward function writes the iterator's slice back into the array. -/
@[nolint defsWithUnderscore]
def MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter.Contract : Prop :=
  ∀ {T : Type} {N : Std.Usize} (a : Array T N),
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter a ⦃
      (it : core.slice.iter.IterMut T) (back : core.slice.iter.IterMut T → Array T N) =>
      it.slice.val = a.val ∧ it.i = 0 ∧
      ∀ it' : core.slice.iter.IterMut T, it'.slice.length = N.val →
        (back it').val = it'.slice.val ⦄

/-- `Vec::is_empty` (alloc/src/vec/mod.rs): "Returns `true` if the vector contains no elements."
Body: `self.len() == 0`; never fails. `A` is the allocator type parameter. -/
@[nolint defsWithUnderscore]
def alloc.vec.Vec.is_empty.Contract : Prop :=
  ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T),
    alloc.vec.Vec.is_empty A v ⦃ (b : Bool) => b = decide (v.length = 0) ⦄

/-- `<T as Borrow<T>>::borrow` (core/src/borrow.rs, `impl<T: ?Sized> Borrow<T> for T`): "Immutably
borrows from an owned value." Body: `self`; never fails. -/
@[nolint defsWithUnderscore]
def core.borrow.Borrow.Blanket.borrow.Contract : Prop :=
  ∀ {T : Type} (x : T), core.borrow.Borrow.Blanket.borrow x ⦃ (y : T) => y = x ⦄

/-- The specification of the `core` functions used: one field per function, the predicates
above. -/
structure core.Contract : Prop where
  array_from_fn : core.array.from_fn.Contract
  result_map : core.result.Result.map.Contract
  usize_div_ceil : core.num.Usize.div_ceil.Contract
  mutArray_into_iter :
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter.Contract
  borrow_blanket : core.borrow.Borrow.Blanket.borrow.Contract

/-- The single trusted assumption about `core`: its functions meet their contracts. -/
axiom RustAx.core : core.Contract

/-- The specification of the `alloc` functions used: one field per function, the predicates
above. -/
structure alloc.Contract : Prop where
  vec_is_empty : alloc.vec.Vec.is_empty.Contract

/-- The single trusted assumption about `alloc`: its functions meet their contracts. -/
axiom RustAx.alloc : alloc.Contract

/-- `core.array.from_fn` meets its contract (`RustAx.core`). -/
theorem core.array.from_fn_spec {T F : Type} (N : Std.Usize)
    (inst : core.ops.function.FnMut F Std.Usize T) (f : F)
    (inv : ℕ → F → Prop) (post : ℕ → T → Prop) (h0 : inv 0 f)
    (h : ∀ (i : Std.Usize) (g : F), i.val < N.val → inv i.val g →
      inst.call_mut g i ⦃ (x : T) (g' : F) => post i.val x ∧ inv (i.val + 1) g' ⦄) :
    core.array.from_fn N inst f ⦃ (a : Array T N) =>
      ∀ (i : ℕ) (hi : i < a.val.length), post i a.val[i] ⦄ :=
  RustAx.core.array_from_fn N inst f inv post h0 h

/-- `core.result.Result.map` meets its contract (`RustAx.core`). -/
theorem core.result.Result.map_spec {T E U F : Type} (inst : core.ops.function.FnOnce F T U)
    (r : core.result.Result T E) (f : F)
    (h : ∀ x, r = .Ok x → ∃ y, inst.call_once f x = ok y) :
    core.result.Result.map inst r f ⦃ (r' : core.result.Result U E) =>
      (∀ x, r = .Ok x → ∃ y, inst.call_once f x = ok y ∧ r' = .Ok y) ∧
      (∀ e, r = .Err e → r' = .Err e) ⦄ :=
  RustAx.core.result_map inst r f h

/-- `core.num.Usize.div_ceil` meets its contract (`RustAx.core`). -/
@[step]
theorem core.num.Usize.div_ceil_spec (self rhs : Std.Usize) (hrhs : rhs.val ≠ 0) :
    core.num.Usize.div_ceil self rhs ⦃ (r : Std.Usize) =>
      r.val = (self.val + rhs.val - 1) / rhs.val ⦄ :=
  RustAx.core.usize_div_ceil self rhs hrhs

/-- `MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter`
meets its contract (`RustAx.core`). -/
@[step]
theorem MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter_spec {T : Type}
    {N : Std.Usize} (a : Array T N) :
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter a ⦃
      (it : core.slice.iter.IterMut T) (back : core.slice.iter.IterMut T → Array T N) =>
      it.slice.val = a.val ∧ it.i = 0 ∧
      ∀ it' : core.slice.iter.IterMut T, it'.slice.length = N.val →
        (back it').val = it'.slice.val ⦄ :=
  RustAx.core.mutArray_into_iter a

/-- `core.borrow.Borrow.Blanket.borrow` meets its contract (`RustAx.core`). -/
@[step]
theorem core.borrow.Borrow.Blanket.borrow_spec {T : Type} (x : T) :
    core.borrow.Borrow.Blanket.borrow x ⦃ (y : T) => y = x ⦄ :=
  RustAx.core.borrow_blanket x

/-- `alloc.vec.Vec.is_empty` meets its contract (`RustAx.alloc`). -/
@[step]
theorem alloc.vec.Vec.is_empty_spec {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    alloc.vec.Vec.is_empty A v ⦃ (b : Bool) => b = decide (v.length = 0) ⦄ :=
  RustAx.alloc.vec_is_empty A v

/-- Iterating over a shared vector uses its slice iterator. -/
@[rust_fun
  "alloc::vec::{core::iter::traits::collect::IntoIterator<&'a alloc::vec::Vec<@T>, &'a @T, \
    core::slice::iter::Iter<'a, @T>>}::into_iter"]
def SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
    {T : Type} (_A : Type) (v : alloc.vec.Vec T) : Result (core.slice.iter.Iter T) :=
  core.slice.Slice.iter v.deref
