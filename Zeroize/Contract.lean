/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Zhang-Liao, Alessandro D'Angelo, Hoang Le Truong,
  Markus Ferdinand Dablander
-/
module
public import Curve25519Dalek.Types
@[expose] public section
set_option linter.style.whitespace false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek

/-! # Functions of the `zeroize` crate (zeroize-1.8.2)

This file is the trusted base for `zeroize`.

* Signatures: Each external function that Aeneas expects is an `opaque` constant with the
  required name, type and `@[rust_fun]` attribute.
* Contracts: Each function used by the proofs has one predicate `….Contract : Prop` that restates
  the Rust documentation. Specs that call trait methods of a generic `Z` assume the behaviour of
  those methods as a hypothesis.
* Axiom: The single axiom `RustAx.zeroize` states that all the contracts hold.
-/

set_option linter.dupNamespace false in
/-- [zeroize::{impl zeroize::Zeroize for Z}::zeroize]:
    Source: 'zeroize-1.8.2/src/lib.rs', lines 301:4-301:25
    Name pattern: [zeroize::{zeroize::Zeroize<@Z>}::zeroize] -/
@[rust_fun "zeroize::{zeroize::Zeroize<@Z>}::zeroize"]
opaque zeroize.Zeroize.Blanket.zeroize
  {Z : Type} (DefaultIsZeroesInst : zeroize.DefaultIsZeroes Z) : Z → Result Z

set_option linter.dupNamespace false in
/-- "Marker trait for types whose [`Default`] is the desired zeroization result" (lib.rs:281).
Body (lib.rs:301-304): `volatile_write(self, Z::default()); atomic_fence();`. The result is
exactly `Z::default()` (including its failure, if `default` fails). -/
def zeroize.Zeroize.Blanket.zeroize.Contract : Prop :=
  ∀ {Z : Type} (inst : zeroize.DefaultIsZeroes Z) (x : Z),
    zeroize.Zeroize.Blanket.zeroize inst x = inst.coredefaultDefaultInst.default

/-- [zeroize::{impl zeroize::Zeroize for [Z; N]}::zeroize]:
    Source: 'zeroize-1.8.2/src/lib.rs', lines 373:4-373:25
    Name pattern: [zeroize::{zeroize::Zeroize<[@Z; @N]>}::zeroize] -/
@[rust_fun "zeroize::{zeroize::Zeroize<[@Z; @N]>}::zeroize"]
opaque Array.Insts.ZeroizeZeroize.zeroize
  {Z : Type} {N : Std.Usize} (ZeroizeInst : zeroize.Zeroize Z) :
  Array Z N → Result (Array Z N)

/-- "Impl [`Zeroize`] on arrays of types that impl [`Zeroize`]." (lib.rs:368). Body
(lib.rs:373-375): `self.iter_mut().zeroize();`. Every element is zeroized, so each element of
the result satisfies any postcondition that the element `zeroize` guarantees. -/
def Array.Insts.ZeroizeZeroize.zeroize.Contract : Prop :=
  ∀ {Z : Type} {N : Std.Usize} (inst : zeroize.Zeroize Z) (a : Array Z N) {post : Z → Prop}
    (h : ∀ x ∈ a.val, inst.zeroize x ⦃ post ⦄),
    Array.Insts.ZeroizeZeroize.zeroize inst a ⦃ a' => ∀ y ∈ a'.val, post y ⦄

/-- [zeroize::{impl zeroize::Zeroize for core::slice::iter::IterMut<'_0, Z>}::zeroize]:
    Source: 'zeroize-1.8.2/src/lib.rs', lines 385:4-385:25
    Name pattern: [zeroize::{zeroize::Zeroize<core::slice::iter::IterMut<'0, @Z>>}::zeroize] -/
@[rust_fun
  "zeroize::{zeroize::Zeroize<core::slice::iter::IterMut<'0, @Z>>}::zeroize"]
opaque core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize
  {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
  core.slice.iter.IterMut Z → Result ((core.slice.iter.IterMut Z) ×
    (core.slice.iter.IterMut Z → core.slice.iter.IterMut Z))

/-- Body (lib.rs:385-389): `for elem in self { elem.zeroize(); }`. Every element the iterator has
not yet yielded (indices `it.i ..`) is zeroized, and the already-yielded prefix is unchanged.
The iterator ends exhausted. The zeroized slice is returned in the new iterator, so the
backward function (ending the `'0` borrow) is the identity. -/
def core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize.Contract : Prop :=
  ∀ {Z : Type} (inst : zeroize.Zeroize Z) (it : core.slice.iter.IterMut Z) {post : Z → Prop}
    (h : ∀ x ∈ it.slice.val.drop it.i, inst.zeroize x ⦃ post ⦄),
    core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize inst it ⦃ it' back =>
      back = id ∧ it'.i = it.slice.length ∧ it'.slice.length = it.slice.length ∧
      it'.slice.val.take it.i = it.slice.val.take it.i ∧
      ∀ y ∈ it'.slice.val.drop it.i, post y ⦄

/-- [zeroize::{impl zeroize::Zeroize for alloc::vec::Vec<Z>}::zeroize]:
    Source: 'zeroize-1.8.2/src/lib.rs', lines 551:4-551:25
    Name pattern: [zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize] -/
@[rust_fun "zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize"]
opaque alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
  {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
  alloc.vec.Vec Z → Result (alloc.vec.Vec Z)

/-- "\"Best effort\" zeroization for `Vec`. Ensures the entire capacity of the `Vec` is zeroed.
Cannot ensure that previous reallocations did not leave values on the heap." (lib.rs:547-550).
Body (lib.rs:551-560): zeroize the elements, `self.clear()`, zeroize the spare capacity.
Aeneas' `Vec` has no capacity, so the observable result is the empty vector. Only the success
of the element `zeroize` matters. -/
def alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize.Contract : Prop :=
  ∀ {Z : Type} (inst : zeroize.Zeroize Z) (v : alloc.vec.Vec Z)
    (h : ∀ x ∈ v.val, inst.zeroize x ⦃ _ => True ⦄),
    alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize inst v ⦃ v' => v' = alloc.vec.Vec.new Z ⦄

/-! ## The specification of the crate -/

/-- The specification of `zeroize`: one field per function, the predicates above. -/
structure zeroize.Contract : Prop where
  blanket_zeroize : zeroize.Zeroize.Blanket.zeroize.Contract
  array_zeroize : Array.Insts.ZeroizeZeroize.zeroize.Contract
  iterMut_zeroize : core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize.Contract
  vec_zeroize : alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize.Contract

/-- The single trusted assumption about `zeroize`: its functions meet their contracts. -/
axiom RustAx.zeroize : zeroize.Contract

/-- `zeroize.Zeroize.Blanket.zeroize` meets its contract (`RustAx.zeroize`). -/
theorem zeroize.Zeroize.Blanket.zeroize_eq
    {Z : Type} (inst : zeroize.DefaultIsZeroes Z) (x : Z) :
    zeroize.Zeroize.Blanket.zeroize inst x = inst.coredefaultDefaultInst.default :=
  RustAx.zeroize.blanket_zeroize inst x

/-- `Array.Insts.ZeroizeZeroize.zeroize` meets its contract (`RustAx.zeroize`). -/
theorem Array.Insts.ZeroizeZeroize.zeroize_spec
    {Z : Type} {N : Std.Usize} (inst : zeroize.Zeroize Z) (a : Array Z N) {post : Z → Prop}
    (h : ∀ x ∈ a.val, inst.zeroize x ⦃ post ⦄) :
    Array.Insts.ZeroizeZeroize.zeroize inst a ⦃ a' => ∀ y ∈ a'.val, post y ⦄ :=
  RustAx.zeroize.array_zeroize inst a h

/-- `core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize`
meets its contract (`RustAx.zeroize`). -/
theorem core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize_spec
    {Z : Type} (inst : zeroize.Zeroize Z) (it : core.slice.iter.IterMut Z) {post : Z → Prop}
    (h : ∀ x ∈ it.slice.val.drop it.i, inst.zeroize x ⦃ post ⦄) :
    core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize inst it ⦃ it' back =>
      back = id ∧ it'.i = it.slice.length ∧ it'.slice.length = it.slice.length ∧
      it'.slice.val.take it.i = it.slice.val.take it.i ∧
      ∀ y ∈ it'.slice.val.drop it.i, post y ⦄ :=
  RustAx.zeroize.iterMut_zeroize inst it h

/-- `alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize` meets its contract (`RustAx.zeroize`). -/
@[step]
theorem alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_spec
    {Z : Type} (inst : zeroize.Zeroize Z) (v : alloc.vec.Vec Z)
    (h : ∀ x ∈ v.val, inst.zeroize x ⦃ _ => True ⦄) :
    alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize inst v ⦃ v' => v' = alloc.vec.Vec.new Z ⦄ :=
  RustAx.zeroize.vec_zeroize inst v h
