/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ForHumans.Specs.External.Zeroize.Contract
@[expose] public section
set_option linter.style.whitespace false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek

/-! # The contracts of `zeroize`, as theorems

Each contract of `ForHumans/Specs/External/Zeroize/Contract.lean`, as the theorem that the proofs
use: its projection from the axiom `RustAx.zeroize`. -/

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
