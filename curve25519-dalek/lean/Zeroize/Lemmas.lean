/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Zeroize.Contract
@[expose] public section
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek

/-! # Derived results for `zeroize` (no axioms)

Specs for the common case where the element `zeroize` always returns the same value `z`. These are
not `@[step]`: `z` does not appear in the call, so `step` cannot infer it. Use them with
`step with … (z := …)`, or through the concrete `@[step]` lemmas in `Zeroize/Instances.lean`.
-/

/-- Zeroizing an `IterMut` whose element `zeroize` always returns `z` keeps the yielded prefix,
replaces the rest by `z` and exhausts the iterator. -/
theorem core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize_const_spec
    {Z : Type} (inst : zeroize.Zeroize Z) (z : Z) (hz : ∀ x, inst.zeroize x ⦃ r => r = z ⦄)
    (it : core.slice.iter.IterMut Z) :
    core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize inst it ⦃ it' back =>
      it'.slice.val = it.slice.val.take it.i ++ List.replicate (it.slice.length - it.i) z ∧
      it'.i = it.slice.length ∧ back = id ⦄ := by
  apply spec_mono (core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize_spec inst it
    (post := (· = z)) (fun x _ => hz x))
  rintro ⟨it', back⟩ ⟨hback, hi, hlen, htake, hdrop⟩
  refine ⟨?_, hi, hback⟩
  have hlen' : it'.slice.val.length = it.slice.val.length := by
    simpa [Slice.length] using hlen
  rw [← List.take_append_drop it.i it'.slice.val, htake]
  fcongr 1
  exact List.eq_replicate_iff.mpr ⟨by simp [Slice.length, hlen'], hdrop⟩

/-- Zeroizing an array whose element `zeroize` always returns `z` gives `[z; N]`. -/
theorem Array.Insts.ZeroizeZeroize.zeroize_const_spec
    {Z : Type} {N : Std.Usize} (inst : zeroize.Zeroize Z) (z : Z)
    (hz : ∀ x, inst.zeroize x ⦃ r => r = z ⦄) (a : Array Z N) :
    Array.Insts.ZeroizeZeroize.zeroize inst a ⦃ a' => a' = Array.repeat N z ⦄ := by
  apply spec_mono
    (Array.Insts.ZeroizeZeroize.zeroize_spec inst a (post := (· = z)) (fun x _ => hz x))
  intro a' h
  apply Aeneas.Std.Array.ext
  simp only [Array.repeat_val]
  exact List.eq_replicate_iff.mpr ⟨a'.property, h⟩
