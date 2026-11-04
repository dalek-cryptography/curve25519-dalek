/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Edwards.Basic
public import Proofs.Helpers.Naf
public section

/-! # Lemmas for `VartimePrecomputedStraus::optional_mixed_multiscalar_mul`

Shared by the four configurations (`OptionalMixedMultiscalarMul/*.lean`). -/

open Aeneas Aeneas.Std curve25519

namespace Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus

/-- `Forall₂` as a statement about the entries `getElem!`. -/
theorem forall₂_getElem! {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) :
    l₁.length = l₂.length ∧ ∀ k < l₁.length, R l₁[k]! l₂[k]! := by
  refine ⟨h.length_eq, fun k hk => ?_⟩
  rw [getElem!_pos l₁ k hk, getElem!_pos l₂ k (h.length_eq ▸ hk)]
  exact (List.forall₂_iff_get.mp h).2 k hk _

/-- Filtering out the `none`s of a list without `none` keeps its length. -/
theorem length_filterMap_id {β : Type} (l : List (Option β)) (h : none ∉ l) :
    (l.filterMap id).length = l.length := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    rcases o with _ | b
    · simp at h
    · rw [List.filterMap_cons_some (by rfl), List.length_cons, List.length_cons,
        ih (by simpa using h)]

/-- One step of Horner's rule in base `2` for the dynamic and the static points together. -/
theorem horner2_two (a b e : ℕ) (d f : ℕ → Array I8 256#usize)
    (P Q : ℕ → curve25519.edwards.Point) (he : e < 256) :
    2 • ((∑ k ∈ Finset.range a, nafTail (d k) (e + 1) • P k) +
        ∑ k ∈ Finset.range b, nafTail (f k) (e + 1) • Q k) +
      ∑ k ∈ Finset.range a, (d k)[e]!.val • P k + ∑ k ∈ Finset.range b, (f k)[e]!.val • Q k =
      (∑ k ∈ Finset.range a, nafTail (d k) e • P k) + ∑ k ∈ Finset.range b, nafTail (f k) e • Q k :=
          by
  rw [← horner2 a e d P he, ← horner2 b e f Q he, smul_add]
  abel

end Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus
