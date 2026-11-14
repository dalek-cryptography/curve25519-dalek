/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Subtle.Contract
@[expose] public section
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek

/-! # Derived results for `subtle` -/

/-! ## Validity -/

namespace subtle.Choice

theorem isValid_iff (c : subtle.Choice) : c.IsValid ↔ c.val ≤ 1 := by
  constructor
  · rintro (rfl | rfl) <;> decide
  · intro h
    have : c.val = 0 ∨ c.val = 1 := by scalar_tac
    rcases this with h0 | h1
    · exact Or.inl (UScalar.eq_of_val_eq (by simpa using h0))
    · exact Or.inr (UScalar.eq_of_val_eq (by simpa using h1))

/-- `0` absorbs a valid `Choice` under `&&&`. -/
theorem IsValid.and_zero {a : subtle.Choice} (ha : a.IsValid) : a &&& 0#u8 = 0#u8 := by
  rcases ha with rfl | rfl <;> decide

end subtle.Choice

/-! ## Specs of the faithful bodies -/

/-- The default `conditional_assign` behaves like the instance's `conditional_select`. -/
theorem subtle.ConditionallySelectable.conditional_assign.default_spec {Self : Type}
    (inst : subtle.ConditionallySelectable Self) (a b : Self) (c : subtle.Choice)
    (h : inst.conditional_select a b c ⦃ r => (c = 0#u8 → r = a) ∧ (c = 1#u8 → r = b) ⦄) :
    subtle.ConditionallySelectable.conditional_assign.default inst a b c ⦃ r =>
      (c = 0#u8 → r = a) ∧ (c = 1#u8 → r = b) ⦄ := h

/-- The default `conditional_swap` swaps iff `c = 1`, given that the instance's
`conditional_assign` follows its contract at `c`. -/
theorem subtle.ConditionallySelectable.conditional_swap.default_spec {Self : Type}
    (inst : subtle.ConditionallySelectable Self) (a b : Self) (c : subtle.Choice)
    (h : ∀ x y, inst.conditional_assign x y c ⦃ r => (c = 0#u8 → r = x) ∧ (c = 1#u8 → r = y) ⦄) :
    subtle.ConditionallySelectable.conditional_swap.default inst a b c ⦃ r =>
      (c = 0#u8 → r = (a, b)) ∧ (c = 1#u8 → r = (b, a)) ⦄ := by
  unfold subtle.ConditionallySelectable.conditional_swap.default
  step with h as ⟨a1, h1⟩
  step with h as ⟨b1, h2⟩
  grind
