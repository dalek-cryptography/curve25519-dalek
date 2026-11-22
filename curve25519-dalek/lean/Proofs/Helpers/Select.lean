module
public import Aeneas
public import ForHumans.Specs.External.Subtle.Contract
public section

open Aeneas Aeneas.Std Aeneas.Std.WP

/-- A result that is `a` or `b` (as `conditional_select` returns) has every property both have. -/
theorem Aeneas.Std.WP.spec_select {α : Type} {m : Result α} {a b : α} {c : subtle.Choice}
    {P : α → Prop} (h : m ⦃ (r : α) => (c = 0#u8 → r = a) ∧ (c = 1#u8 → r = b) ⦄)
    (hc : c.IsValid) (ha : P a) (hb : P b) : m ⦃ (r : α) => P r ⦄ :=
  spec_mono h fun r ⟨h0, h1⟩ => by
    rcases hc with h | h
    · obtain rfl := h0 h; exact ha
    · obtain rfl := h1 h; exact hb
