/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Aeneas.Std.WP
public section

/-! # Results over optional inputs

The `optional_*` multiscalar functions return `none` iff some input is `none`. Their proofs give
the result as `(r = none ↔ none ∈ ops) ∧ ∀ R, r = some R → Q R (ops.filterMap id)`; the public
specs state it on the inputs directly: `none` if some input is `none`, and for inputs `ps.map some`
a result `some R` with `Q R ps` (`spec_some_of_filterMap`). -/

open Aeneas Aeneas.Std Aeneas.Std.WP

/-- From the `filterMap` form of an optional result to the form on `ps.map some`. -/
theorem spec_some_of_filterMap {α β : Type} {m : Result (Option β)} {ops : List (Option α)}
    {Q : β → List α → Prop}
    (h : m ⦃ (r : Option β) => (r = none ↔ none ∈ ops) ∧
      ∀ R, r = some R → Q R (ops.filterMap id) ⦄) :
    m ⦃ (r : Option β) => (none ∈ ops → r = none) ∧
      ∀ ps : List α, ops = ps.map some → ∃ R, r = some R ∧ Q R ps ⦄ := by
  refine spec_mono h fun r ⟨hnone, hsome⟩ => ⟨hnone.mpr, fun ps hps => ?_⟩
  cases r with
  | none =>
    have := hnone.mp rfl
    simp [hps] at this
  | some R =>
    refine ⟨R, rfl, ?_⟩
    have := hsome R rfl
    rwa [hps, List.filterMap_map, show (id ∘ some : α → Option α) = some from rfl,
      List.filterMap_some] at this
