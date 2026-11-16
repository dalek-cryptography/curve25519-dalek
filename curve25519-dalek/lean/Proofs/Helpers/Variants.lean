/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Lean
public section

/-- Proves `∀ f ∈ [f₁, …, fₙ], P f` from `h₁, …, hₙ` (or from a single `h` for all). -/
syntax (name := variants) "variants " "[" term,+ "]" : tactic

macro_rules
  | `(tactic| variants [$h]) =>
    `(tactic| (simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
                 and_true]
               and_intros <;> (apply $h <;> assumption)))
  | `(tactic| variants [$hs,*]) => do
    let proofs ← hs.getElems.mapM fun h => `(by apply $h <;> assumption)
    `(tactic| (simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
                 and_true]
               exact ⟨$proofs,*⟩))
