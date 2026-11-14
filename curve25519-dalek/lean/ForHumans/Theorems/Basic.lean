/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public section

/-! # How to read the specs

Each spec is a theorem about a translated Rust function `f`, usually of the form

    theorem name (args) (hypotheses on args) : f args ⦃ (r : T) => P r ⦄

`triple_iff` below says what the triple means: `f args` returns a value `r` (it does not panic,
overflow or diverge) and `P r` holds. A function returning a tuple is written
`⦃ (r₁ : T₁) (r₂ : T₂) => P r₁ r₂ ⦄`.

The variants of one operator (`&a + &b`, `a + &b`, `&a + b`, `a + b`, `a += &b`, `a += b`) are
stated together, as `∀ f ∈ [f₁, …, fₙ], f a b ⦃ … ⦄`. In `ForHumans/Theorems/Edwards.lean` and
`ForHumans/Theorems/Ristretto.lean` each `fᵢ` is named by the Rust expression it evaluates (`«&P +
&Q»`, …), and defined just above as the translated function.

The proofs are one line, from the theorems of `Proofs/`; they need not be read. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Theorems

/-- `x ⦃ p ⦄`: `x` returns a value, and it satisfies `p`. -/
theorem triple_iff {α : Type} (x : Result α) (p : α → Prop) :
    x ⦃ p ⦄ ↔ ∃ v, x = ok v ∧ p v :=
  ⟨fun h => by cases x <;> simp_all, fun ⟨_, hx, hv⟩ => by simpa [hx] using hv⟩

end Theorems
