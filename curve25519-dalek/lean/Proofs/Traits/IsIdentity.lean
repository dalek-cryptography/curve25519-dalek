/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Subtle
public section

/-! # `IsIdentity::is_identity` (the blanket implementation of `traits.rs`)

`is_identity` is `ct_eq` with `T::identity()`, converted to `bool`. The spec is generic in `T`
and conditional on the behaviour of `T`'s `Identity` and `ConstantTimeEq` instances: every
value `e` that `identity` returns satisfies `R e`, and for such `e`, `ct_eq self e` returns a
valid `Choice` that is `1` exactly when `Q`. The per-type specs of `identity` and `ct_eq`
discharge these hypotheses directly (`R` the postcondition of `identity`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.traits.IsIdentity.Blanket

/-- `IsIdentity::is_identity`: `true` iff `ct_eq self (identity)` returns `1`. -/
@[step]
theorem is_identity_spec {T : Type} (ctEqInst : subtle.ConstantTimeEq T)
    (identityInst : traits.Identity T) (self : T) (R : T → Prop) (Q : Prop)
    (hidentity : identityInst.identity ⦃ (e : T) => R e ⦄)
    (hct_eq : ∀ e, R e → ctEqInst.ct_eq self e ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ Q) ⦄) :
    is_identity ctEqInst identityInst self ⦃ (b : Bool) => b = true ↔ Q ⦄ := by
  unfold is_identity
  step with hidentity as ⟨e, he⟩
  step with hct_eq e he as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

end Curve25519Dalek.traits.IsIdentity.Blanket
