/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.External.Subtle
import Proofs
public section

/-! # Theorems about `src/traits.rs`

The traits of `traits.rs` (`Identity`, `IsIdentity`, `ValidityCheck`, `BasepointTable`,
`MultiscalarMul`, …) have no functions of their own in the translation: their implementations are
specified in the files of the implementing types. The one function is the blanket implementation
of `IsIdentity` for every `T : ConstantTimeEq + Identity`.

Definitions used: `subtle.Choice`, `Choice.IsValid` (`ForHumans/Specs/External/Subtle/`).-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP Curve25519Dalek

namespace Theorems.traits

/-- `IsIdentity::is_identity`, for every `T : ConstantTimeEq + Identity`: `true` iff
`ct_eq self (identity)` returns `1`. Stated generically: if every value `e` that `identity` returns
satisfies `R e`, and `ct_eq self e` then returns a valid `Choice` that is `1` exactly when `Q`, the
result is `true` iff `Q`. For `EdwardsPoint`, `R e` is "`e` represents `0`" and `Q` is
`self.toPoint = 0`. -/
theorem is_identity {T : Type} (ctEqInst : subtle.ConstantTimeEq T)
    (identityInst : traits.Identity T) (self : T) (R : T → Prop) (Q : Prop)
    (hidentity : identityInst.identity ⦃ (r : T) => R r ⦄)
    (hct_eq : ∀ e, R e → ctEqInst.ct_eq self e ⦃ (r : subtle.Choice) =>
      r.IsValid ∧ (r = 1#u8 ↔ Q) ⦄) :
    traits.IsIdentity.Blanket.is_identity ctEqInst identityInst self ⦃ (r : Bool) =>
      r = true ↔ Q ⦄ :=
  traits.IsIdentity.Blanket.is_identity_spec ctEqInst identityInst self R Q hidentity hct_eq

end Theorems.traits
