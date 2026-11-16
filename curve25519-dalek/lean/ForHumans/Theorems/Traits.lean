/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
import Proofs -- shake: keep
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP Curve25519Dalek

namespace Theorems.traits

/-- `IsIdentity::is_identity`: `true` iff `ct_eq self (identity)` returns `1`. -/
theorem is_identity {T : Type} (ctEqInst : subtle.ConstantTimeEq T)
    (identityInst : traits.Identity T) (self : T) (R : T → Prop) (Q : Prop)
    (hidentity : identityInst.identity ⦃ (r : T) => R r ⦄)
    (hct_eq : ∀ e, R e → ctEqInst.ct_eq self e ⦃ (r : subtle.Choice) =>
      r.IsValid ∧ (r = 1#u8 ↔ Q) ⦄) :
    traits.IsIdentity.Blanket.is_identity ctEqInst identityInst self ⦃ (r : Bool) =>
      r = true ↔ Q ⦄ :=
  traits.IsIdentity.Blanket.is_identity_spec ctEqInst identityInst self R Q hidentity hct_eq

end Theorems.traits
