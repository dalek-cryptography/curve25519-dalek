/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Subtle
import Proofs.Traits.IsIdentity
public section

/-! # Specs of `src/traits.rs`

Spec summary: the items of `traits.rs` in the crate's public API with their spec statements,
restated with `recall` from the theorems proved in `Proofs/Traits/`, and the axioms they depend
on. The traits themselves (`Identity`, `IsIdentity`, `ValidityCheck`, `BasepointTable`,
`MultiscalarMul`, `VartimeMultiscalarMul`, `VartimePrecomputedMultiscalarMul`) have no functions
of their own in the translation; their implementations are specified in the files of the
implementing types. The one function is the blanket implementation of `IsIdentity` for every
`T : ConstantTimeEq + Identity`.

`is_identity` is stated generically, conditional on `T`'s instances: every value `e` that
`identity` returns satisfies `R e`, and `ct_eq self e` then returns a valid `Choice` that is `1`
exactly when `Q`; the result is `true` iff `Q`. For `EdwardsPoint`, `R` is "represents `0`" and
`Q` is `self.toPoint = 0`.

Definitions used: `subtle.Choice.IsValid` (`Subtle/`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.traits.IsIdentity.Blanket

/-- `IsIdentity::is_identity`: `true` iff `ct_eq self (identity)` returns `1`. -/
recall is_identity_spec {T : Type} (ctEqInst : subtle.ConstantTimeEq T)
    (identityInst : traits.Identity T) (self : T) (R : T → Prop) (Q : Prop)
    (hidentity : identityInst.identity ⦃ (e : T) => R e ⦄)
    (hct_eq : ∀ e, R e → ctEqInst.ct_eq self e ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ Q) ⦄) :
    is_identity ctEqInst identityInst self ⦃ (b : Bool) => b = true ↔ Q ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_identity_spec

end Curve25519Dalek.traits.IsIdentity.Blanket
