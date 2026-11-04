/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Montgomery
import Proofs.Montgomery.CtEq
public section

/-! # `PartialEq for MontgomeryPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint

/-- `PartialEq for MontgomeryPoint`: equality of the encoded `u`-coordinates (x86_64 targets). -/
@[step]
theorem eq_spec (self other : MontgomeryPoint) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.u = other.u ⦄ := by
  unfold eq
  step with SubtleConstantTimeEq.ct_eq_spec self other as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint
