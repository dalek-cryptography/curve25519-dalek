/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Ristretto
import Proofs.Ristretto.CompressedCtEq
public section

/-! # `PartialEq for CompressedRistretto` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.ristretto.CompressedRistretto.Insts.CoreCmpPartialEqCompressedRistretto

/-- `PartialEq for CompressedRistretto`: byte equality. -/
@[step]
theorem eq_spec (self other : CompressedRistretto) :
    eq self other ⦃ (b : Bool) => b = true ↔ self = other ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

end Curve25519Dalek.ristretto.CompressedRistretto.Insts.CoreCmpPartialEqCompressedRistretto
