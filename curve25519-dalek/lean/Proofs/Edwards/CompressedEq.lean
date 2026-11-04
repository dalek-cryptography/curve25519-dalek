/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Edwards.CompressedCtEq
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts.CoreCmpPartialEqCompressedEdwardsY

/-- `PartialEq for CompressedEdwardsY`: byte equality (two encodings of one point can differ). -/
@[step]
theorem eq_spec (self other : CompressedEdwardsY) :
    eq self other ⦃ (b : Bool) => b = true ↔ self = other ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

end Curve25519Dalek.edwards.CompressedEdwardsY.Insts.CoreCmpPartialEqCompressedEdwardsY
