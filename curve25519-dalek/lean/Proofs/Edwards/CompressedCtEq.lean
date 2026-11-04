/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Subtle.Contract
import Proofs.Edwards.AsBytes
import Proofs.Helpers.Array
import Subtle.Instances
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts.SubtleConstantTimeEq

/-- `ConstantTimeEq for CompressedEdwardsY`: byte equality (two encodings of one point can
differ). -/
@[step]
theorem ct_eq_spec (self other : CompressedEdwardsY) :
    ct_eq self other ⦃ (c : subtle.Choice) => c.IsValid ∧ (c = 1#u8 ↔ self = other) ⦄ := by
  unfold ct_eq
  step as ⟨a, ha⟩
  step as ⟨s, hs⟩
  step as ⟨a1, ha1⟩
  step as ⟨s1, hs1⟩
  step as ⟨c, hcv, hc1, hc0⟩
  subst ha hs ha1 hs1
  refine ⟨hcv, fun h => ?_, fun h => hc1 (by rw [h])⟩
  by_contra hne
  rw [hc0 fun hss => hne (Array.eq_of_to_slice_eq hss)] at h
  exact absurd h (by decide)

end Curve25519Dalek.edwards.CompressedEdwardsY.Insts.SubtleConstantTimeEq
