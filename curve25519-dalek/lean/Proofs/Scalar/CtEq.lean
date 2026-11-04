/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar52
public import Subtle
import Proofs.Helpers.Array
import Subtle.Instances
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar.Insts.SubtleConstantTimeEq

@[step]
theorem ct_eq_spec (self other : Scalar) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (self = other → c = 1#u8) ∧ (self ≠ other → c = 0#u8) ⦄ := by
  unfold ct_eq
  step as ⟨s, hs⟩
  step as ⟨s1, hs1⟩
  step as ⟨c, hcv, hc1, hc0⟩
  subst hs hs1
  refine ⟨hcv, fun h => hc1 (by rw [h]), fun h => hc0 fun hss => h ?_⟩
  exact congrArg Scalar.mk (Array.eq_of_to_slice_eq hss)

end Curve25519Dalek.scalar.Scalar.Insts.SubtleConstantTimeEq
