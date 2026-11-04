/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Subtle
import Proofs.Helpers.AsNat
import Proofs.Scalar.CtEq
import Proofs.Scalar.Reduce
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar)

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem is_canonical_spec (self : Scalar) :
    is_canonical self ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (self.asNat < L → c = 1#u8) ∧ (L ≤ self.asNat → c = 0#u8) ⦄ := by
  unfold is_canonical
  step as ⟨s, hs⟩
  step as ⟨c, hcv, hc1, hc0⟩
  refine ⟨hcv, fun h => hc1 ?_, fun h => hc0 ?_⟩
  · rw [Nat.mod_eq_of_lt h] at hs
    have := Array.eq_of_asNat_eq (a := self.bytes) (b := s.bytes) (by
      simp only [Scalar.asNat_def] at hs; exact hs.symm)
    exact congrArg Scalar.mk this
  · rintro rfl
    have := Nat.mod_lt self.asNat L_pos
    omega

end Curve25519Dalek.scalar.Scalar
