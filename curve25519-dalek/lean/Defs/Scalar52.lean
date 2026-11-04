/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
module
public import Curve25519Dalek.Types
public import Defs.Array
public section

/-! # The value of a `Scalar52`, its limb bounds and the Montgomery radix (audited) -/

open Aeneas.Std

namespace Curve25519Dalek.backend.serial.u64

/-- The natural number represented by the five radix-2^52 limbs. -/
def scalar.Scalar52.asNat (self : scalar.Scalar52) : ℕ :=
  Array.asNat 52 self

theorem scalar.Scalar52.asNat_def (self : scalar.Scalar52) : self.asNat = Array.asNat 52 self := by
  unfold scalar.Scalar52.asNat
  rfl

/-- The Montgomery radix `2^260` of the scalar arithmetic; also the modulus at which the five
52-bit limbs of a `Scalar52` wrap around. Not exposed: use `montgomeryRadix_def`. -/
def scalar.montgomeryRadix : ℕ := 2 ^ 260

theorem scalar.montgomeryRadix_def : scalar.montgomeryRadix = 2 ^ 260 := by
  unfold scalar.montgomeryRadix
  rfl

/-- Every limb is `< 2^n`. -/
abbrev scalar.Scalar52.LimbsLt (n : ℕ) (self : scalar.Scalar52) : Prop :=
  ∀ i < 5, self[i]!.val < 2 ^ n

instance scalar.Scalar52.instDecidableLimbsLt (n : ℕ) (self : scalar.Scalar52) :
    Decidable (self.LimbsLt n) :=
  inferInstanceAs (Decidable (∀ i < 5, self[i]!.val < 2 ^ n))

attribute [scalar_tac_simps] scalar.Scalar52.LimbsLt

end Curve25519Dalek.backend.serial.u64
