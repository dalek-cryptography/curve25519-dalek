/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga, Wojciech Aleksander Wołoszyn
-/
module
public import Curve25519Dalek.Types
public import Defs.Array
public section

/-! # The value of a `Scalar29`, its limb bounds and the Montgomery radix (audited) -/

open Aeneas.Std

namespace Curve25519Dalek.backend.serial.u32

/-- The natural number represented by the nine radix-2^29 limbs. -/
def scalar.Scalar29.asNat (self : scalar.Scalar29) : ℕ :=
  Array.asNat 29 self

theorem scalar.Scalar29.asNat_def (self : scalar.Scalar29) : self.asNat = Array.asNat 29 self := by
  unfold scalar.Scalar29.asNat
  rfl

/-- The Montgomery radix `2^261` of the scalar arithmetic; also the modulus at which the nine
29-bit limbs of a `Scalar29` wrap around. Not exposed: use `montgomeryRadix_def`. -/
def scalar.montgomeryRadix : ℕ := 2 ^ 261

theorem scalar.montgomeryRadix_def : scalar.montgomeryRadix = 2 ^ 261 := by
  unfold scalar.montgomeryRadix
  rfl

/-- Every limb is `< 2^n`. -/
abbrev scalar.Scalar29.LimbsLt (n : ℕ) (self : scalar.Scalar29) : Prop :=
  ∀ i < 9, self[i]!.val < 2 ^ n

instance scalar.Scalar29.instDecidableLimbsLt (n : ℕ) (self : scalar.Scalar29) :
    Decidable (self.LimbsLt n) :=
  inferInstanceAs (Decidable (∀ i < 9, self[i]!.val < 2 ^ n))

attribute [scalar_tac_simps] scalar.Scalar29.LimbsLt

end Curve25519Dalek.backend.serial.u32
