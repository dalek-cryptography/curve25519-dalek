/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
module
public import ForHumans.Specs.Constants
public import Curve25519Dalek.Types
import ForHumans.Specs.Representation.Array
public section

open Aeneas.Std
open curve25519 (p)

namespace Curve25519Dalek.backend.serial.u64

/-- The natural number represented by the five radix-2^51 limbs. The limbs may exceed 51 bits. -/
def field.FieldElement51.asNat (self : field.FieldElement51) : ℕ :=
  Array.asNat 51 self

/-- The field element represented by the limbs: their value modulo `p`. -/
noncomputable def field.FieldElement51.toField (self : field.FieldElement51) : ZMod p :=
  (self.asNat : ZMod p)

/-- Every limb is `< 2^n`. -/
abbrev field.FieldElement51.LimbsLt (n : ℕ) (self : field.FieldElement51) : Prop :=
  ∀ i < 5, self[i]!.val < 2 ^ n

end Curve25519Dalek.backend.serial.u64
