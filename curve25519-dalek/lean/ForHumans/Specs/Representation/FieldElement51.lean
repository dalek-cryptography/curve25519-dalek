/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
module
public import ForHumans.Specs.Constants
public import ForHumans.Specs.Representation.Array
public import Curve25519Dalek.Types
public import Mathlib.Algebra.Field.ZMod
public section

/-! # The value of a `FieldElement51`

A `FieldElement51` (`backend/serial/u64/field.rs`) is five `u64` limbs in radix `2^51`. `asNat`
is the number they represent (the limbs may exceed 51 bits), `toField` the field element. -/

open Aeneas.Std curve25519

namespace Curve25519Dalek.backend.serial.u64

/-- The natural number represented by the five radix-2^51 limbs. The limbs may exceed 51 bits. -/
def field.FieldElement51.asNat (self : field.FieldElement51) : ℕ :=
  Array.asNat 51 self

/-- The field element represented by the limbs: their value modulo `p`. -/
noncomputable def field.FieldElement51.toField (self : field.FieldElement51) : ZMod p :=
  (self.asNat : ZMod p)

end Curve25519Dalek.backend.serial.u64
