/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Types
public import Defs.Array
public section

/-! # The value of a `FieldElement51` (audited)

`asNat` is the natural number encoded by the limbs (unreduced), the form of the field specs
(`r.asNat % p = …`); `toField` is the field element it represents, the form of the point specs.
The bridge between the two forms is `Proofs/Helpers/ToField.lean`. -/

open Aeneas.Std curve25519

namespace Curve25519Dalek.backend.serial.u64

/-- The natural number represented by the five radix-2^51 limbs. The limbs may exceed 51 bits. -/
def field.FieldElement51.asNat (self : field.FieldElement51) : ℕ :=
  Array.asNat 51 self

theorem field.FieldElement51.asNat_def (self : field.FieldElement51) :
    self.asNat = Array.asNat 51 self := by
  unfold field.FieldElement51.asNat
  rfl

/-- The field element represented by the limbs: their value modulo `p`. -/
noncomputable def field.FieldElement51.toField (self : field.FieldElement51) : ZMod p :=
  (self.asNat : ZMod p)

theorem field.FieldElement51.toField_def (self : field.FieldElement51) :
    self.toField = (self.asNat : ZMod p) := by
  unfold field.FieldElement51.toField
  rfl

/-- Every limb is `< 2^n`. -/
abbrev field.FieldElement51.LimbsLt (n : ℕ) (self : field.FieldElement51) : Prop :=
  ∀ i < 5, self[i]!.val < 2 ^ n

instance field.FieldElement51.instDecidableLimbsLt (n : ℕ) (self : field.FieldElement51) :
    Decidable (self.LimbsLt n) :=
  inferInstanceAs (Decidable (∀ i < 5, self[i]!.val < 2 ^ n))

attribute [scalar_tac_simps] field.FieldElement51.LimbsLt

end Curve25519Dalek.backend.serial.u64
