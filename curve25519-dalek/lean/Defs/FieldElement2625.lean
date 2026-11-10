/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga, Wojciech Aleksander Wołoszyn
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Types
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Div
public section

/-! # The value of a `FieldElement2625` (audited)

A `FieldElement2625` is ten `u32` limbs in radix `2^25.5` (`backend/serial/u32/field.rs`):
"`x = ∑_{i=0}^9 x_i 2^⌈i 51/2⌉ = x_0 + x_1 2^26 + x_2 2^51 + x_3 2^77 + ⋯ + x_9 2^230`". `asNat`
is that natural number (unreduced), the form of the field specs; `toField` is the field element
it represents. `reduce` takes ten `u64` coefficients with the same weights, so the value is
defined on any array of ten limbs (`Array.asNat2625`). Other forms of the sum (integer
exponents, written out) are lemmas in `Proofs/Helpers/FieldElement2625.lean`. -/

open Aeneas.Std curve25519

/-- The value of ten limbs in radix `2^25.5`: `∑ x_i · 2^⌈i · 51 / 2⌉` (`⌈/⌉` is ceiling
division). The limbs may exceed their nominal `26` or `25` bits. -/
def Aeneas.Std.Array.asNat2625 {ty : UScalarTy} (a : Array (UScalar ty) 10#usize) : ℕ :=
  ∑ i ∈ Finset.range 10, a[i]!.val * 2 ^ (i * 51 ⌈/⌉ 2)

theorem Aeneas.Std.Array.asNat2625_def {ty : UScalarTy} (a : Array (UScalar ty) 10#usize) :
    a.asNat2625 = ∑ i ∈ Finset.range 10, a[i]!.val * 2 ^ (i * 51 ⌈/⌉ 2) := by
  unfold Aeneas.Std.Array.asNat2625
  rfl

namespace Curve25519Dalek.backend.serial.u32

/-- The natural number represented by the ten radix-`2^25.5` limbs. -/
def field.FieldElement2625.asNat (self : field.FieldElement2625) : ℕ :=
  Array.asNat2625 self

theorem field.FieldElement2625.asNat_def (self : field.FieldElement2625) :
    self.asNat = Array.asNat2625 self := by
  unfold field.FieldElement2625.asNat
  rfl

/-- The field element represented by the limbs: their value modulo `p`. -/
noncomputable def field.FieldElement2625.toField (self : field.FieldElement2625) : ZMod p :=
  (self.asNat : ZMod p)

theorem field.FieldElement2625.toField_def (self : field.FieldElement2625) :
    self.toField = (self.asNat : ZMod p) := by
  unfold field.FieldElement2625.toField
  rfl

/-- Every limb is `< 2^n`. -/
abbrev field.FieldElement2625.LimbsLt (n : ℕ) (self : field.FieldElement2625) : Prop :=
  ∀ i < 10, self[i]!.val < 2 ^ n

instance field.FieldElement2625.instDecidableLimbsLt (n : ℕ) (self : field.FieldElement2625) :
    Decidable (self.LimbsLt n) :=
  inferInstanceAs (Decidable (∀ i < 10, self[i]!.val < 2 ^ n))

attribute [scalar_tac_simps] field.FieldElement2625.LimbsLt

end Curve25519Dalek.backend.serial.u32
