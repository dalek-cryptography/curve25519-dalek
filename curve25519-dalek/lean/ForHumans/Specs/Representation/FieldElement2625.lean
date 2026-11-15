/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
module
public import ForHumans.Specs.Constants
public import Curve25519Dalek.Types
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Div
public section

/-! # The value of a `FieldElement2625`

A `FieldElement2625` (`backend/serial/u32/field.rs`) is ten `u32` limbs in radix `2^25.5`:
"`x = ∑_{i=0}^9 x_i 2^⌈i 51/2⌉ = x_0 + x_1 2^26 + x_2 2^51 + x_3 2^77 + ⋯ + x_9 2^230`". `asNat`
is that number (the limbs may exceed their nominal width), `toField` the field element, `LimbsLt n`
says that every limb is `< 2^n`. -/

open Aeneas.Std curve25519

/-- The value of ten limbs in radix `2^25.5`: `∑ x_i · 2^⌈i · 51 / 2⌉` (`⌈/⌉` is ceiling
division). The limbs may exceed their nominal `26` or `25` bits. -/
def Aeneas.Std.Array.asNat2625 {ty : UScalarTy} (a : Array (UScalar ty) 10#usize) : ℕ :=
  ∑ i ∈ Finset.range 10, a[i]!.val * 2 ^ (i * 51 ⌈/⌉ 2)

namespace Curve25519Dalek.backend.serial.u32

/-- The natural number represented by the ten radix-`2^25.5` limbs. -/
def field.FieldElement2625.asNat (self : field.FieldElement2625) : ℕ :=
  Array.asNat2625 self

/-- The field element represented by the limbs: their value modulo `p`. -/
noncomputable def field.FieldElement2625.toField (self : field.FieldElement2625) : ZMod p :=
  (self.asNat : ZMod p)

/-- Every limb is `< 2^n`: the limb bounds that the theorems assume and guarantee (the
bound is in the invariant of each point type). -/
abbrev field.FieldElement2625.LimbsLt (n : ℕ) (self : field.FieldElement2625) : Prop :=
  ∀ i < 10, self[i]!.val < 2 ^ n

end Curve25519Dalek.backend.serial.u32
