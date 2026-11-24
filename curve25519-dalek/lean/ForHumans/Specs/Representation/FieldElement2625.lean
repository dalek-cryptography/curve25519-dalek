module
public import ForHumans.Specs.Constants
public import Curve25519Dalek.Types
public section

open Aeneas.Std
open curve25519 (p)

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

/-- Every limb is `< 2^n`. -/
abbrev field.FieldElement2625.LimbsLt (n : ℕ) (self : field.FieldElement2625) : Prop :=
  ∀ i < 10, self[i]!.val < 2 ^ n

end Curve25519Dalek.backend.serial.u32
