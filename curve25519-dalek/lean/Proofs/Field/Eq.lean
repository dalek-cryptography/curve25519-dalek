/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Defs.FieldElement51
import Proofs.Field.CtEq
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
namespace CoreCmpPartialEqFieldElement51

@[step]
theorem eq_spec (self other : FieldElement51) :
    eq self other ⦃ (b : Bool) =>
      (b = true ↔ self.asNat % p = other.asNat % p) ⦄ := by
  unfold eq
  step as ⟨c, _, hc1, hc0⟩
  step as ⟨b, hb⟩
  subst hb
  by_cases h : self.asNat % p = other.asNat % p
  · simp [h, hc1 h]
  · simp [h, hc0 h]

end CoreCmpPartialEqFieldElement51
end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625.Insts
namespace CoreCmpPartialEqFieldElement2625

@[step]
theorem eq_spec (self other : FieldElement2625) :
    eq self other ⦃ (b : Bool) =>
      (b = true ↔ self.asNat % p = other.asNat % p) ⦄ := by
  unfold eq
  step as ⟨c, _, hc1, hc0⟩
  step as ⟨b, hb⟩
  subst hb
  by_cases h : self.asNat % p = other.asNat % p
  · simp [h, hc1 h]
  · simp [h, hc0 h]

end CoreCmpPartialEqFieldElement2625
end Curve25519Dalek.backend.serial.u32.field.FieldElement2625.Insts
