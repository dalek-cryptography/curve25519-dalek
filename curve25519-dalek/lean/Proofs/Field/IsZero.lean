/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.ToBytes
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
import Subtle.Instances
import Proofs.Backend.Serial.U32.Field.ToBytes
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.field.FieldElement51

@[step]
theorem is_zero_spec (self : FieldElement51) :
    is_zero self ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (self.asNat % p = 0 → c = 1#u8) ∧ (self.asNat % p ≠ 0 → c = 0#u8) ⦄ := by
  unfold is_zero
  step as ⟨bytes, hbytes⟩
  step as ⟨s, hs⟩
  step as ⟨s1, hs1⟩
  step as ⟨c, hcv, hc1, hc0⟩
  subst hs hs1
  have hzero : (Array.repeat 32#usize 0#u8).asNat 8 = 0 := by rw [Array.asNat_def]; decide
  refine ⟨hcv, fun h => hc1 ?_, fun h => hc0 fun hss => h ?_⟩
  · exact congrArg Array.to_slice (Array.eq_of_asNat_eq (hbytes.trans (h.trans hzero.symm)))
  · rw [← hbytes, Array.eq_of_to_slice_eq hss, hzero]

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement2625

@[step]
theorem is_zero_spec (self : FieldElement2625) :
    is_zero self ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (self.asNat % p = 0 → c = 1#u8) ∧ (self.asNat % p ≠ 0 → c = 0#u8) ⦄ := by
  unfold is_zero
  step as ⟨bytes, hbytes⟩
  step as ⟨s, hs⟩
  step as ⟨s1, hs1⟩
  step as ⟨c, hcv, hc1, hc0⟩
  subst hs hs1
  have hzero : (Array.repeat 32#usize 0#u8).asNat 8 = 0 := by rw [Array.asNat_def]; decide
  refine ⟨hcv, fun h => hc1 ?_, fun h => hc0 fun hss => h ?_⟩
  · exact congrArg Array.to_slice (Array.eq_of_asNat_eq (hbytes.trans (h.trans hzero.symm)))
  · rw [← hbytes, Array.eq_of_to_slice_eq hss, hzero]

end Curve25519Dalek.field.FieldElement2625
