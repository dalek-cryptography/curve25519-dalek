/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.ToBytes
import Proofs.Helpers.AsNat
import Subtle.Lemmas
import Proofs.Backend.Serial.U32.Field.ToBytes
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.field.FieldElement51

@[step]
theorem is_negative_spec (self : FieldElement51) :
    is_negative self ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ c.val = self.asNat % p % 2 ⦄ := by
  unfold is_negative
  step as ⟨bytes, hbytes⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1, hi1bv⟩
  step as ⟨c, hcv, hc⟩
  · refine (subtle.Choice.isValid_iff i1).mpr ?_
    rw [hi1, UScalar.val_and]
    exact Nat.and_le_right
  refine ⟨hcv, ?_⟩
  rw [hc, hi1, UScalar.val_and]
  change i.val &&& 1 = _
  rw [Nat.and_one_is_mod, ← hbytes, hi]
  simpa [Array.getElem!_Nat_eq] using
    (Array.asNat_mod_of_dvd 8 (m := 2) (by norm_num) bytes (by simp)).symm

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement2625

@[step]
theorem is_negative_spec (self : FieldElement2625) :
    is_negative self ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ c.val = self.asNat % p % 2 ⦄ := by
  unfold is_negative
  step as ⟨bytes, hbytes⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1, hi1bv⟩
  step as ⟨c, hcv, hc⟩
  · refine (subtle.Choice.isValid_iff i1).mpr ?_
    rw [hi1, UScalar.val_and]
    exact Nat.and_le_right
  refine ⟨hcv, ?_⟩
  rw [hc, hi1, UScalar.val_and]
  change i.val &&& 1 = _
  rw [Nat.and_one_is_mod, ← hbytes, hi]
  simpa [Array.getElem!_Nat_eq] using
    (Array.asNat_mod_of_dvd 8 (m := 2) (by norm_num) bytes (by simp)).symm

end Curve25519Dalek.field.FieldElement2625
