/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Backend.U32
public import Proofs.Helpers.ToField2625
import Proofs.Field.Eq
import Proofs.Field.IsZero
import Proofs.Backend.Serial.U32.Field.ToBytes
import Proofs.Field.CtEq
import Proofs.Field.IsNegative

public section

/-! # The `u32` backend's specs through the encoding

`eq`, `ct_eq`, `is_negative`, `is_zero`, `to_bytes` of `FieldElement2625` go through `to_bytes`,
whose proof is long: they are kept apart from `Backend/U32.lean`, so that the generic proofs that
do not use them do not wait for it. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open Curve25519Dalek.SharedAFieldElement2625.Insts

namespace Curve25519Dalek.Backend.U32

theorem eq_spec (a b : FieldElement2625) :
    FieldElement2625.Insts.CoreCmpPartialEqFieldElement2625.eq a b ⦃ c =>
      (c = true ↔ a.toField = b.toField) ⦄ :=
  spec_mono (FieldElement2625.Insts.CoreCmpPartialEqFieldElement2625.eq_spec a b)
    fun _ h => h.trans FieldElement2625.toField_eq_toField_iff.symm

theorem ct_eq_spec (a b : FieldElement2625) :
    FieldElement2625.Insts.SubtleConstantTimeEq.ct_eq a b ⦃ c =>
      c.IsValid ∧ (a.toField = b.toField → c = 1#u8) ∧ (a.toField ≠ b.toField → c = 0#u8) ⦄ :=
  spec_mono (FieldElement2625.Insts.SubtleConstantTimeEq.ct_eq_spec a b) fun _ ⟨hv, h1, h0⟩ =>
    ⟨hv, fun h => h1 (FieldElement2625.toField_eq_toField_iff.mp h),
      fun h => h0 fun h' => h (FieldElement2625.toField_eq_toField_iff.mpr h')⟩

theorem is_negative_spec (a : FieldElement2625) :
    field.FieldElement2625.is_negative a ⦃ c => c.IsValid ∧ c.val = a.toField.val % 2 ⦄ :=
  spec_mono (field.FieldElement2625.is_negative_spec a)
    fun _ ⟨hv, h⟩ => ⟨hv, by rw [h, FieldElement2625.toField_val]⟩

theorem to_bytes_spec (a : FieldElement2625) :
    FieldElement2625.to_bytes a ⦃ r => r.asNat 8 = a.toField.val ⦄ :=
  spec_mono (FieldElement2625.to_bytes_spec a) fun _ h => by rw [h, FieldElement2625.toField_val]

theorem is_zero_spec (a : FieldElement2625) :
    field.FieldElement2625.is_zero a ⦃ c =>
      c.IsValid ∧ (a.toField = 0 → c = 1#u8) ∧ (a.toField ≠ 0 → c = 0#u8) ⦄ :=
  spec_mono (field.FieldElement2625.is_zero_spec a) fun _ ⟨hv, h1, h0⟩ =>
    ⟨hv, fun h => h1 (FieldElement2625.toField_eq_zero_iff.mp h),
      fun h => h0 fun h' => h (FieldElement2625.toField_eq_zero_iff.mpr h')⟩

end Curve25519Dalek.Backend.U32
