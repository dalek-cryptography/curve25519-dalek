/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Backend.U64
import Proofs.Field.Eq
import Proofs.Field.IsZero
import Proofs.Backend.Serial.U64.Field.ToBytes
import Proofs.Field.CtEq
import Proofs.Field.IsNegative
import Proofs.Helpers.ToField
public section

/-! # The `u64` backend's specs through the encoding

`eq`, `ct_eq`, `is_negative`, `is_zero`, `to_bytes` of `FieldElement51` go through `to_bytes`,
whose proof is long: they are kept apart from `Backend/U64.lean`, so that the generic proofs that
do not use them do not wait for it. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51
open Curve25519Dalek.Shared0FieldElement51.Insts

namespace Curve25519Dalek.Backend.U64

theorem eq_spec (a b : FieldElement51) :
    FieldElement51.Insts.CoreCmpPartialEqFieldElement51.eq a b ⦃ c =>
      (c = true ↔ a.toField = b.toField) ⦄ :=
  spec_mono (FieldElement51.Insts.CoreCmpPartialEqFieldElement51.eq_spec a b)
    fun _ h => h.trans FieldElement51.toField_eq_toField_iff.symm

theorem ct_eq_spec (a b : FieldElement51) :
    FieldElement51.Insts.SubtleConstantTimeEq.ct_eq a b ⦃ c =>
      c.IsValid ∧ (a.toField = b.toField → c = 1#u8) ∧ (a.toField ≠ b.toField → c = 0#u8) ⦄ :=
  spec_mono (FieldElement51.Insts.SubtleConstantTimeEq.ct_eq_spec a b) fun _ ⟨hv, h1, h0⟩ =>
    ⟨hv, fun h => h1 (FieldElement51.toField_eq_toField_iff.mp h),
      fun h => h0 fun h' => h (FieldElement51.toField_eq_toField_iff.mpr h')⟩

theorem is_negative_spec (a : FieldElement51) :
    field.FieldElement51.is_negative a ⦃ c => c.IsValid ∧ c.val = a.toField.val % 2 ⦄ :=
  spec_mono (field.FieldElement51.is_negative_spec a)
    fun _ ⟨hv, h⟩ => ⟨hv, by rw [h, FieldElement51.toField_val]⟩

theorem to_bytes_spec (a : FieldElement51) :
    FieldElement51.to_bytes a ⦃ r => r.asNat 8 = a.toField.val ⦄ :=
  spec_mono (FieldElement51.to_bytes_spec a) fun _ h => by rw [h, FieldElement51.toField_val]

theorem is_zero_spec (a : FieldElement51) :
    field.FieldElement51.is_zero a ⦃ c =>
      c.IsValid ∧ (a.toField = 0 → c = 1#u8) ∧ (a.toField ≠ 0 → c = 0#u8) ⦄ :=
  spec_mono (field.FieldElement51.is_zero_spec a) fun _ ⟨hv, h1, h0⟩ =>
    ⟨hv, fun h => h1 (FieldElement51.toField_eq_zero_iff.mp h),
      fun h => h0 fun h' => h (FieldElement51.toField_eq_zero_iff.mpr h')⟩

end Curve25519Dalek.Backend.U64
