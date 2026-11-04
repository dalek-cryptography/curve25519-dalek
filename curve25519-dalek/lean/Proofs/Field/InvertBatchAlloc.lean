/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Field.InternalInvertBatch
import Proofs.Backend.Serial.U32.Field.One
public import Curve25519.Basic
public import Proofs.Helpers.Backend.U64
public import Proofs.Helpers.Backend.U32
import Proofs.Helpers.ToField
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.field.FieldElement51

@[step]
theorem invert_batch_alloc_spec (inputs : Slice FieldElement51)
    (hinputs : ∀ i < inputs.length, (inputs[i]!).LimbsLt 54) :
    invert_batch_alloc inputs ⦃ (r : Slice FieldElement51) =>
      r.length = inputs.length ∧
      ∀ i < inputs.length,
        (inputs[i]!.asNat % p = 0 → r[i]! = inputs[i]!) ∧
        (inputs[i]!.asNat % p ≠ 0 → r[i]!.asNat * inputs[i]!.asNat % p = 1 ∧
          (r[i]!).LimbsLt 52) ⦄ := by
  unfold invert_batch_alloc
  step as ⟨one, hone, honeb⟩
  step with alloc.vec.from_elem_spec
    backend.serial.u64.field.FieldElement51.Insts.CoreCloneClone one inputs.len rfl
    as ⟨scratch, hsc, hsclen⟩
  simp only [alloc.vec.Vec.deref_mut, lift]
  have hslen : scratch.slice.length = inputs.length := by
    rw [show scratch.slice.length = scratch.length from rfl, hsclen, Slice.len_val]
  step as ⟨r, scratch', hrlen, hr⟩
  exact ⟨hrlen, hr⟩

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement2625

@[step]
theorem invert_batch_alloc_spec (inputs : Slice FieldElement2625)
    (hinputs : ∀ i < inputs.length, (inputs[i]!).LimbsLt 27) :
    invert_batch_alloc inputs ⦃ (r : Slice FieldElement2625) =>
      r.length = inputs.length ∧
      ∀ i < inputs.length,
        (inputs[i]!.asNat % p = 0 → r[i]! = inputs[i]!) ∧
        (inputs[i]!.asNat % p ≠ 0 → r[i]!.asNat * inputs[i]!.asNat % p = 1 ∧
          (r[i]!).LimbsLt 26) ⦄ := by
  unfold invert_batch_alloc
  step as ⟨one, hone, honeb⟩
  step with alloc.vec.from_elem_spec
    backend.serial.u32.field.FieldElement2625.Insts.CoreCloneClone one inputs.len rfl
    as ⟨scratch, hsc, hsclen⟩
  simp only [alloc.vec.Vec.deref_mut, lift]
  have hslen : scratch.slice.length = inputs.length := by
    rw [show scratch.slice.length = scratch.length from rfl, hsclen, Slice.len_val]
  step as ⟨r, scratch', hrlen, hr⟩
  exact ⟨hrlen, hr⟩

end Curve25519Dalek.field.FieldElement2625

namespace Curve25519Dalek.Backend

theorem U64.invertBatchAlloc_spec : U64.InvertBatchAllocSpec := by
  intro s hs
  apply spec_mono (field.FieldElement51.invert_batch_alloc_spec s
    fun i hi => U64.red_mulIn (hs i hi))
  rintro r ⟨hlen, hr⟩
  exact ⟨hlen, fun i hi => FieldElement51.toField_inv_of_batch (hr i hi).1 (hr i hi).2 (hs i hi)⟩

theorem U32.invertBatchAlloc_spec : U32.InvertBatchAllocSpec := by
  intro s hs
  apply spec_mono (field.FieldElement2625.invert_batch_alloc_spec s
    fun i hi => U32.red_sqIn (hs i hi))
  rintro r ⟨hlen, hr⟩
  exact ⟨hlen, fun i hi =>
    FieldElement2625.toField_inv_of_batch (hr i hi).1 (hr i hi).2 (hs i hi)⟩

end Curve25519Dalek.Backend
