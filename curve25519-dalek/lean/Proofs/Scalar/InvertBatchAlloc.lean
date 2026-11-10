/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar29
import Proofs.Backend.Serial.U64.Scalar.AsMontgomery
import Proofs.Helpers.Target
import Proofs.Scalar.InvertBatchInternal
import Proofs.Scalar.Unpack
import Proofs.Backend.Serial.U32.Scalar.AsMontgomery
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert_batch_alloc.«x86_64-tables_spec» (inputs : Slice Scalar)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_alloc.«x86_64-tables» inputs ⦃ (ret : Scalar) (r : Slice Scalar) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ := by
  unfold invert_batch_alloc.«x86_64-tables»
  step as ⟨one, hone, honeb⟩
  step as ⟨acc, hacc, haccb⟩
  step with alloc.vec.from_elem_spec
    backend.serial.u64.scalar.Scalar52.Insts.CoreCloneClone acc inputs.len rfl
    as ⟨scratch, hsc, hsclen⟩
  simp only [alloc.vec.Vec.deref_mut, lift]
  have hslen : scratch.slice.length = inputs.length := by
    rw [show scratch.slice.length = scratch.length from rfl, hsclen, Slice.len_val]
  step as ⟨ret, r, scratch', hrlen, hr, hret, hretL⟩
  exact ⟨hrlen, hr, hret, hretL⟩

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert_batch_alloc.«x86_64-no-tables_spec» (inputs : Slice Scalar)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_alloc.«x86_64-no-tables» inputs ⦃ (ret : Scalar) (r : Slice Scalar) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  invert_batch_alloc.«x86_64-tables_spec» inputs hinputs

end Curve25519Dalek.scalar.Scalar


namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert_batch_alloc.«i686-tables_spec» (inputs : Slice Scalar)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_alloc.«i686-tables» inputs ⦃ (ret : Scalar) (r : Slice Scalar) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ := by
  unfold invert_batch_alloc.«i686-tables»
  step as ⟨one, hone, honeb⟩
  step as ⟨acc, hacc, haccb⟩
  step with alloc.vec.from_elem_spec
    backend.serial.u32.scalar.Scalar29.Insts.CoreCloneClone acc inputs.len rfl
    as ⟨scratch, hsc, hsclen⟩
  simp only [alloc.vec.Vec.deref_mut, lift]
  have hslen : scratch.slice.length = inputs.length := by
    rw [show scratch.slice.length = scratch.length from rfl, hsclen, Slice.len_val]
  step as ⟨ret, r, scratch', hrlen, hr, hret, hretL⟩
  exact ⟨hrlen, hr, hret, hretL⟩

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert_batch_alloc.«i686-no-tables_spec» (inputs : Slice Scalar)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_alloc.«i686-no-tables» inputs ⦃ (ret : Scalar) (r : Slice Scalar) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  invert_batch_alloc.«i686-tables_spec» inputs hinputs

end Curve25519Dalek.scalar.Scalar
namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert_batch_alloc_spec (inputs : Slice Scalar)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_alloc inputs ⦃ (ret : Scalar) (r : Slice Scalar) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ := by
  unfold invert_batch_alloc
  exact dispatch_all_spec
    (invert_batch_alloc.«x86_64-tables_spec» inputs hinputs)
    (invert_batch_alloc.«x86_64-no-tables_spec» inputs hinputs)
    (invert_batch_alloc.«i686-tables_spec» inputs hinputs)
    (invert_batch_alloc.«i686-no-tables_spec» inputs hinputs)

end Curve25519Dalek.scalar.Scalar
