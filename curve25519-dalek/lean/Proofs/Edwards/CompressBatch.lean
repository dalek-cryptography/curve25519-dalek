/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Edwards.Encoding
public import Defs.Edwards
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Edwards.Affine.Compress
import Proofs.Field.InvertBatch
import Proofs.Helpers.Array
import Proofs.Helpers.Coords
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Helpers.ToField2625
public section

/-! # `EdwardsPoint::compress_batch`

The `Z` coordinates are inverted in one batch (`invert_batch`), then each point is compressed as
the affine point `(X Z⁻¹, Y Z⁻¹)`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

open scoped Helpers.IndexStep in
/-- The first closure of `compress_batch`: `Z` of point `i`. -/
private theorem compress_batch.closure.call_mut_spec {N : Usize}
    (inputs : Array EdwardsPoint.«x86_64-tables» N) (i : Usize) (hi : i.val < N.val) :
    compress_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement51.call_mut inputs i
      ⦃ (z : FieldElement51) (c' : compress_batch.closure N) =>
        z = inputs[i.val]!.Z ∧ c' = inputs ⦄ := by
  unfold compress_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement51.call_mut
  step as ⟨ep, hep⟩
  rw [hep]

open scoped Helpers.IndexStep in
/-- The second closure of `compress_batch`: compress `(X z, Y z)` for the inverse `z` of `Z`. -/
private theorem compress_batch.closure_1.call_mut_spec {N : Usize}
    (inputs : Array EdwardsPoint.«x86_64-tables» N) (zs : Array FieldElement51 N) (i : Usize)
    (hi : i.val < N.val) (hinput : inputs[i.val]!.LimbsLt 52)
    (hz : zs[i.val]!.toField = inputs[i.val]!.Z.toField⁻¹)
    (hzb : (zs[i.val]!).LimbsLt 52) :
    compress_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeCompressedEdwardsY.call_mut
      (inputs, zs) i ⦃ (r : CompressedEdwardsY) (c' : compress_batch.closure_1 N) =>
        r.asNat = (inputs[i.val]!.Y.toField / inputs[i.val]!.Z.toField).val +
          2 ^ 255 * (if (inputs[i.val]!.X.toField / inputs[i.val]!.Z.toField).IsNeg then 1 else 0) ∧
        c' = (inputs, zs) ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hinput
  unfold compress_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeCompressedEdwardsY.call_mut
  step as ⟨ep, hep⟩
  step as ⟨fe, hfe⟩
  subst hep hfe
  step as ⟨x, hx, hxb⟩
  step as ⟨y, hy, hyb⟩
  step as ⟨cey, hcey⟩
  refine ⟨?_, rfl⟩
  rw [hcey, toField_mul_of_mod hx, toField_mul_of_mod hy, hz, div_eq_mul_inv, div_eq_mul_inv]

/-- `EdwardsPoint::compress_batch`: entry `i` is the canonical `y = Y / Z` of point `i` with the
sign of `x = X / Z` in bit `255`; limbs `< 2^52`. -/
@[step]
theorem compress_batch_spec {N : Usize} (inputs : Array EdwardsPoint.«x86_64-tables» N)
    (hinputs : ∀ i < N.val, inputs[i]!.LimbsLt 52) :
    compress_batch inputs ⦃ (r : Array CompressedEdwardsY N) =>
      ∀ i < N.val, r[i]!.asNat = (inputs[i]!.Y.toField / inputs[i]!.Z.toField).val +
        2 ^ 255 * (if (inputs[i]!.X.toField / inputs[i]!.Z.toField).IsNeg then 1 else 0) ⦄ := by
  unfold compress_batch
  apply spec_bind (core.array.from_fn_spec N _ inputs (fun _ c => c = inputs)
    (fun i z => z = inputs[i]!.Z) rfl fun i c hi hc => ?_)
  · intro zs hzs
    have hz : ∀ i < N.val, zs[i]! = inputs[i]!.Z := fun i hi => by
      rw [Array.getElem!_Nat_eq, getElem!_pos zs.val i (by simpa using hi)]
      exact hzs i (by simpa using hi)
    have hzb : ∀ i < N.val, (zs[i]!).LimbsLt 54 := fun i hi j hj => by
      rw [hz i hi]
      exact ((hinputs i hi).2.2.1 j hj).trans (by norm_num : (2 : ℕ) ^ 52 < 2 ^ 54)
    step as ⟨zs1, hzs1⟩
    apply spec_mono (core.array.from_fn_spec N _ (inputs, zs1) (fun _ c => c = (inputs, zs1))
      (fun i x => x.asNat = (inputs[i]!.Y.toField / inputs[i]!.Z.toField).val +
        2 ^ 255 * (if (inputs[i]!.X.toField / inputs[i]!.Z.toField).IsNeg then 1 else 0))
      rfl fun i c hi hc => ?_)
    · intro r hr i hi
      rw [Array.getElem!_Nat_eq, getElem!_pos r.val i (by simpa using hi)]
      exact hr i (by simpa using hi)
    · subst hc
      obtain ⟨h0, h1⟩ := hzs1 i.val hi
      rw [hz i.val hi] at h0 h1
      obtain ⟨hinv, hinvb⟩ := toField_inv_of_batch h0 h1 (hinputs i.val hi).2.2.1
      exact compress_batch.closure_1.call_mut_spec inputs zs1 i hi (hinputs i.val hi) hinv hinvb
  · subst c
    exact compress_batch.closure.call_mut_spec inputs i hi

/-- `EdwardsPoint::compress_batch`: entry `i` is RFC 8032's encoding of point `i`. -/
theorem compress_batch_spec_point {N : Usize} (inputs : Array EdwardsPoint.«x86_64-tables» N)
    (hinputs : ∀ i < N.val, inputs[i]!.LimbsLt 52) (hinputs_on : ∀ i < N.val, inputs[i]!.OnCurve) :
    compress_batch inputs ⦃ (r : Array CompressedEdwardsY N) =>
      ∀ i < N.val, r[i]!.asNat = curve25519.encode inputs[i]!.toPoint ⦄ :=
  spec_mono (compress_batch_spec inputs hinputs) fun r hr i hi => by
    rw [hr i hi, encode_eq, EdwardsPoint.«x86_64-tables».toPoint_x (hinputs_on i hi),
      EdwardsPoint.«x86_64-tables».toPoint_y (hinputs_on i hi)]

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

open scoped Helpers.IndexStep in
/-- The first closure of `compress_batch`: `Z` of point `i`. -/
private theorem compress_batch.closure.call_mut_spec {N : Usize}
    (inputs : Array EdwardsPoint.«i686-tables» N) (i : Usize) (hi : i.val < N.val) :
    compress_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement2625.call_mut inputs i
      ⦃ (z : FieldElement2625) (c' : compress_batch.closure N) =>
        z = inputs[i.val]!.Z ∧ c' = inputs ⦄ := by
  unfold compress_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement2625.call_mut
  step as ⟨ep, hep⟩
  rw [hep]

open scoped Helpers.IndexStep in
/-- The second closure of `compress_batch`: compress `(X z, Y z)` for the inverse `z` of `Z`. -/
private theorem compress_batch.closure_1.call_mut_spec {N : Usize}
    (inputs : Array EdwardsPoint.«i686-tables» N) (zs : Array FieldElement2625 N) (i : Usize)
    (hi : i.val < N.val) (hinput : inputs[i.val]!.LimbsLt 26)
    (hz : zs[i.val]!.toField = inputs[i.val]!.Z.toField⁻¹)
    (hzb : (zs[i.val]!).LimbsLt 26) :
    compress_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeCompressedEdwardsY.call_mut
      (inputs, zs) i ⦃ (r : CompressedEdwardsY) (c' : compress_batch.closure_1 N) =>
        r.asNat = (inputs[i.val]!.Y.toField / inputs[i.val]!.Z.toField).val +
          2 ^ 255 * (if (inputs[i.val]!.X.toField / inputs[i.val]!.Z.toField).IsNeg then 1 else 0) ∧
        c' = (inputs, zs) ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hinput
  unfold compress_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeCompressedEdwardsY.call_mut
  step as ⟨ep, hep⟩
  step as ⟨fe, hfe⟩
  subst hep hfe
  step as ⟨x, hx, hxb⟩
  step as ⟨y, hy, hyb⟩
  step as ⟨cey, hcey⟩
  refine ⟨?_, rfl⟩
  rw [hcey, toField_mul_of_mod hx, toField_mul_of_mod hy, hz, div_eq_mul_inv, div_eq_mul_inv]

/-- `EdwardsPoint::compress_batch`: entry `i` is the canonical `y = Y / Z` of point `i` with the
sign of `x = X / Z` in bit `255`; limbs `< 2^26`. -/
@[step]
theorem compress_batch_spec {N : Usize} (inputs : Array EdwardsPoint.«i686-tables» N)
    (hinputs : ∀ i < N.val, inputs[i]!.LimbsLt 26) :
    compress_batch inputs ⦃ (r : Array CompressedEdwardsY N) =>
      ∀ i < N.val, r[i]!.asNat = (inputs[i]!.Y.toField / inputs[i]!.Z.toField).val +
        2 ^ 255 * (if (inputs[i]!.X.toField / inputs[i]!.Z.toField).IsNeg then 1 else 0) ⦄ := by
  unfold compress_batch
  apply spec_bind (core.array.from_fn_spec N _ inputs (fun _ c => c = inputs)
    (fun i z => z = inputs[i]!.Z) rfl fun i c hi hc => ?_)
  · intro zs hzs
    have hz : ∀ i < N.val, zs[i]! = inputs[i]!.Z := fun i hi => by
      rw [Array.getElem!_Nat_eq, getElem!_pos zs.val i (by simpa using hi)]
      exact hzs i (by simpa using hi)
    have hzb : ∀ i < N.val, (zs[i]!).LimbsLt 27 := fun i hi j hj => by
      rw [hz i hi]
      exact ((hinputs i hi).2.2.1 j hj).trans (by norm_num : (2 : ℕ) ^ 26 < 2 ^ 27)
    step as ⟨zs1, hzs1⟩
    apply spec_mono (core.array.from_fn_spec N _ (inputs, zs1) (fun _ c => c = (inputs, zs1))
      (fun i x => x.asNat = (inputs[i]!.Y.toField / inputs[i]!.Z.toField).val +
        2 ^ 255 * (if (inputs[i]!.X.toField / inputs[i]!.Z.toField).IsNeg then 1 else 0))
      rfl fun i c hi hc => ?_)
    · intro r hr i hi
      rw [Array.getElem!_Nat_eq, getElem!_pos r.val i (by simpa using hi)]
      exact hr i (by simpa using hi)
    · subst hc
      obtain ⟨h0, h1⟩ := hzs1 i.val hi
      rw [hz i.val hi] at h0 h1
      obtain ⟨hinv, hinvb⟩ := toField_inv_of_batch h0 h1 (hinputs i.val hi).2.2.1
      exact compress_batch.closure_1.call_mut_spec inputs zs1 i hi (hinputs i.val hi) hinv hinvb
  · subst c
    exact compress_batch.closure.call_mut_spec inputs i hi

/-- `EdwardsPoint::compress_batch`: entry `i` is RFC 8032's encoding of point `i`. -/
theorem compress_batch_spec_point {N : Usize} (inputs : Array EdwardsPoint.«i686-tables» N)
    (hinputs : ∀ i < N.val, inputs[i]!.LimbsLt 26) (hinputs_on : ∀ i < N.val, inputs[i]!.OnCurve) :
    compress_batch inputs ⦃ (r : Array CompressedEdwardsY N) =>
      ∀ i < N.val, r[i]!.asNat = curve25519.encode inputs[i]!.toPoint ⦄ :=
  spec_mono (compress_batch_spec inputs hinputs) fun r hr i hi => by
    rw [hr i hi, encode_eq, EdwardsPoint.«i686-tables».toPoint_x (hinputs_on i hi),
      EdwardsPoint.«i686-tables».toPoint_y (hinputs_on i hi)]

end «EdwardsPointi686-tables»

namespace «EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

open scoped Helpers.IndexStep in
/-- The first closure of `compress_batch`: `Z` of point `i`. -/
private theorem compress_batch.closure.call_mut_spec {N : Usize}
    (inputs : Array EdwardsPoint.«x86_64-no-tables» N) (i : Usize) (hi : i.val < N.val) :
    compress_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement51.call_mut inputs i
      ⦃ (z : FieldElement51) (c' : compress_batch.closure N) =>
        z = inputs[i.val]!.Z ∧ c' = inputs ⦄ := by
  unfold compress_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement51.call_mut
  step as ⟨ep, hep⟩
  rw [hep]

open scoped Helpers.IndexStep in
/-- The second closure of `compress_batch`: compress `(X z, Y z)` for the inverse `z` of `Z`. -/
private theorem compress_batch.closure_1.call_mut_spec {N : Usize}
    (inputs : Array EdwardsPoint.«x86_64-no-tables» N) (zs : Array FieldElement51 N) (i : Usize)
    (hi : i.val < N.val) (hinput : inputs[i.val]!.LimbsLt 52)
    (hz : zs[i.val]!.toField = inputs[i.val]!.Z.toField⁻¹)
    (hzb : (zs[i.val]!).LimbsLt 52) :
    compress_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeCompressedEdwardsY.call_mut
      (inputs, zs) i ⦃ (r : CompressedEdwardsY) (c' : compress_batch.closure_1 N) =>
        r.asNat = (inputs[i.val]!.Y.toField / inputs[i.val]!.Z.toField).val +
          2 ^ 255 * (if (inputs[i.val]!.X.toField / inputs[i.val]!.Z.toField).IsNeg then 1 else 0) ∧
        c' = (inputs, zs) ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hinput
  unfold compress_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeCompressedEdwardsY.call_mut
  step as ⟨ep, hep⟩
  step as ⟨fe, hfe⟩
  subst hep hfe
  step as ⟨x, hx, hxb⟩
  step as ⟨y, hy, hyb⟩
  step as ⟨cey, hcey⟩
  refine ⟨?_, rfl⟩
  rw [hcey, toField_mul_of_mod hx, toField_mul_of_mod hy, hz, div_eq_mul_inv, div_eq_mul_inv]

/-- `EdwardsPoint::compress_batch`: entry `i` is the canonical `y = Y / Z` of point `i` with the
sign of `x = X / Z` in bit `255`; limbs `< 2^52`. -/
@[step]
theorem compress_batch_spec {N : Usize} (inputs : Array EdwardsPoint.«x86_64-no-tables» N)
    (hinputs : ∀ i < N.val, inputs[i]!.LimbsLt 52) :
    compress_batch inputs ⦃ (r : Array CompressedEdwardsY N) =>
      ∀ i < N.val, r[i]!.asNat = (inputs[i]!.Y.toField / inputs[i]!.Z.toField).val +
        2 ^ 255 * (if (inputs[i]!.X.toField / inputs[i]!.Z.toField).IsNeg then 1 else 0) ⦄ := by
  unfold compress_batch
  apply spec_bind (core.array.from_fn_spec N _ inputs (fun _ c => c = inputs)
    (fun i z => z = inputs[i]!.Z) rfl fun i c hi hc => ?_)
  · intro zs hzs
    have hz : ∀ i < N.val, zs[i]! = inputs[i]!.Z := fun i hi => by
      rw [Array.getElem!_Nat_eq, getElem!_pos zs.val i (by simpa using hi)]
      exact hzs i (by simpa using hi)
    have hzb : ∀ i < N.val, (zs[i]!).LimbsLt 54 := fun i hi j hj => by
      rw [hz i hi]
      exact ((hinputs i hi).2.2.1 j hj).trans (by norm_num : (2 : ℕ) ^ 52 < 2 ^ 54)
    step as ⟨zs1, hzs1⟩
    apply spec_mono (core.array.from_fn_spec N _ (inputs, zs1) (fun _ c => c = (inputs, zs1))
      (fun i x => x.asNat = (inputs[i]!.Y.toField / inputs[i]!.Z.toField).val +
        2 ^ 255 * (if (inputs[i]!.X.toField / inputs[i]!.Z.toField).IsNeg then 1 else 0))
      rfl fun i c hi hc => ?_)
    · intro r hr i hi
      rw [Array.getElem!_Nat_eq, getElem!_pos r.val i (by simpa using hi)]
      exact hr i (by simpa using hi)
    · subst hc
      obtain ⟨h0, h1⟩ := hzs1 i.val hi
      rw [hz i.val hi] at h0 h1
      obtain ⟨hinv, hinvb⟩ := toField_inv_of_batch h0 h1 (hinputs i.val hi).2.2.1
      exact compress_batch.closure_1.call_mut_spec inputs zs1 i hi (hinputs i.val hi) hinv hinvb
  · subst c
    exact compress_batch.closure.call_mut_spec inputs i hi

/-- `EdwardsPoint::compress_batch`: entry `i` is RFC 8032's encoding of point `i`. -/
theorem compress_batch_spec_point {N : Usize} (inputs : Array EdwardsPoint.«x86_64-no-tables» N)
    (hinputs : ∀ i < N.val, inputs[i]!.LimbsLt 52) (hinputs_on : ∀ i < N.val, inputs[i]!.OnCurve) :
    compress_batch inputs ⦃ (r : Array CompressedEdwardsY N) =>
      ∀ i < N.val, r[i]!.asNat = curve25519.encode inputs[i]!.toPoint ⦄ :=
  spec_mono (compress_batch_spec inputs hinputs) fun r hr i hi => by
    rw [hr i hi, encode_eq, EdwardsPoint.«x86_64-no-tables».toPoint_x (hinputs_on i hi),
      EdwardsPoint.«x86_64-no-tables».toPoint_y (hinputs_on i hi)]

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

open scoped Helpers.IndexStep in
/-- The first closure of `compress_batch`: `Z` of point `i`. -/
private theorem compress_batch.closure.call_mut_spec {N : Usize}
    (inputs : Array EdwardsPoint.«i686-no-tables» N) (i : Usize) (hi : i.val < N.val) :
    compress_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement2625.call_mut inputs i
      ⦃ (z : FieldElement2625) (c' : compress_batch.closure N) =>
        z = inputs[i.val]!.Z ∧ c' = inputs ⦄ := by
  unfold compress_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement2625.call_mut
  step as ⟨ep, hep⟩
  rw [hep]

open scoped Helpers.IndexStep in
/-- The second closure of `compress_batch`: compress `(X z, Y z)` for the inverse `z` of `Z`. -/
private theorem compress_batch.closure_1.call_mut_spec {N : Usize}
    (inputs : Array EdwardsPoint.«i686-no-tables» N) (zs : Array FieldElement2625 N) (i : Usize)
    (hi : i.val < N.val) (hinput : inputs[i.val]!.LimbsLt 26)
    (hz : zs[i.val]!.toField = inputs[i.val]!.Z.toField⁻¹)
    (hzb : (zs[i.val]!).LimbsLt 26) :
    compress_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeCompressedEdwardsY.call_mut
      (inputs, zs) i ⦃ (r : CompressedEdwardsY) (c' : compress_batch.closure_1 N) =>
        r.asNat = (inputs[i.val]!.Y.toField / inputs[i.val]!.Z.toField).val +
          2 ^ 255 * (if (inputs[i.val]!.X.toField / inputs[i.val]!.Z.toField).IsNeg then 1 else 0) ∧
        c' = (inputs, zs) ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hinput
  unfold compress_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeCompressedEdwardsY.call_mut
  step as ⟨ep, hep⟩
  step as ⟨fe, hfe⟩
  subst hep hfe
  step as ⟨x, hx, hxb⟩
  step as ⟨y, hy, hyb⟩
  step as ⟨cey, hcey⟩
  refine ⟨?_, rfl⟩
  rw [hcey, toField_mul_of_mod hx, toField_mul_of_mod hy, hz, div_eq_mul_inv, div_eq_mul_inv]

/-- `EdwardsPoint::compress_batch`: entry `i` is the canonical `y = Y / Z` of point `i` with the
sign of `x = X / Z` in bit `255`; limbs `< 2^26`. -/
@[step]
theorem compress_batch_spec {N : Usize} (inputs : Array EdwardsPoint.«i686-no-tables» N)
    (hinputs : ∀ i < N.val, inputs[i]!.LimbsLt 26) :
    compress_batch inputs ⦃ (r : Array CompressedEdwardsY N) =>
      ∀ i < N.val, r[i]!.asNat = (inputs[i]!.Y.toField / inputs[i]!.Z.toField).val +
        2 ^ 255 * (if (inputs[i]!.X.toField / inputs[i]!.Z.toField).IsNeg then 1 else 0) ⦄ := by
  unfold compress_batch
  apply spec_bind (core.array.from_fn_spec N _ inputs (fun _ c => c = inputs)
    (fun i z => z = inputs[i]!.Z) rfl fun i c hi hc => ?_)
  · intro zs hzs
    have hz : ∀ i < N.val, zs[i]! = inputs[i]!.Z := fun i hi => by
      rw [Array.getElem!_Nat_eq, getElem!_pos zs.val i (by simpa using hi)]
      exact hzs i (by simpa using hi)
    have hzb : ∀ i < N.val, (zs[i]!).LimbsLt 27 := fun i hi j hj => by
      rw [hz i hi]
      exact ((hinputs i hi).2.2.1 j hj).trans (by norm_num : (2 : ℕ) ^ 26 < 2 ^ 27)
    step as ⟨zs1, hzs1⟩
    apply spec_mono (core.array.from_fn_spec N _ (inputs, zs1) (fun _ c => c = (inputs, zs1))
      (fun i x => x.asNat = (inputs[i]!.Y.toField / inputs[i]!.Z.toField).val +
        2 ^ 255 * (if (inputs[i]!.X.toField / inputs[i]!.Z.toField).IsNeg then 1 else 0))
      rfl fun i c hi hc => ?_)
    · intro r hr i hi
      rw [Array.getElem!_Nat_eq, getElem!_pos r.val i (by simpa using hi)]
      exact hr i (by simpa using hi)
    · subst hc
      obtain ⟨h0, h1⟩ := hzs1 i.val hi
      rw [hz i.val hi] at h0 h1
      obtain ⟨hinv, hinvb⟩ := toField_inv_of_batch h0 h1 (hinputs i.val hi).2.2.1
      exact compress_batch.closure_1.call_mut_spec inputs zs1 i hi (hinputs i.val hi) hinv hinvb
  · subst c
    exact compress_batch.closure.call_mut_spec inputs i hi

/-- `EdwardsPoint::compress_batch`: entry `i` is RFC 8032's encoding of point `i`. -/
theorem compress_batch_spec_point {N : Usize} (inputs : Array EdwardsPoint.«i686-no-tables» N)
    (hinputs : ∀ i < N.val, inputs[i]!.LimbsLt 26) (hinputs_on : ∀ i < N.val, inputs[i]!.OnCurve) :
    compress_batch inputs ⦃ (r : Array CompressedEdwardsY N) =>
      ∀ i < N.val, r[i]!.asNat = curve25519.encode inputs[i]!.toPoint ⦄ :=
  spec_mono (compress_batch_spec inputs hinputs) fun r hr i hi => by
    rw [hr i hi, encode_eq, EdwardsPoint.«i686-no-tables».toPoint_x (hinputs_on i hi),
      EdwardsPoint.«i686-no-tables».toPoint_y (hinputs_on i hi)]

end «EdwardsPointi686-no-tables»

end Curve25519Dalek.edwards
