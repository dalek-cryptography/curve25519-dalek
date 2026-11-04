/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
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
theorem invert_batch.«x86_64-tables_spec» {N : Usize} (inputs : Array Scalar N)
    (hinputs : ∀ i < N.val, inputs[i]!.asNat % L ≠ 0) :
    invert_batch.«x86_64-tables» inputs ⦃ (ret : Scalar) (r : Array Scalar N) =>
      (∀ i < N.val, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range N.val, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ := by
  unfold invert_batch.«x86_64-tables»
  step as ⟨one, hone, honeb⟩
  step as ⟨acc, hacc, haccb⟩
  step as ⟨s, back, hs, hback⟩
  step as ⟨s1, back1, hs1, hback1⟩
  have hsN : s.length = N.val := by
    simp only [Slice.length, hs]
    exact inputs.property
  have hs1N : s1.length = s.length := by
    simp only [Slice.length, hs1, hs, Array.repeat_val, List.length_replicate]
    exact inputs.property.symm
  have hin : ∀ i : ℕ, inputs[i]! = s[i]! := by
    intro i
    rw [Array.getElem!_Nat_eq, Slice.getElem!_Nat_eq, hs]
  step with invert_batch_internal.«x86_64-tables_spec» s s1 hs1N
    (fun i hi => hin i ▸ hinputs i (hsN ▸ hi)) as ⟨ret, r, sc, hrl, hr, hret, hretL⟩
  have hget : ∀ i : ℕ, (back r)[i]! = r[i]! := by
    intro i
    rw [hback, Array.getElem!_Nat_eq, Array.from_slice_val _ _ (by simp [hrl, hsN]),
      ← Slice.getElem!_Nat_eq]
  refine ⟨fun i hi => ?_, ?_, hretL⟩
  · rw [hget, hin]
    exact hr i (hsN ▸ hi)
  · rw [← hsN, Finset.prod_congr rfl fun i _ => congrArg Scalar.asNat (hin i)]
    exact hret

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert_batch.«x86_64-no-tables_spec» {N : Usize} (inputs : Array Scalar N)
    (hinputs : ∀ i < N.val, inputs[i]!.asNat % L ≠ 0) :
    invert_batch.«x86_64-no-tables» inputs ⦃ (ret : Scalar) (r : Array Scalar N) =>
      (∀ i < N.val, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range N.val, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  invert_batch.«x86_64-tables_spec» inputs hinputs

end Curve25519Dalek.scalar.Scalar


namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert_batch.«i686-tables_spec» {N : Usize} (inputs : Array Scalar N)
    (hinputs : ∀ i < N.val, inputs[i]!.asNat % L ≠ 0) :
    invert_batch.«i686-tables» inputs ⦃ (ret : Scalar) (r : Array Scalar N) =>
      (∀ i < N.val, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range N.val, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ := by
  unfold invert_batch.«i686-tables»
  step as ⟨one, hone, honeb⟩
  step as ⟨acc, hacc, haccb⟩
  step as ⟨s, back, hs, hback⟩
  step as ⟨s1, back1, hs1, hback1⟩
  have hsN : s.length = N.val := by
    simp only [Slice.length, hs]
    exact inputs.property
  have hs1N : s1.length = s.length := by
    simp only [Slice.length, hs1, hs, Array.repeat_val, List.length_replicate]
    exact inputs.property.symm
  have hin : ∀ i : ℕ, inputs[i]! = s[i]! := by
    intro i
    rw [Array.getElem!_Nat_eq, Slice.getElem!_Nat_eq, hs]
  step with invert_batch_internal.«i686-tables_spec» s s1 hs1N
    (fun i hi => hin i ▸ hinputs i (hsN ▸ hi)) as ⟨ret, r, sc, hrl, hr, hret, hretL⟩
  have hget : ∀ i : ℕ, (back r)[i]! = r[i]! := by
    intro i
    rw [hback, Array.getElem!_Nat_eq, Array.from_slice_val _ _ (by simp [hrl, hsN]),
      ← Slice.getElem!_Nat_eq]
  refine ⟨fun i hi => ?_, ?_, hretL⟩
  · rw [hget, hin]
    exact hr i (hsN ▸ hi)
  · rw [← hsN, Finset.prod_congr rfl fun i _ => congrArg Scalar.asNat (hin i)]
    exact hret

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert_batch.«i686-no-tables_spec» {N : Usize} (inputs : Array Scalar N)
    (hinputs : ∀ i < N.val, inputs[i]!.asNat % L ≠ 0) :
    invert_batch.«i686-no-tables» inputs ⦃ (ret : Scalar) (r : Array Scalar N) =>
      (∀ i < N.val, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range N.val, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  invert_batch.«i686-tables_spec» inputs hinputs

end Curve25519Dalek.scalar.Scalar
namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert_batch_spec {N : Usize} (inputs : Array Scalar N)
    (hinputs : ∀ i < N.val, inputs[i]!.asNat % L ≠ 0) :
    invert_batch inputs ⦃ (ret : Scalar) (r : Array Scalar N) =>
      (∀ i < N.val, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range N.val, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ := by
  unfold invert_batch
  exact dispatch_all_spec
    (invert_batch.«x86_64-tables_spec» inputs hinputs)
    (invert_batch.«x86_64-no-tables_spec» inputs hinputs)
    (invert_batch.«i686-tables_spec» inputs hinputs)
    (invert_batch.«i686-no-tables_spec» inputs hinputs)

end Curve25519Dalek.scalar.Scalar
