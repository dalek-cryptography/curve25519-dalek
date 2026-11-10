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
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.field.FieldElement51

@[step]
theorem invert_batch_spec {N : Usize} (inputs : Array FieldElement51 N)
    (hinputs : ∀ i < N.val, (inputs[i]!).LimbsLt 54) :
    invert_batch inputs ⦃ (r : Array FieldElement51 N) =>
      ∀ i < N.val,
        (inputs[i]!.asNat % p = 0 → r[i]! = inputs[i]!) ∧
        (inputs[i]!.asNat % p ≠ 0 → r[i]!.asNat * inputs[i]!.asNat % p = 1 ∧
          (r[i]!).LimbsLt 52) ⦄ := by
  unfold invert_batch
  step as ⟨one, hone, honeb⟩
  step as ⟨s, back, hs, hback⟩
  step as ⟨s1, back1, hs1, hback1⟩
  step as ⟨s2, scratch, hs2len, hs2⟩
  have hsN : s.length = N.val := by
    simp only [Slice.length, hs]
    exact inputs.property
  have hget : ∀ i : ℕ, (back s2)[i]! = s2[i]! := by
    intro i
    rw [hback, Array.getElem!_Nat_eq, Array.from_slice_val _ _ (by simp [hs2len, hsN]),
      ← Slice.getElem!_Nat_eq]
  have hin : ∀ i : ℕ, inputs[i]! = s[i]! := by
    intro i
    rw [Array.getElem!_Nat_eq, Slice.getElem!_Nat_eq, hs]
  intro i hi
  rw [hget, hin]
  exact hs2 i (hsN ▸ hi)

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement2625

@[step]
theorem invert_batch_spec {N : Usize} (inputs : Array FieldElement2625 N)
    (hinputs : ∀ i < N.val, (inputs[i]!).LimbsLt 27) :
    invert_batch inputs ⦃ (r : Array FieldElement2625 N) =>
      ∀ i < N.val,
        (inputs[i]!.asNat % p = 0 → r[i]! = inputs[i]!) ∧
        (inputs[i]!.asNat % p ≠ 0 → r[i]!.asNat * inputs[i]!.asNat % p = 1 ∧
          (r[i]!).LimbsLt 26) ⦄ := by
  unfold invert_batch
  step as ⟨one, hone, honeb⟩
  step as ⟨s, back, hs, hback⟩
  step as ⟨s1, back1, hs1, hback1⟩
  step as ⟨s2, scratch, hs2len, hs2⟩
  have hsN : s.length = N.val := by
    simp only [Slice.length, hs]
    exact inputs.property
  have hget : ∀ i : ℕ, (back s2)[i]! = s2[i]! := by
    intro i
    rw [hback, Array.getElem!_Nat_eq, Array.from_slice_val _ _ (by simp [hs2len, hsN]),
      ← Slice.getElem!_Nat_eq]
  have hin : ∀ i : ℕ, inputs[i]! = s[i]! := by
    intro i
    rw [Array.getElem!_Nat_eq, Slice.getElem!_Nat_eq, hs]
  intro i hi
  rw [hget, hin]
  exact hs2 i (hsN ▸ hi)

end Curve25519Dalek.field.FieldElement2625
