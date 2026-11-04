/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong, Oliver Butterley
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.SquareLimbs
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51
@[local step]
private theorem pow2k_loop_spec (k : U32) (a : Array U64 5#usize) (hk : 0 < k.val)
    (ha : FieldElement51.LimbsLt 54 a) :
    pow2k_loop k a ⦃ (r : Array U64 5#usize) =>
      FieldElement51.asNat r % p = FieldElement51.asNat a ^ 2 ^ k.val % p ∧
      FieldElement51.LimbsLt 52 r ⦄ := by
  unfold pow2k_loop
  apply loop.spec_decr_nat (measure := fun s => s.1.val)
    (inv := fun s => 0 < s.1.val ∧ s.1.val ≤ k.val ∧ FieldElement51.LimbsLt 54 s.2 ∧
      FieldElement51.asNat s.2 % p = FieldElement51.asNat a ^ 2 ^ (k.val - s.1.val) % p)
  · rintro ⟨k', a'⟩ ⟨hk0, hkk, ha', hmod⟩
    unfold pow2k_loop.body
    step as ⟨a1, hsq, ha1⟩
    step as ⟨k1, hk1⟩
    have hpow : FieldElement51.asNat a1 % p =
        FieldElement51.asNat a ^ 2 ^ (k.val - k1.val) % p := by
      have he : k.val - k1.val = k.val - k'.val + 1 := by scalar_tac
      rw [hsq, Nat.pow_mod, hmod, ← Nat.pow_mod, ← pow_mul, ← pow_succ, he]
    by_cases hz : k1 = 0#u32
    · have hk1z : k1.val = 0 := by simp [hz]
      simp only [hz, ite_true, WP.spec_ok]
      exact ⟨by simpa [hk1z] using hpow, ha1⟩
    · have hk1z : k1.val ≠ 0 := fun h => hz (by scalar_tac)
      simp only [hz, ite_false, WP.spec_ok]
      exact ⟨by scalar_tac, by scalar_tac, fun i hi => (ha1 i hi).trans (by norm_num), hpow,
        by scalar_tac⟩
  · exact ⟨hk, le_refl _, ha, by simp⟩

@[step]
theorem pow2k_spec (self : FieldElement51) (k : U32) (hk : 0 < k.val)
    (hself : self.LimbsLt 54) :
    pow2k self k ⦃ (r : FieldElement51) =>
      r.asNat % p = self.asNat ^ 2 ^ k.val % p ∧ r.LimbsLt 52 ⦄ := by
  unfold pow2k
  step*
end Curve25519Dalek.backend.serial.u64.field.FieldElement51
