/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
module
public import Curve25519.Basic
public import Defs.Scalar52
import Proofs.Helpers.Radix
public section

/-! # Facts about the Montgomery radix `R = 2^260` modulo `L` -/

namespace Curve25519Dalek.backend.serial.u64

theorem scalar.L_lt_montgomeryRadix : curve25519.L < scalar.montgomeryRadix :=
  scalar.montgomeryRadix_def ▸ curve25519.L_lt_two_pow_260

/-- The sum of two scalars below `L` does not wrap around. -/
theorem scalar.two_mul_L_lt_montgomeryRadix : 2 * curve25519.L < scalar.montgomeryRadix := by
  have h (k : ℕ) (hk : 254 ≤ k) : 2 * curve25519.L < 2 ^ k :=
    calc 2 * curve25519.L < 2 * 2 ^ 253 :=
        Nat.mul_lt_mul_of_pos_left curve25519.L_lt_two_pow_253 (by decide)
      _ = 2 ^ 254 := Nat.pow_succ'.symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  exact scalar.montgomeryRadix_def ▸ h 260 (by decide)

/-- `L` is odd, so the Montgomery radix is invertible modulo `L`. -/
theorem scalar.montgomeryRadix_coprime_L : Nat.Coprime scalar.montgomeryRadix curve25519.L := by
  have h (k : ℕ) : Nat.Coprime (2 ^ k) curve25519.L :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr curve25519.L_mod_two))
  exact scalar.montgomeryRadix_def ▸ h 260

theorem scalar.montgomeryRadix_mod_L :
    scalar.montgomeryRadix % curve25519.L =
      7237005577332262213973186563042994233755083008372585100823854863819240236781 := by
  rw [scalar.montgomeryRadix_def, curve25519.two_pow_260_mod_L]

theorem scalar.montgomeryRadix_sq_mod_L :
    scalar.montgomeryRadix ^ 2 % curve25519.L =
      4185850391763183796333492317919282507600454137915443218209456916606550724923 := by
  rw [scalar.montgomeryRadix_def, ← pow_mul, curve25519.two_pow_520_mod_L]

end Curve25519Dalek.backend.serial.u64
