/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.Scalar52
public import Defs.Scalar
import Proofs.Helpers.AsNat
public import Curve25519.Basic
import Proofs.Helpers.Montgomery
public section

/-! # Lemmas shared by the proofs of `src/scalar.rs`

A `Scalar` is below `2 ^ 256` (`Scalar.asNat_lt`), so the product of two of them stays below
`R * L` (`mul_lt_montgomeryRadix_mul_L`), as the Montgomery reduction requires; values below `L`
can be packed (`lt_two_pow_256_of_lt_L`). The Montgomery radix `R` is a unit of `ZMod L`
(`montgomeryRadix_natCast_ne_zero`). -/

open Aeneas Aeneas.Std curve25519
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix montgomeryRadix_def
  montgomeryRadix_coprime_L)

namespace Curve25519Dalek.scalar

/-- The 32 bytes of a `Scalar` represent a number below `2 ^ 256`. -/
theorem Scalar.asNat_lt (s : Scalar) : s.asNat < 2 ^ 256 :=
  s.asNat_def ▸ Array.asNat_lt 8 s.bytes fun i _ => s.bytes[i]!.hBounds

/-- Byte 31 of a `Scalar` is its value divided by `2 ^ 248`. -/
theorem Scalar.bytes_31_val (s : Scalar) : s.bytes[31]!.val = s.asNat / 2 ^ 248 :=
  s.asNat_def ▸
    Array.getElem!_last_eq_asNat_div 8 s.bytes (fun i _ => s.bytes[i]!.hBounds) (by decide)

/-- A `Scalar` below `2 ^ (248 + k)` has byte 31 below `2 ^ k`. -/
theorem Scalar.bytes_31_lt {s : Scalar} {k : ℕ} (h : s.asNat < 2 ^ (248 + k)) :
    s.bytes[31]!.val < 2 ^ k := by
  rw [Scalar.bytes_31_val]
  exact Nat.div_lt_of_lt_mul (by rwa [← Nat.pow_add])

/-- Numbers below `L` are below `2 ^ 256`, as `pack` requires. -/
theorem lt_two_pow_256_of_lt_L {x : ℕ} (h : x < L) : x < 2 ^ 256 :=
  h.trans (L_lt_two_pow_253.trans (Nat.pow_lt_pow_right (by decide) (by decide)))

/-- Two numbers below `2 ^ 256` have a product below `R * L`. -/
theorem mul_lt_montgomeryRadix_mul_L {a b : ℕ} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    a * b < montgomeryRadix * L := by
  have h (n k m : ℕ) (hkm : n + n ≤ k + m) : 2 ^ n * 2 ^ n ≤ 2 ^ k * 2 ^ m := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) hkm
  calc a * b < 2 ^ 256 * 2 ^ 256 := Nat.mul_lt_mul'' ha hb
    _ ≤ montgomeryRadix * 2 ^ 252 := montgomeryRadix_def ▸ h 256 260 252 (by decide)
    _ ≤ montgomeryRadix * L := Nat.mul_le_mul_left _ two_pow_252_lt_L.le

/-- The Montgomery radix is invertible modulo `L`. -/
theorem montgomeryRadix_natCast_ne_zero : (montgomeryRadix : ZMod L) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (montgomeryRadix_coprime_L.symm.eq_one_of_dvd h)
    (ne_of_gt ((Nat.one_lt_two_pow (by decide)).trans two_pow_252_lt_L))

end Curve25519Dalek.scalar
