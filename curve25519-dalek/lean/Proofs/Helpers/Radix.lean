/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public section

/-! # Curve25519 constants in dalek's radices

The group order `L` in radix `2^52` (dalek's `Scalar52`), the square root of `-1` in radix `2^51`
(dalek's `FieldElement51`), and the Montgomery radices `2^260`, `2^520` modulo `L`. These are facts
about the numerals of `Curve25519.Basic` that only the backend proofs need, kept out of the
implementation-independent `Curve25519` library. -/

namespace curve25519

/-- `L` in radix `2^52`, the representation of dalek's `Scalar52`. -/
theorem L_eq_limbs :
    L = 671914833335277 + 2 ^ 52 * 3916664325105025 + 2 ^ 104 * 1367801 + 2 ^ 156 * 0
      + 2 ^ 208 * 17592186044416 := by
  rw [L_eq_numeral]
  decide

theorem L_mod_two_pow_52 : L % 2 ^ 52 = 671914833335277 := by rw [L_eq_numeral]; decide

/-- The Montgomery radix `2^260` modulo `L`. -/
theorem two_pow_260_mod_L :
    2 ^ 260 % L =
      7237005577332262213973186563042994233755083008372585100823854863819240236781 := by
  rw [L_eq_numeral]
  decide +kernel

theorem two_pow_520_mod_L :
    2 ^ 520 % L =
      4185850391763183796333492317919282507600454137915443218209456916606550724923 := by
  rw [L_eq_numeral]
  decide +kernel

/-- `sqrtM1` in radix `2^51`, the representation of dalek's `FieldElement51`. -/
theorem sqrtM1_eq_limbs :
    sqrtM1 = 1718705420411056 + 2 ^ 51 * 234908883556509 + 2 ^ 102 * 2233514472574048
      + 2 ^ 153 * 2117202627021982 + 2 ^ 204 * 765476049583133 := by
  rw [sqrtM1_def]
  decide

end curve25519
