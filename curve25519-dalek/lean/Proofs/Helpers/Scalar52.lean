/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.Scalar52
import Proofs.Helpers.Limbs
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
import Proofs.Helpers.Bitwise
public import Curve25519.Basic
import Proofs.Helpers.Montgomery
public section

/-! # Lemmas shared by the proofs of `backend/serial/u64/scalar.rs`

Five 52-bit limbs stay below the Montgomery radix `R = montgomeryRadix` (`Scalar52.asNat_lt`).
Modulo `L`, `R` can be cancelled (`mod_L_of_mul_montgomeryRadix`), and a Montgomery product with
`RR = R^2 mod L` multiplies by `R` (`mod_L_of_mul_montgomeryRadix_eq_mul_RR`). Five limbs
written over a `Scalar52` give its value (`Scalar52.asNat_set_five`) and its limb bounds
(`Scalar52.getElem!_set_five_lt`). `from_bytes` and `from_bytes_wide` cut their first limbs from
64-bit words alike (`limb1_of_words`, `limb2_of_words`, `limb3_of_words`). -/

open Aeneas Aeneas.Std curve25519

namespace Curve25519Dalek.backend.serial.u64.scalar

/-- Five limbs below `2 ^ 52` represent a number below the Montgomery radix. -/
theorem Scalar52.asNat_lt (a : Scalar52) (h : a.LimbsLt 52) :
    a.asNat < montgomeryRadix :=
  a.asNat_def ▸ (Array.asNat_lt 52 a h).trans_eq
    ((congrArg (2 ^ ·) (show 52 * (5#usize).val = 260 from rfl)).trans montgomeryRadix_def.symm)

/-- Limb 1 of the 52-bit limbs cut from 64-bit words: word 0 without its low 52 bits, and the
low 40 bits of word 1. -/
theorem limb1_of_words (w0 w1 : U64) :
    (w0.val >>> 52 ||| w1.val <<< 12 % U64.size) % 2 ^ 52
      = w0.val / 2 ^ 52 + 2 ^ 12 * (w1.val % 2 ^ 40) :=
  Nat.shiftRight_or_shiftLeft_mod _ (UScalar.hBounds _) (U64.two_pow_dvd_size (by norm_num))

/-- Limb 2 of the 52-bit limbs cut from 64-bit words: word 1 without its low 40 bits, and the
low 28 bits of word 2. -/
theorem limb2_of_words (w1 w2 : U64) :
    (w1.val >>> 40 ||| w2.val <<< 24 % U64.size) % 2 ^ 52
      = w1.val / 2 ^ 40 + 2 ^ 24 * (w2.val % 2 ^ 28) :=
  Nat.shiftRight_or_shiftLeft_mod _ (UScalar.hBounds _) (U64.two_pow_dvd_size (by norm_num))

/-- Limb 3 of the 52-bit limbs cut from 64-bit words: word 2 without its low 28 bits, and the
low 16 bits of word 3. -/
theorem limb3_of_words (w2 w3 : U64) :
    (w2.val >>> 28 ||| w3.val <<< 36 % U64.size) % 2 ^ 52
      = w2.val / 2 ^ 28 + 2 ^ 36 * (w3.val % 2 ^ 16) :=
  Nat.shiftRight_or_shiftLeft_mod _ (UScalar.hBounds _) (U64.two_pow_dvd_size (by norm_num))

/-- Multiplication by the Montgomery radix can be cancelled modulo `L`. -/
theorem mod_L_of_mul_montgomeryRadix {x y : ℕ}
    (h : x * montgomeryRadix % L = y * montgomeryRadix % L) : x % L = y % L :=
  Nat.ModEq.cancel_right_of_coprime montgomeryRadix_coprime_L.symm h

/-- A Montgomery product with `RR = R^2 mod L` multiplies by `R` modulo `L`. -/
theorem mod_L_of_mul_montgomeryRadix_eq_mul_RR {r x : ℕ}
    (h : r * montgomeryRadix % L = x * (montgomeryRadix ^ 2 % L) % L) :
    r % L = x * montgomeryRadix % L := by
  rw [← Nat.mod_mod (x * montgomeryRadix) L]
  apply mod_L_of_mul_montgomeryRadix
  rw [h, Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_two]

/-- The value of five limbs written over a `Scalar52`. -/
theorem Scalar52.asNat_set_five {r : Scalar52} (a : Scalar52) (x0 x1 x2 x3 x4 : U64)
    (hr : r = ((((a.set 0#usize x0).set 1#usize x1).set 2#usize x2).set 3#usize x3).set
      4#usize x4) :
    r.asNat = x0.val + 2 ^ 52 * x1.val + 2 ^ 104 * x2.val + 2 ^ 156 * x3.val
      + 2 ^ 208 * x4.val := by
  rw [hr, Scalar52.asNat_eq]
  simp_lists

/-- The limbs of five values written over a `Scalar52` are below a common bound. -/
theorem Scalar52.getElem!_set_five_lt {r : Scalar52} (a : Scalar52) (x0 x1 x2 x3 x4 : U64)
    {B : ℕ} (hr : r = ((((a.set 0#usize x0).set 1#usize x1).set 2#usize x2).set 3#usize x3).set
      4#usize x4)
    (h0 : x0.val < B) (h1 : x1.val < B) (h2 : x2.val < B) (h3 : x3.val < B) (h4 : x4.val < B) :
    ∀ i : ℕ, i < 5 → r[i]!.val < B := by
  rw [Nat.forall_lt_five, hr]
  simp_lists
  exact ⟨h0, h1, h2, h3, h4⟩

end Curve25519Dalek.backend.serial.u64.scalar
