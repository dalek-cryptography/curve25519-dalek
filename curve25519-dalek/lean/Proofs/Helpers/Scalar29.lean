/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.Scalar29
public import Curve25519Dalek.Funs
public import Curve25519.Basic
import Proofs.Helpers.AsNat
import Proofs.Helpers.Bitwise
public import Aeneas
public section

/-! # Lemmas shared by the proofs of `backend/serial/u32/scalar.rs`

The Montgomery radix `R = 2^261` modulo `L` (as for `R = 2^260` in
`Proofs/Helpers/Montgomery.lean`), nine 29-bit limbs stay below `R` (`Scalar29.asNat_lt`), and
`R` can be cancelled modulo `L` (`mod_L_of_mul_montgomeryRadix`,
`mod_L_of_mul_montgomeryRadix_eq_mul_RR`), as it is a unit of `ZMod L`
(`montgomeryRadix_natCast_ne_zero`). The product of two `Scalar`s stays below `R * L`
(`mul_lt_montgomeryRadix_mul_L`). -/

open Aeneas Aeneas.Std Result curve25519

namespace Curve25519Dalek.backend.serial.u32.scalar

set_option exponentiation.threshold 300 in
theorem L_lt_montgomeryRadix : L < montgomeryRadix := by
  rw [montgomeryRadix_def]
  exact L_lt_two_pow_253.trans (Nat.pow_lt_pow_right (by decide) (by decide))

set_option exponentiation.threshold 300 in
/-- The sum of two scalars below `L` does not wrap around. -/
theorem two_mul_L_lt_montgomeryRadix : 2 * L < montgomeryRadix := by
  rw [montgomeryRadix_def]
  calc 2 * L < 2 * 2 ^ 253 := Nat.mul_lt_mul_of_pos_left L_lt_two_pow_253 (by decide)
    _ = 2 ^ 254 := Nat.pow_succ'.symm
    _ ≤ 2 ^ 261 := Nat.pow_le_pow_right (by decide) (by decide)

set_option exponentiation.threshold 300 in
/-- `L` is odd, so the Montgomery radix is invertible modulo `L`. -/
theorem montgomeryRadix_coprime_L : Nat.Coprime montgomeryRadix L := by
  rw [montgomeryRadix_def]
  exact Nat.Coprime.pow_left 261 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr L_mod_two))

theorem montgomeryRadix_mod_L :
    montgomeryRadix % L =
      7237005577332262213973186563042994226653049657365262595645758789353026222573 := by
  rw [montgomeryRadix_def, L_eq_numeral]
  decide +kernel

theorem montgomeryRadix_sq_mod_L :
    montgomeryRadix ^ 2 % L =
      2269390412388210757387596145591141548687583832901957660833925789855294397714 := by
  rw [montgomeryRadix_def, L_eq_numeral]
  decide +kernel

/-- `L` in nine radix-`2^29` limbs. -/
theorem L_eq_limbs29 :
    L = 485872621 + 2 ^ 29 * 9640146 + 2 ^ 58 * 501691798 + 2 ^ 87 * 502512965 +
      2 ^ 116 * 333 + 2 ^ 145 * 0 + 2 ^ 174 * 0 + 2 ^ 203 * 0 + 2 ^ 232 * 1048576 := by
  rw [L_eq_numeral]
  decide

theorem L_mod_two_pow_29 : L % 2 ^ 29 = 485872621 := by
  rw [L_eq_numeral]
  decide

/-- Nine limbs below `2 ^ 29` represent a number below the Montgomery radix. -/
theorem Scalar29.asNat_lt (a : Scalar29) (h : a.LimbsLt 29) :
    a.asNat < montgomeryRadix :=
  a.asNat_def ▸ (Array.asNat_lt 29 a h).trans_eq
    ((congrArg (2 ^ ·) (show 29 * (9#usize).val = 261 from rfl)).trans montgomeryRadix_def.symm)

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

/-- The value of a `Scalar29` written out as its nine weighted limbs. -/
theorem Scalar29.asNat_eq (a : Scalar29) :
    a.asNat = a[0]!.val + 2 ^ 29 * a[1]!.val + 2 ^ 58 * a[2]!.val + 2 ^ 87 * a[3]!.val
      + 2 ^ 116 * a[4]!.val + 2 ^ 145 * a[5]!.val + 2 ^ 174 * a[6]!.val + 2 ^ 203 * a[7]!.val
      + 2 ^ 232 * a[8]!.val := by
  rw [a.asNat_def, Array.asNat_nine]

/-- A limb of 29 bits cut from two 32-bit words: word `w` shifted right by `r`, and the low `m`
bits of word `w'` above it. -/
theorem limb_of_words (w w' : U32) {r s m : ℕ} (hrs : r + s = 32) (hms : m + s = 29) :
    (w.val >>> r ||| w'.val <<< s % U32.size) % 2 ^ 29
      = w.val / 2 ^ r + 2 ^ s * (w'.val % 2 ^ m) := by
  have hx : w.val < 2 ^ (r + s) := by rw [hrs]; exact UScalar.hBounds w
  have hM : 2 ^ (m + s) ∣ U32.size := by
    rw [hms, show U32.size = 2 ^ 32 by simp [U32.size, U32.numBits]]
    exact Nat.pow_dvd_pow 2 (by norm_num)
  rw [← hms]
  exact Nat.shiftRight_or_shiftLeft_mod _ hx hM

/-- The value of nine limbs written over a `Scalar29`. -/
theorem Scalar29.asNat_set_nine {r : Scalar29} (a : Scalar29) (x0 x1 x2 x3 x4 x5 x6 x7 x8 : U32)
    (hr : r = ((((((((a.set 0#usize x0).set 1#usize x1).set 2#usize x2).set 3#usize x3).set
      4#usize x4).set 5#usize x5).set 6#usize x6).set 7#usize x7).set 8#usize x8) :
    r.asNat = x0.val + 2 ^ 29 * x1.val + 2 ^ 58 * x2.val + 2 ^ 87 * x3.val + 2 ^ 116 * x4.val
      + 2 ^ 145 * x5.val + 2 ^ 174 * x6.val + 2 ^ 203 * x7.val + 2 ^ 232 * x8.val := by
  rw [hr, Scalar29.asNat_eq]
  simp_lists

/-- The limbs of nine values written over a `Scalar29` are below a common bound. -/
theorem Scalar29.getElem!_set_nine_lt {r : Scalar29} (a : Scalar29)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : U32) {B : ℕ}
    (hr : r = ((((((((a.set 0#usize x0).set 1#usize x1).set 2#usize x2).set 3#usize x3).set
      4#usize x4).set 5#usize x5).set 6#usize x6).set 7#usize x7).set 8#usize x8)
    (h0 : x0.val < B) (h1 : x1.val < B) (h2 : x2.val < B) (h3 : x3.val < B) (h4 : x4.val < B)
    (h5 : x5.val < B) (h6 : x6.val < B) (h7 : x7.val < B) (h8 : x8.val < B) :
    ∀ i : ℕ, i < 9 → r[i]!.val < B := by
  intro i hi
  rw [hr]
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  all_goals first | omega | (simp_lists; assumption)

/-- Indexing a `Scalar29` in bounds returns the limb. -/
theorem Scalar29.index_eq (a : Scalar29) (j : Usize) (h_j : j.val < 9) :
    Scalar29.Insts.CoreOpsIndexIndexUsizeU32.index a j = ok a.val[j.val]! := by
  have h : j.val < a.val.length := by simp [h_j]
  simp [Scalar29.Insts.CoreOpsIndexIndexUsizeU32.index, Array.index_usize,
    List.getElem?_eq_getElem h]

set_option exponentiation.threshold 300 in
/-- Two numbers below `2 ^ 256` have a product below `R * L`. -/
theorem mul_lt_montgomeryRadix_mul_L {a b : ℕ} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    a * b < montgomeryRadix * L := by
  have h (n k m : ℕ) (hkm : n + n ≤ k + m) : 2 ^ n * 2 ^ n ≤ 2 ^ k * 2 ^ m := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) hkm
  calc a * b < 2 ^ 256 * 2 ^ 256 := Nat.mul_lt_mul'' ha hb
    _ ≤ montgomeryRadix * 2 ^ 252 := montgomeryRadix_def ▸ h 256 261 252 (by decide)
    _ ≤ montgomeryRadix * L := Nat.mul_le_mul_left _ two_pow_252_lt_L.le

/-- The Montgomery radix is invertible modulo `L`. -/
theorem montgomeryRadix_natCast_ne_zero : (montgomeryRadix : ZMod L) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (montgomeryRadix_coprime_L.symm.eq_one_of_dvd h)
    (ne_of_gt ((Nat.one_lt_two_pow (by decide)).trans two_pow_252_lt_L))

end Curve25519Dalek.backend.serial.u32.scalar

namespace Aeneas.Std

open Result

/-- Indexing an array in bounds returns the element. -/
theorem Array.index_usize_eq {α : Type} [Inhabited α] {n : Usize} (a : Array α n) (i : Usize)
    (hi : i.val < n.val) : Array.index_usize a i = ok a[i.val]! := by
  have h : i.val < a.val.length := by simp [hi]
  simp [Array.index_usize, Array.getElem!_Nat_eq, List.getElem?_eq_getElem h]

/-- Updating an array in bounds returns the array with the element set. -/
theorem Array.update_eq {α : Type} {n : Usize} (a : Array α n) (i : Usize) (x : α)
    (hi : i.val < n.val) : Array.update a i x = ok (a.set i x) := by
  have h : i.val < a.val.length := by simp [hi]
  simp [Array.update, Array.set, List.getElem?_eq_getElem h]

end Aeneas.Std
