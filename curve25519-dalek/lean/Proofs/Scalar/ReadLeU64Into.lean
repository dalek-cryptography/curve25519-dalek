/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander, Hoang Le Truong
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar52
import Mathlib.Tactic.ReduceModChar
import Proofs.Helpers.Iterator
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
import Proofs.Helpers.Bitwise
import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

/-- A little-endian byte list read as a bit vector has the value of its digits in radix `256`. -/
private theorem BitVec.toNat_fromLEBytes (l : List Byte) :
    (BitVec.fromLEBytes l).toNat = Nat.ofDigits 256 (l.map BitVec.toNat) := by
  induction l with
  | nil => simp [BitVec.fromLEBytes]
  | cons b l ih =>
    have hlt : (BitVec.fromLEBytes l).toNat < 2 ^ (8 * l.length) := (BitVec.fromLEBytes l).isLt
    have hb : b.toNat < 2 ^ 8 := b.isLt
    have hpow : 2 ^ (8 * l.length) * 2 ^ 8 = 2 ^ (8 * (l.length + 1)) := by
      rw [← Nat.pow_add]; ring_nf
    have hlt' : (BitVec.fromLEBytes l).toNat < 2 ^ (8 * (l.length + 1)) :=
      lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hsh : (BitVec.fromLEBytes l).toNat <<< 8 < 2 ^ (8 * (l.length + 1)) := by
      rw [Nat.shiftLeft_eq, ← hpow]
      exact Nat.mul_lt_mul_of_pos_right hlt (by positivity)
    have hb' : b.toNat < 2 ^ (8 * (l.length + 1)) :=
      lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [BitVec.fromLEBytes, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      BitVec.toNat_setWidth, List.length_cons, Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt hlt',
      Nat.mod_eq_of_lt hsh, Nat.or_shiftLeft_eq_add_pow_mul _ hb, ih, List.map_cons,
      Nat.ofDigits_cons]
    rfl

namespace Curve25519Dalek.scalar

/-- The loop of `read_le_u64_into` reads each word of `dst` from 8 bytes of `src`. -/
@[local step]
private theorem read_le_u64_into_loop_spec (src : Slice U8) (dst : Slice U64)
    (hsrc : src.length = 8 * dst.length) :
    read_le_u64_into_loop { start := 0#usize, «end» := dst.len } src dst ⦃ (r : Slice U64) =>
      r.length = dst.length ∧
      ∀ i < dst.length, ∀ j : ℕ, j < 8 →
        r[i]!.val / 2 ^ (8 * j) % 2 ^ 8 = src[8 * i + j]!.val ⦄ := by
  unfold read_le_u64_into_loop
  apply loop.spec_decr_nat (measure := fun (it, _) => it.end.val - it.start.val)
    (inv := fun (it, d) => it.end.val = dst.length ∧
      d.length = dst.length ∧ it.start.val ≤ dst.length ∧
      ∀ i < it.start.val, ∀ j : ℕ, j < 8 → d[i]!.val / 2 ^ (8 * j) % 2 ^ 8 = src[8 * i + j]!.val)
  · rintro ⟨it, d⟩ ⟨hend, hd, hk, hdone⟩
    let k := it.start
    unfold read_le_u64_into_loop.body
    by_cases hlt : k.val < d.length
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨o, it1, ho, hstart, hend1⟩
      subst ho
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      step as ⟨bytes, hbytes, hblen⟩
      step as ⟨r, hr⟩
      rcases r with a | e
      · obtain ⟨ha, -⟩ := hr
        simp only [core.result.Result.expect]
        step as ⟨x, hx⟩
        step as ⟨d1, hd1⟩
        have hword (j : ℕ) (hj : j < 8) :
            x.val / 2 ^ (8 * j) % 2 ^ 8 = src[8 * k.val + j]!.val := by
          have hL : ∀ c ∈ a.val.map (·.val), c < 256 := by
            intro c hc
            obtain ⟨y, -, rfl⟩ := List.mem_map.mp hc
            exact y.hBounds
          have hxv : x.val = Nat.ofDigits 256 (a.val.map (·.val)) := by
            have h1 := congrArg BitVec.toNat hx
            rw [BitVec.toNat_cast, BitVec.toNat_fromLEBytes, List.map_map] at h1
            exact h1
          rw [hxv, pow_mul, show (2 : ℕ) ^ 8 = 256 by norm_num,
            Nat.ofDigits_div_pow_mod 256 _ hL j,
            List.getElem!_map_eq _ _ _ (by simp only [ha, hblen]; scalar_tac), ha, hbytes,
            List.getElem!_slice _ _ _ _ (by scalar_tac), hi2, Slice.getElem!_Nat_eq]
        refine ⟨by simpa [hend1] using hend, by simp [hd1, hd], by scalar_tac, fun i hi j hj => ?_,
          by scalar_tac⟩
        by_cases hik : i = k.val
        · rw [hd1, Slice.getElem!_Nat_set_eq _ _ _ _ ⟨hik.symm, by scalar_tac⟩, hik]
          exact hword j hj
        · rw [hd1, Slice.getElem!_Nat_set_ne _ _ _ _ (Ne.symm hik)]
          exact hdone i (by scalar_tac) j hj
      · exact absurd hblen (by scalar_tac)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      exact ⟨hd, fun i hi j hj => hdone i (by scalar_tac) j hj⟩
  · simp

@[step]
theorem read_le_u64_into_spec (src : Slice U8) (dst : Slice U64)
    (hsrc : src.length = 8 * dst.length) :
    read_le_u64_into src dst ⦃ (r : Slice U64) =>
      r.length = dst.length ∧
      ∀ i < dst.length, ∀ j : ℕ, j < 8 →
        r[i]!.val / 2 ^ (8 * j) % 2 ^ 8 = src[8 * i + j]!.val ⦄ := by
  unfold read_le_u64_into
  step*

end Curve25519Dalek.scalar
