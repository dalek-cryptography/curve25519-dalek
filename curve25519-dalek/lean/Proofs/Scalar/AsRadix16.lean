/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar
import Mathlib.Tactic.ReduceModChar
import Proofs.Helpers.Array
import Proofs.Helpers.AsInt
import Proofs.Helpers.AsNat
import Proofs.Helpers.Scalar
import Proofs.Scalar.Index
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

/-- A sum over `2 m` terms, grouped in consecutive pairs. -/
private theorem Finset.sum_range_two_mul {M : Type*} [AddCommMonoid M] (m : ℕ) (f : ℕ → M) :
    ∑ j ∈ Finset.range (2 * m), f j =
      ∑ i ∈ Finset.range m, (f (2 * i) + f (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

/-- Signed digits in radix `2 ^ bits` whose consecutive pairs combine to the digits of `b` in radix
`2 ^ (2 bits)` have the value of `b`. -/
private theorem Aeneas.Std.Array.asInt_eq_asNat_of_pairs {tyI : IScalarTy} {tyU : UScalarTy}
    {n m : Usize} (bits : ℕ) (a : Array (IScalar tyI) n) (b : Array (UScalar tyU) m)
    (h : n.val = 2 * m.val)
    (hab : ∀ i < m.val, a[2 * i]!.val + 2 ^ bits * a[2 * i + 1]!.val = b[i]!.val) :
    a.asInt bits = b.asNat (2 * bits) := by
  rw [Array.asInt_eq_sum, Array.asNat_eq_sum, h, Finset.sum_range_two_mul]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← hab i (Finset.mem_range.mp hi)]
  ring

namespace Curve25519Dalek.scalar.Scalar.as_radix_16

@[step]
theorem bot_half_spec (x : U8) :
    bot_half x ⦃ (r : U8) =>
      r.val = x.val % 16 ⦄ := by
  unfold bot_half
  step as ⟨i, hi, hibv⟩
  simp only [UScalar.val_and, hi]
  exact Nat.and_two_pow_sub_one_eq_mod _ 4

end Curve25519Dalek.scalar.Scalar.as_radix_16

namespace Curve25519Dalek.scalar.Scalar.as_radix_16

@[step]
theorem top_half_spec (x : U8) :
    top_half x ⦃ (r : U8) =>
      16 * r.val + x.val % 16 = x.val ⦄ := by
  unfold top_half
  step as ⟨i, hi, hibv⟩
  simp only [UScalar.val_and, hi]
  rw [show (15#u8).val = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]
  scalar_tac

end Curve25519Dalek.scalar.Scalar.as_radix_16

namespace Curve25519Dalek.scalar.Scalar

/-- The bytes below `s` are split into their nibbles at entries `2 i`, `2 i + 1` of `out`. -/
private def Loop0Inv (self : Scalar) (out : Array I8 64#usize) (s : ℕ) : Prop :=
  ∀ i < s, out[2 * i]!.val = ((self.bytes[i]!.val % 16 : ℕ) : ℤ) ∧
    out[2 * i + 1]!.val = ((self.bytes[i]!.val / 16 : ℕ) : ℤ)

/-- For `i < s`, the entries `2 i`, `2 i + 1` are not `2 s`, `2 s + 1`. -/
private theorem two_mul_ne {i s : ℕ} (h : i < s) :
    (2 * i ≠ 2 * s ∧ 2 * i ≠ 2 * s + 1) ∧ 2 * i + 1 ≠ 2 * s ∧ 2 * i + 1 ≠ 2 * s + 1 := by
  omega

/-- The quotient from `top_half`. -/
private theorem eq_div_sixteen {t x : ℕ} (h : 16 * t + x % 16 = x) : t = x / 16 := by
  omega

/-- Writing the nibbles of byte `s` extends the invariant to `s + 1`. -/
private theorem loop0_inv_succ {self : Scalar} {out out2 : Array I8 64#usize} {s : ℕ}
    (hinv : Loop0Inv self out s)
    (h0 : out2[2 * s]!.val = ((self.bytes[s]!.val % 16 : ℕ) : ℤ))
    (h1 : out2[2 * s + 1]!.val = ((self.bytes[s]!.val / 16 : ℕ) : ℤ))
    (hrest : ∀ j, j ≠ 2 * s → j ≠ 2 * s + 1 → out2[j]! = out[j]!) :
    Loop0Inv self out2 (s + 1) := by
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
  · obtain ⟨⟨h00, h01⟩, h10, h11⟩ := two_mul_ne h
    rw [hrest _ h00 h01, hrest _ h10 h11]
    exact hinv i h
  · exact ⟨h0, h1⟩

/-- One step of the first loop of `as_radix_16`: byte `s` is split into entries `2 s`, `2 s + 1`. -/
private theorem as_radix_16_loop0_body_spec (self : Scalar) (iter : core.ops.range.Range Usize)
    (out : Array I8 64#usize) (hlt : iter.start.val < 32) (hend : iter.end = 32#usize) :
    as_radix_16_loop0.body self iter out ⦃ r => ∃ iter1 out2, r = .cont (iter1, out2) ∧
      iter1.start.val = iter.start.val + 1 ∧ iter1.end = iter.end ∧
      out2[2 * iter.start.val]!.val = ((self.bytes[iter.start.val]!.val % 16 : ℕ) : ℤ) ∧
      out2[2 * iter.start.val + 1]!.val = ((self.bytes[iter.start.val]!.val / 16 : ℕ) : ℤ) ∧
      ∀ j, j ≠ 2 * iter.start.val → j ≠ 2 * iter.start.val + 1 → out2[j]! = out[j]! ⦄ := by
  unfold as_radix_16_loop0.body
  step with core.iter.range.IteratorRange.next_Usize_some_spec
    as ⟨o, iter1, ho, hstart1, hend1⟩
  subst ho
  step as ⟨x, hx⟩
  step as ⟨lo, hlo⟩
  step as ⟨k2, hk2⟩
  step with UScalar.hcast_inBounds_spec as ⟨lo8, hlo8⟩
  step with Array.update_getElem!_spec as ⟨out1, hout1, hout1'⟩
  step as ⟨top, htop⟩
  step as ⟨k3, hk3⟩
  step with UScalar.hcast_inBounds_spec as ⟨hi8, hhi8⟩
  step with Array.update_getElem!_spec as ⟨out2, hout2, hout2'⟩
  rw [hk2] at hk3 hout1 hout1'
  rw [hk3] at hout2 hout2'
  refine ⟨iter1, out2, rfl, hstart1, hend1, ?_, ?_, fun j hj0 hj1 => ?_⟩
  · rw [hout2' _ (Nat.succ_ne_self _).symm, hout1, hlo8, hlo, hx]
  · rw [hout2, hhi8, eq_div_sixteen htop, hx]
  · rw [hout2' j hj1, hout1' j hj0]

/-- The first loop of `as_radix_16` splits each byte into its two nibbles. -/
@[local step]
private theorem as_radix_16_loop0_spec (self : Scalar) :
    as_radix_16_loop0 { start := 0#usize, «end» := 32#usize } self (Array.repeat 64#usize 0#i8)
    ⦃ (r : Array I8 64#usize) => ∀ i : ℕ, i < 32 →
      r[2 * i]!.val = ((self.bytes[i]!.val % 16 : ℕ) : ℤ) ∧
      r[2 * i + 1]!.val = ((self.bytes[i]!.val / 16 : ℕ) : ℤ) ⦄ := by
  unfold as_radix_16_loop0
  apply loop.spec_decr_nat (measure := fun (iter, _) => 32 - iter.start.val)
    (inv := fun (iter, out) => iter.end = 32#usize ∧ iter.start.val ≤ 32 ∧
      Loop0Inv self out iter.start.val)
  · rintro ⟨iter, out⟩ ⟨hend, hstart, hdone⟩
    by_cases hlt : iter.start.val < 32
    · apply spec_mono (as_radix_16_loop0_body_spec self iter out hlt hend)
      rintro r ⟨iter1, out2, rfl, hstart1, hend1, h0, h1, hrest⟩
      refine ⟨⟨hend1.trans hend, hstart1 ▸ hlt, hstart1 ▸ loop0_inv_succ hdone h0 h1 hrest⟩, ?_⟩
      dsimp only
      rw [hstart1]
      exact Nat.sub_lt_sub_left hlt (Nat.lt_succ_self _)
    · have hs : iter.start.val = 32 := Nat.le_antisymm hstart (Nat.le_of_not_lt hlt)
      unfold as_radix_16_loop0.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, iter1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      rw [hs] at hdone
      exact hdone
  · exact ⟨rfl, by decide, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

/-- The carry of one recentring step. -/
private theorem carry_arith {d d8 c : ℤ} (hd : 0 ≤ d ∧ d ≤ 16) (hd8 : d8 = d + 8)
    (hc : c = d8 / 2 ^ 4) : (c = 0 ∨ c = 1) ∧ -8 ≤ d - 16 * c ∧ d - 16 * c < 8 := by
  subst hd8 hc
  omega

/-- A digit `0 … 15`, possibly increased by a carry. -/
private theorem digit_succ_bound {x y : ℤ} (h : x = y ∨ x = y + 1) (hy : 0 ≤ y ∧ y ≤ 15) :
    0 ≤ x ∧ x ≤ 16 := by
  omega

/-- The last digit, possibly increased by a carry. -/
private theorem last_digit_bound {x y : ℤ} (h : x = y ∨ x = y + 1) (h0 : 0 ≤ y) (h7 : y ≤ 7) :
    -8 ≤ x ∧ x ≤ 8 := by
  omega

/-- One step of the second loop of `as_radix_16`: digit `i` is recentred and its carry added to
digit `i + 1`. -/
private theorem as_radix_16_loop1_body_spec (iter : core.ops.range.Range Usize)
    (cur : Array I8 64#usize) (hlt : iter.start.val < 63) (hend : iter.end = 63#usize)
    (hd : 0 ≤ cur[iter.start.val]!.val ∧ cur[iter.start.val]!.val ≤ 16)
    (hn : 0 ≤ cur[iter.start.val + 1]!.val ∧ cur[iter.start.val + 1]!.val ≤ 15) :
    as_radix_16_loop1.body iter cur ⦃ r => ∃ iter1 cur2, r = .cont (iter1, cur2) ∧
      iter1.start.val = iter.start.val + 1 ∧ iter1.end = iter.end ∧
      cur2.asInt 4 = cur.asInt 4 ∧
      (-8 ≤ cur2[iter.start.val]!.val ∧ cur2[iter.start.val]!.val < 8) ∧
      (cur2[iter.start.val + 1]!.val = cur[iter.start.val + 1]!.val ∨
        cur2[iter.start.val + 1]!.val = cur[iter.start.val + 1]!.val + 1) ∧
      ∀ j, j ≠ iter.start.val → j ≠ iter.start.val + 1 → cur2[j]! = cur[j]! ⦄ := by
  unfold as_radix_16_loop1.body
  have hs : iter.start.val < (64#usize).val := Nat.lt_succ_of_lt hlt
  have hsl : iter.start.val < cur.length := lt_of_lt_of_eq hs (Array.length_eq cur).symm
  have hne : iter.start.val + 1 ≠ iter.start.val := Nat.succ_ne_self _
  step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, iter1, ho, hstart1, hend1⟩
  subst ho
  step with Array.index_usize_getElem!_spec as ⟨d, hdv⟩
  rw [← hdv] at hd
  step as ⟨d8, hd8⟩
  step as ⟨c, hc, hcbv⟩
  rw [Int.shiftRight_eq_div_pow] at hc
  have hcb := carry_arith hd hd8 (by simpa using hc)
  step as ⟨c16, hc16, hc16bv⟩
  have hc16v : c16.val = 16 * c.val := by
    rw [hc16, Int.shiftLeft_eq]
    rcases hcb.1 with h | h <;> rw [h] <;> norm_num [I8.size, I8.numBits, Int.bmod]
  step as ⟨e, he⟩
  step as ⟨cur1, hcur1⟩
  step as ⟨k1, hk1⟩
  have hk1s : k1.val < (64#usize).val := by rw [hk1]; exact Nat.succ_lt_succ hlt
  step with Array.index_usize_getElem!_spec as ⟨n, hnv⟩
  have hn1eq : n = cur[iter.start.val + 1]! := by
    rw [hnv, hcur1, hk1, Array.getElem!_Nat_set_ne _ _ _ _ hne.symm]
  rw [← hn1eq] at hn
  step as ⟨n1, hn1⟩
  step as ⟨cur2, hcur2⟩
  have hcur2s : cur2[iter.start.val]! = e := by
    rw [hcur2, Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hk1]; exact hne), hcur1,
      Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, hsl⟩]
  have hb : -8 ≤ cur2[iter.start.val]!.val ∧ cur2[iter.start.val]!.val < 8 := by
    rw [hcur2s, he, hc16v]
    exact hcb.2
  refine ⟨iter1, cur2, rfl, hstart1, hend1, ?_, hb.1, hb.2, ?_, fun j hj hj1 => ?_⟩
  · have h1 := Array.asInt_set 4 cur iter.start e hs
    have h2 := Array.asInt_set 4 cur1 k1 n1 hk1s
    rw [← hcur1] at h1
    rw [← hcur2, ← hnv, h1, hn1, he, hc16v, ← hdv, hk1, Nat.mul_succ, pow_add] at h2
    rw [h2]
    ring
  · have hk1l : iter.start.val + 1 < cur1.length :=
      hk1 ▸ lt_of_lt_of_eq hk1s (Array.length_eq cur1).symm
    rw [hcur2, Array.getElem!_Nat_set_eq _ _ _ _ ⟨hk1, hk1l⟩, hn1, ← hn1eq]
    rcases hcb.1 with h | h <;> rw [h] <;> simp
  · rw [hcur2, Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hk1]; exact Ne.symm hj1), hcur1,
      Array.getElem!_Nat_set_ne _ _ _ _ (Ne.symm hj)]

/-- The second loop of `as_radix_16` recentres the digits `0 … 15` into `-8 … 7`, carrying into
the next digit. -/
@[local step]
private theorem as_radix_16_loop1_spec (out : Array I8 64#usize)
    (hout : ∀ j : ℕ, j < 64 → 0 ≤ out[j]!.val ∧ out[j]!.val ≤ 15) (h63 : out[63]!.val ≤ 7) :
    as_radix_16_loop1 { start := 0#usize, «end» := 63#usize } out ⦃ (r : Array I8 64#usize) =>
      r.asInt 4 = out.asInt 4 ∧ (∀ i : ℕ, i < 63 → -8 ≤ r[i]!.val ∧ r[i]!.val < 8) ∧
      -8 ≤ r[63]!.val ∧ r[63]!.val ≤ 8 ⦄ := by
  unfold as_radix_16_loop1
  apply loop.spec_decr_nat (measure := fun (iter, _) => 63 - iter.start.val)
    (inv := fun (iter, cur) => iter.end = 63#usize ∧ iter.start.val ≤ 63 ∧
      cur.asInt 4 = out.asInt 4 ∧
      (∀ j < iter.start.val, -8 ≤ cur[j]!.val ∧ cur[j]!.val < 8) ∧
      (cur[iter.start.val]!.val = out[iter.start.val]!.val ∨
        cur[iter.start.val]!.val = out[iter.start.val]!.val + 1) ∧
      ∀ j, iter.start.val < j → j < 64 → cur[j]! = out[j]!)
  · rintro ⟨iter, cur⟩ ⟨hend, hstart, hval, hlow, hcur, hhigh⟩
    by_cases hlt : iter.start.val < 63
    · have hs1 : iter.start.val + 1 < 64 := Nat.succ_lt_succ hlt
      have hos := hout iter.start.val (Nat.lt_of_succ_lt hs1)
      have hcur1 := hhigh (iter.start.val + 1) (Nat.lt_succ_self _) hs1
      have hos1 := hout (iter.start.val + 1) hs1
      rw [← hcur1] at hos1
      apply spec_mono (as_radix_16_loop1_body_spec iter cur hlt hend (digit_succ_bound hcur hos)
        hos1)
      rintro r ⟨iter1, cur2, rfl, hstart1, hend1, hval2, hb, hnext, hrest⟩
      refine ⟨⟨hend1.trans hend, hstart1 ▸ hlt, hval2.trans hval, fun j hj => ?_, ?_,
        fun j hj hj64 => ?_⟩, ?_⟩
      · rw [hstart1] at hj
        by_cases hjs : j = iter.start.val
        · rw [hjs]
          exact hb
        · rw [hrest j hjs (Nat.ne_of_lt hj)]
          exact hlow j (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hjs)
      · rw [hstart1, ← hcur1]
        exact hnext
      · rw [hstart1] at hj
        rw [hrest j (Nat.ne_of_gt (Nat.lt_of_succ_lt hj)) (Nat.ne_of_gt hj)]
        exact hhigh j (Nat.lt_of_succ_lt hj) hj64
      · dsimp only
        rw [hstart1]
        exact Nat.sub_lt_sub_left hlt (Nat.lt_succ_self _)
    · have hs : iter.start.val = 63 := Nat.le_antisymm hstart (Nat.le_of_not_lt hlt)
      unfold as_radix_16_loop1.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, iter1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      rw [hs] at hcur hlow
      exact ⟨hval, hlow, last_digit_bound hcur (hout 63 (by norm_num)).1 h63⟩
  · exact ⟨rfl, by decide, rfl, fun j hj => absurd hj (Nat.not_lt_zero j), Or.inl rfl,
      fun _ _ _ => rfl⟩

/-- The two nibbles of a byte are digits `0 … 15`. -/
private theorem nibble_bounds {b : ℕ} (hb : b < 256) :
    (0 ≤ ((b % 16 : ℕ) : ℤ) ∧ ((b % 16 : ℕ) : ℤ) ≤ 15) ∧
    0 ≤ ((b / 16 : ℕ) : ℤ) ∧ ((b / 16 : ℕ) : ℤ) ≤ 15 := by
  omega

/-- The top nibble of a byte `≤ 127` is at most `7`. -/
private theorem top_nibble_le {b : ℕ} (hb : b ≤ 127) : ((b / 16 : ℕ) : ℤ) ≤ 7 := by
  omega

/-- A byte is the sum of its nibbles, in radix `2 ^ 4`. -/
private theorem nibbles_val (b : ℕ) :
    ((b % 16 : ℕ) : ℤ) + 2 ^ 4 * ((b / 16 : ℕ) : ℤ) = (b : ℤ) := by
  omega

@[step]
theorem as_radix_16_spec (self : Scalar) (hself : self.asNat < 2 ^ 255) :
    as_radix_16 self ⦃ (r : Array I8 64#usize) =>
      r.asInt 4 = self.asNat ∧
      (∀ i : ℕ, i < 63 → -8 ≤ r[i]!.val ∧ r[i]!.val < 8) ∧ -8 ≤ r[63]!.val ∧ r[63]!.val ≤ 8 ⦄ := by
  have h31 : self.bytes[31]!.val ≤ 127 := Nat.lt_succ_iff.mp (Scalar.bytes_31_lt (k := 7) hself)
  clear hself
  unfold as_radix_16
  step as ⟨b31, hb31⟩
  step
  step as ⟨out, hout⟩
  have hbounds : ∀ j : ℕ, j < 64 → 0 ≤ out[j]!.val ∧ out[j]!.val ≤ 15 := by
    intro j hj
    rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
    · rw [(hout i (Nat.lt_of_mul_lt_mul_left (a := 2) hj)).1]
      exact nibble_bounds (self.bytes[i]!).hBounds |>.1
    · rw [(hout i (Nat.lt_of_mul_lt_mul_left (a := 2) (Nat.lt_of_succ_lt hj))).2]
      exact nibble_bounds (self.bytes[i]!).hBounds |>.2
  have h63 : out[63]!.val ≤ 7 := by
    rw [(hout 31 (by norm_num)).2]
    exact top_nibble_le h31
  step as ⟨r, hval, hlow, h63l, h63u⟩
  refine ⟨?_, hlow, h63l, h63u⟩
  rw [hval, Scalar.asNat_def]
  exact Array.asInt_eq_asNat_of_pairs 4 out self.bytes (by simp) fun i hi => by
    rw [(hout i (by simpa using hi)).1, (hout i (by simpa using hi)).2]
    exact nibbles_val _

end Curve25519Dalek.scalar.Scalar
