/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar
import Mathlib.Tactic.ReduceModChar
import Proofs.Helpers.Array
import Proofs.Helpers.AsInt
import Proofs.Helpers.AsNat
import Proofs.Helpers.Bitwise
import Proofs.Scalar.ReadLeU64Into
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar

/-- An even window: the remaining value halves. -/
private theorem naf_even_val {Y c w : ℕ} (hw : 1 ≤ w) (hc : c ≤ 1)
    (hev : (c + Y % 2 ^ w) % 2 = 0) :
    c + Y = 2 * (c + Y / 2) := by
  have h : Y % 2 ^ w % 2 = Y % 2 := Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))
  omega

/-- The top bit: a carry into bit `255` gives an odd window. -/
private theorem naf_even_carry {X pos c w : ℕ} (hX : X < 2 ^ 255) (hpos : 255 ≤ pos)
    (hc : c ≤ 1)
    (hev : (c + X / 2 ^ pos % 2 ^ w) % 2 = 0) : c = 0 := by
  have hY : X / 2 ^ pos = 0 :=
    Nat.div_eq_of_lt (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) hpos))
  rw [hY, Nat.zero_mod] at hev
  omega

/-- Near the top, an odd window is below `2 ^ (w - 1)`: no carry out of bit `255`. -/
private theorem naf_odd_carry {X pos c w : ℕ} (hX : X < 2 ^ 255) (hpw : 256 ≤ pos + w)
    (hw : 2 ≤ w) (hc : c ≤ 1) (hodd : (c + X / 2 ^ pos % 2 ^ w) % 2 = 1) :
    c + X / 2 ^ pos % 2 ^ w < 2 ^ (w - 1) := by
  have hP : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hPe : 2 ^ (w - 1) = 2 * 2 ^ (w - 2) := by
    rw [← pow_succ']; congr 1; omega
  have hYlt : X / 2 ^ pos < 2 ^ (w - 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hmod : X / 2 ^ pos % 2 ^ w = X / 2 ^ pos := Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hodd ⊢
  omega

/-- The digit of an odd window `v = c + (window bits)`, with `2 ^ w = 2 P`: odd and of absolute
value below `P`. -/
private theorem naf_digit {v P : ℕ} (hPe : P % 2 = 0) (hv : v ≤ 2 * P) (hodd : v % 2 = 1) :
    (v < P → (v : ℤ) % 2 = 1 ∧ 2 * |(v : ℤ)| < 2 * P) ∧
    (P ≤ v → ((v : ℤ) - 2 * P) % 2 = 1 ∧ 2 * |(v : ℤ) - 2 * P| < 2 * P) := by
  constructor
  · intro h
    rw [abs_of_nonneg (by positivity)]
    omega
  · intro h
    rw [abs_of_nonpos (by omega)]
    omega

/-- The `i8` value of the negative digit `v - q`, computed with wrap-around. -/
private theorem bmod_sub_bmod {v q : ℤ} (h : -128 ≤ v - q ∧ v - q < 128) :
    Int.bmod (Int.bmod v 256 - Int.bmod q 256) 256 = v - q := by
  simp only [Int.bmod]
  split_ifs <;> omega

/-- The invariant of the loop of `non_adjacent_form` at bit `pos` with carry `carry`: the digits
written so far and the remaining value `carry + X / 2 ^ pos` make up `X`; the digits from `pos` on
are zero; each nonzero digit is odd, below `2 ^ (w - 1)` in absolute value, and followed by `w - 1`
zeros. -/
private def NafInv (X w : ℕ) (naf : Array I8 256#usize) (pos carry : ℕ) : Prop :=
  carry ≤ 1 ∧ (256 ≤ pos → carry = 0) ∧
  naf.asInt 1 + 2 ^ pos * ((carry + X / 2 ^ pos : ℕ) : ℤ) = X ∧
  (∀ j, pos ≤ j → j < 256 → naf[j]!.val = 0) ∧
  ∀ i : ℕ, i < 256 → naf[i]!.val ≠ 0 → (naf[i]!.val % 2 = 1 ∧ 2 * |naf[i]!.val| < 2 ^ w) ∧
    i + w ≤ pos ∧ ∀ j, i < j → j < i + w → j < 256 → naf[j]!.val = 0

/-- An even window: no digit, move to the next bit. -/
private theorem naf_inv_even {X w : ℕ} {naf : Array I8 256#usize} {pos c : ℕ} (hX : X < 2 ^ 255)
    (hw : 2 ≤ w) (hinv : NafInv X w naf pos c)
    (hev : (c + X / 2 ^ pos % 2 ^ w) % 2 = 0) :
    NafInv X w naf (pos + 1) c := by
  obtain ⟨hc, -, hval, hzero, hnz⟩ := hinv
  refine ⟨hc, fun h => naf_even_carry hX (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le
    (by norm_num) h)) hc hev, ?_, fun j hj hj256 => hzero j (Nat.le_of_succ_le hj) hj256,
    fun i hi hne => ?_⟩
  · have hhalf := naf_even_val (by omega) hc hev
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← hval, hhalf]
    push_cast
    ring
  · obtain ⟨hd, hiw, hz⟩ := hnz i hi hne
    exact ⟨hd, Nat.le_succ_of_le hiw, hz⟩

/-- An odd window: digit `d` at `pos`, carry `c'`, move `w` bits on. -/
private theorem naf_inv_odd {X w : ℕ} {naf : Array I8 256#usize} {pos c c' : ℕ} {d : I8}
    (hw : 1 ≤ w) (hpos : pos < 256) (hinv : NafInv X w naf pos c) (hc' : c' ≤ 1)
    (hc'0 : 256 ≤ pos + w → c' = 0)
    (hd : d.val + 2 ^ w * (c' : ℤ) = ((c + X / 2 ^ pos % 2 ^ w : ℕ) : ℤ))
    (hdd : d.val % 2 = 1 ∧ 2 * |d.val| < 2 ^ w) (p : Usize) (hp : p.val = pos) :
    NafInv X w (naf.set p d) (pos + w) c' := by
  obtain ⟨-, -, hval, hzero, hnz⟩ := hinv
  refine ⟨hc', hc'0, ?_, fun j hj hj256 => ?_, fun i hi hne => ?_⟩
  · have hv := Nat.two_pow_mul_window_eq (pos := pos) hd
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add] at hv
    rw [Array.asInt_set 1 naf p d (by simp [hp, hpos]), hp, hzero pos le_rfl hpos, sub_zero,
      ← hval, hv, one_mul, add_assoc]
  · rw [Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hp]; exact Nat.ne_of_lt (by omega))]
    exact hzero j (by omega) hj256
  · by_cases hip : i = pos
    · subst hip
      rw [Array.getElem!_Nat_set_eq _ _ _ _ ⟨hp, by simp [hi]⟩]
      refine ⟨hdd, le_rfl, fun j hj hjw hj256 => ?_⟩
      rw [Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hp]; exact Nat.ne_of_lt hj)]
      exact hzero j (Nat.le_of_lt hj) hj256
    · rw [Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hp]; exact Ne.symm hip)] at hne ⊢
      have hilt : i < pos := by
        by_contra hge
        exact hne (hzero i (Nat.le_of_not_lt hge) hi)
      obtain ⟨hd', hiw, hz⟩ := hnz i hi hne
      refine ⟨hd', le_trans hiw (Nat.le_add_right _ _), fun j hj hjw hj256 => ?_⟩
      rw [Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hp]; exact Nat.ne_of_gt (by omega))]
      exact hz j hj hjw hj256

/-- The bit buffer of `non_adjacent_form`: its low `w` bits are the bits `64 u + b …` of `X`. -/
private theorem naf_bit_buf_spec (x : Array U64 5#usize) (X : ℕ) (hX : x.asNat 64 = X)
    (w u b t : Usize) (hw : w.val ≤ 8) (hu : u.val ≤ 3) (hb : b.val < 64)
    (ht : t.val = 64 - w.val) :
    (if b < t
      then do
           let i1 ← Array.index_usize x u
           i1 >>> b
      else
        do
        let i1 ← Array.index_usize x u
        let i2 ← i1 >>> b
        let i3 ← 1#usize + u
        let i4 ← Array.index_usize x i3
        let i5 ← 64#usize - b
        let i6 ← i4 <<< i5
        ok (i2 ||| i6)) ⦃ (bb : U64) =>
      bb.val % 2 ^ w.val = X / 2 ^ (64 * u.val + b.val) % 2 ^ w.val ⦄ := by
  have hlimb (j : ℕ) : X / 2 ^ (64 * j) % 2 ^ 64 = x[j]!.val := by
    rw [← hX]
    exact Array.asNat_div_pow_mod 64 x (fun i _ => by simpa using (x[i]!).hBounds) j
  split_ifs with hbt
  · step with Array.index_usize_getElem!_spec as ⟨l, hl⟩
    step as ⟨r, hr, hrbv⟩
    rw [hr, Nat.shiftRight_eq_div_pow, hl, ← hlimb]
    exact Nat.window_in_limb X u.val b.val w.val (by scalar_tac)
  · step with Array.index_usize_getElem!_spec as ⟨l, hl⟩
    step as ⟨r, hr, hrbv⟩
    step as ⟨u1, hu1⟩
    step with Array.index_usize_getElem!_spec as ⟨l1, hl1⟩
    step as ⟨k, hk⟩
    step as ⟨r1, hr1, hr1bv⟩
    rw [UScalar.val_or, hr, hr1, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, hl, hl1, hu1, hk,
      ← hlimb, ← hlimb]
    have := Nat.window_across X u.val b.val w.val hb (hw.trans (by norm_num))
    rw [Nat.add_comm 1 u.val]
    simpa [U64.size, U64.numBits] using this

/-- The half width `P = 2 ^ (w - 1)` of a window of `2 ≤ w ≤ 8` bits. -/
private theorem naf_half {w : ℕ} (hw : 2 ≤ w ∧ w ≤ 8) :
    2 ^ w = 2 * 2 ^ (w - 1) ∧ 2 ^ (w - 1) % 2 = 0 ∧ 2 ^ (w - 1) ≤ 128 := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 2 := ⟨w - 2, by omega⟩
  refine ⟨by rw [show k + 2 - 1 = k + 1 by omega, pow_succ, mul_comm], ?_, ?_⟩
  · rw [show k + 2 - 1 = k + 1 by omega, pow_succ, Nat.mul_mod_left]
  · rw [show k + 2 - 1 = k + 1 by omega]
    exact (Nat.pow_le_pow_right (by norm_num) (by omega : k + 1 ≤ 7)).trans (by norm_num)

/-- A window plus a carry is at most `2 ^ w`. -/
private theorem naf_win_le {c Y W : ℕ} (hc : c ≤ 1) (hW : 0 < W) : c + Y % W ≤ W := by
  have := Nat.mod_lt Y hW
  omega

/-- The negative digit `v - 2 P` of a window `P ≤ v ≤ 2 P` fits in an `i8`. -/
private theorem naf_neg_digit_bound {v P : ℕ} (h1 : P ≤ v) (h2 : v ≤ 2 * P) (h3 : P ≤ 128) :
    -128 ≤ (v : ℤ) - 2 * P ∧ (v : ℤ) - 2 * P < 128 := by
  omega

/-- One step of the loop of `non_adjacent_form` keeps the invariant and advances `pos`. -/
private theorem naf_body_spec (w : Usize) (x : Array U64 5#usize) (width mask : U64) (X : ℕ)
    (hX : x.asNat 64 = X) (hX255 : X < 2 ^ 255) (hw : 2 ≤ w.val ∧ w.val ≤ 8)
    (hwidth : width.val = 2 ^ w.val) (hmask : mask.val = 2 ^ w.val - 1)
    (naf : Array I8 256#usize) (pos : Usize) (carry : U64) (hpos : pos.val < 256)
    (hinv : NafInv X w.val naf pos.val carry.val) :
    non_adjacent_form_loop.body w x width mask naf pos carry ⦃ r =>
      ∃ naf' pos' carry', r = .cont (naf', pos', carry') ∧ pos.val < pos'.val ∧
        NafInv X w.val naf' pos'.val carry'.val ⦄ := by
  have hc := hinv.1
  have hw1 : 1 ≤ w.val := Nat.le_of_succ_le hw.1
  have hposw : pos.val < pos.val + w.val := Nat.lt_add_of_pos_right hw1
  unfold non_adjacent_form_loop.body
  simp only [show pos < 256#usize by scalar_tac, ite_true]
  step as ⟨u, hu⟩
  step as ⟨b, hb⟩
  step as ⟨t, ht⟩
  have hub' : pos.val / 64 ≤ 3 ∧ pos.val % 64 < 64 :=
    ⟨Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul hpos), Nat.mod_lt _ (by norm_num)⟩
  rw [← hu, ← hb] at hub'
  step with naf_bit_buf_spec x X hX w u b t hw.2 hub'.1 hub'.2 ht as ⟨bb, hbb⟩
  have hub : 64 * u.val + b.val = pos.val := by
    rw [hu, hb]
    exact Nat.div_add_mod _ _
  rw [hub] at hbb
  step with UScalar.and_two_pow_sub_one_spec bb mask w.val hmask as ⟨m, hm⟩
  rw [hbb] at hm
  have hmlt : m.val < 2 ^ w.val := by
    rw [hm]
    exact Nat.mod_lt _ (by positivity)
  step as ⟨win, hwin⟩
  step with UScalar.and_two_pow_sub_one_spec win 1#u64 1 rfl as ⟨par, hpar⟩
  have hwinv : win.val = carry.val + X / 2 ^ pos.val % 2 ^ w.val := by rw [hwin, hm]
  by_cases hev : win.val % 2 = 0
  · have hp0 : par = 0#u64 := UScalar.eq_of_val_eq (by rw [hpar]; simpa using hev)
    simp only [hp0, ite_true]
    step as ⟨pos1, hpos1⟩
    refine ⟨naf, pos1, carry, rfl, by rw [hpos1]; exact Nat.lt_succ_self _, ?_⟩
    rw [hpos1]
    exact naf_inv_even hX255 hw.1 hinv (by rw [← hwinv]; exact hev)
  · have hodd : win.val % 2 = 1 := Nat.mod_two_ne_zero.mp hev
    have hp0 : par ≠ 0#u64 := fun h => hev (by
      have := congrArg UScalar.val h
      rw [hpar] at this
      simpa using this)
    simp only [hp0, ite_false]
    step as ⟨h2, hh2⟩
    obtain ⟨P, hPdef⟩ : ∃ P, 2 ^ (w.val - 1) = P := ⟨_, rfl⟩
    obtain ⟨hP, hPe, hP128⟩ := naf_half hw
    rw [hPdef] at hP hPe hP128
    have hh2v : h2.val = P := by
      rw [hh2, hwidth, hP]
      exact Nat.mul_div_cancel_left P (by norm_num)
    clear hh2
    have hwin2 : win.val ≤ 2 * P := by
      rw [← hP, hwinv]
      exact naf_win_le hc (by positivity)
    have hdig := naf_digit hPe hwin2 hodd
    have hPz : (2 : ℤ) ^ w.val = 2 * (P : ℤ) := by exact_mod_cast hP
    by_cases hlt : win.val < P
    · simp only [show win < h2 by rw [UScalar.lt_equiv, hh2v]; exact hlt, ite_true]
      have hwin127 : (win.val : ℤ) ≤ IScalar.max .I8 := by
        rw [IScalar.max_IScalarTy_I8_eq, I8.max_eq]
        exact_mod_cast Nat.le_of_lt_succ (lt_of_lt_of_le hlt hP128)
      step with UScalar.hcast_inBounds_spec .I8 win hwin127 as ⟨d, hd⟩
      step as ⟨naf1, hnaf1⟩
      step as ⟨pos1, hpos1⟩
      refine ⟨naf1, pos1, 0#u64, rfl, by rw [hpos1]; exact hposw, ?_⟩
      rw [hpos1, hnaf1]
      refine naf_inv_odd hw1 hpos hinv (by simp) (fun _ => rfl) ?_ ?_ pos rfl
      · rw [hd, ← hwinv]
        simp
      · rw [hd, hPz]
        exact hdig.1 hlt
    · simp only [show ¬ win < h2 by rw [UScalar.lt_equiv, hh2v]; exact hlt, ite_false]
      step as ⟨d0, hd0⟩
      step as ⟨q0, hq0⟩
      step as ⟨d, hd⟩
      step as ⟨naf1, hnaf1⟩
      step as ⟨pos1, hpos1⟩
      refine ⟨naf1, pos1, 1#u64, rfl, by rw [hpos1]; exact hposw, ?_⟩
      rw [hpos1, hnaf1]
      have hge : P ≤ win.val := Nat.le_of_not_lt hlt
      have hdv : d.val = (win.val : ℤ) - 2 * P := by
        rw [hd, core.num.I8.wrapping_sub_val_eq, hd0, hq0, UScalar.hcast_val_eq,
          UScalar.hcast_val_eq, hwidth]
        have h2w : ((2 ^ w.val : ℕ) : ℤ) = 2 * P := by exact_mod_cast hP
        rw [h2w]
        exact bmod_sub_bmod (naf_neg_digit_bound hge hwin2 hP128)
      refine naf_inv_odd hw1 hpos hinv (by simp) (fun h => ?_) ?_ ?_ pos rfl
      · have := naf_odd_carry hX255 h hw.1 hc (by rw [← hwinv]; exact hodd)
        rw [← hwinv, hPdef] at this
        exact absurd hge (Nat.not_le.mpr this)
      · rw [hdv, hPz, ← hwinv]
        simp
      · rw [hdv, hPz]
        exact hdig.2 hge

/-- The invariant holds initially. -/
private theorem naf_inv_init (X w : ℕ) : NafInv X w (Array.repeat 256#usize 0#i8) 0 0 := by
  unfold NafInv
  refine ⟨Nat.zero_le _, fun h => absurd h (by norm_num), ?_, fun j _ hj => ?_,
    fun i hi hne => ?_⟩
  · rw [Array.asInt_repeat_zero 1 _ (by simp)]
    simp
  · rw [Array.getElem!_repeat _ (by simpa using hj)]
    rfl
  · refine (hne ?_).elim
    rw [Array.getElem!_repeat _ (by simpa using hi)]
    rfl

/-- The loop of `non_adjacent_form` computes the width-`w` NAF of `x` (below `2 ^ 255`). -/
private theorem naf_loop_spec (w : Usize) (x : Array U64 5#usize) (width mask : U64) (X : ℕ)
    (hX : x.asNat 64 = X) (hX255 : X < 2 ^ 255) (hw : 2 ≤ w.val ∧ w.val ≤ 8)
    (hwidth : width.val = 2 ^ w.val) (hmask : mask.val = 2 ^ w.val - 1) :
    non_adjacent_form_loop w (Array.repeat 256#usize 0#i8) x width mask 0#usize 0#u64
    ⦃ (r : Array I8 256#usize) =>
      r.asInt 1 = X ∧
      (∀ i : ℕ, i < 256 → r[i]!.val ≠ 0 → r[i]!.val % 2 = 1 ∧ 2 * |r[i]!.val| < 2 ^ w.val) ∧
      ∀ i : ℕ, i < 256 → ∀ j : ℕ, j < 256 → i < j → j < i + w.val → r[i]!.val ≠ 0 →
        r[j]!.val = 0 ⦄ := by
  unfold non_adjacent_form_loop
  apply loop.spec_decr_nat (measure := fun (_, pos, _) => 256 - pos.val)
    (inv := fun (naf, pos, carry) => NafInv X w.val naf pos.val carry.val)
  · rintro ⟨naf, pos, carry⟩ hinv
    by_cases hpos : pos.val < 256
    · apply spec_mono (naf_body_spec w x width mask X hX hX255 hw hwidth hmask naf pos carry hpos
        hinv)
      rintro r ⟨naf', pos', carry', rfl, hlt, hinv'⟩
      exact ⟨hinv', Nat.sub_lt_sub_left hpos hlt⟩
    · unfold non_adjacent_form_loop.body
      simp only [show ¬ pos < 256#usize from fun h => hpos h, ite_false, WP.spec_ok]
      obtain ⟨-, hc0, hval, -, hnz⟩ := hinv
      have hge : 256 ≤ pos.val := Nat.le_of_not_lt hpos
      have hq : X / 2 ^ pos.val = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hX255
        (Nat.pow_le_pow_right (by norm_num) (le_trans (by norm_num) hge)))
      rw [hc0 hge, hq] at hval
      refine ⟨by simpa using hval, fun i hi hne => (hnz i hi hne).1, fun i hi j hj hij hjw hne =>
        (hnz i hi hne).2.2 j hij hjw hj⟩
  · exact naf_inv_init X w.val

@[step]
theorem non_adjacent_form_spec (self : Scalar) (w : Usize) (hw : 2 ≤ w.val ∧ w.val ≤ 8)
    (hself : self.asNat < 2 ^ 255) :
    non_adjacent_form self w ⦃ (r : Array I8 256#usize) =>
      r.asInt 1 = self.asNat ∧
      (∀ i : ℕ, i < 256 → r[i]!.val ≠ 0 → r[i]!.val % 2 = 1 ∧ 2 * |r[i]!.val| < 2 ^ w.val) ∧
      ∀ i : ℕ, i < 256 → ∀ j : ℕ, j < 256 → i < j → j < i + w.val → r[i]!.val ≠ 0 →
        r[j]!.val = 0 ⦄ := by
  unfold non_adjacent_form
  step
  step
  step as ⟨s, hs⟩
  step as ⟨s1, back, hs1, hs1len, hback⟩
  step as ⟨s2, hs2len, hs2⟩
  step as ⟨width, hwv, hwbv⟩
  have hwidth : width.val = 2 ^ w.val := by
    rw [hwv, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hw.2)
      (by simp [U64.size, U64.numBits]))
  have h1w : (1#u64).val ≤ width.val := by
    rw [hwidth]
    exact Nat.one_le_two_pow
  step as ⟨mask, hmask⟩
  have hs1l : s1.length = 4 := by simpa using hs1len
  have hlimb (i : ℕ) (hi : i < 4) : (back s2)[i]! = s2[i]! := by
    have hlen : i < (Array.repeat 5#usize 0#u64).val.length := by
      simp only [Array.repeat_val, List.length_replicate]
      scalar_tac
    rw [Array.getElem!_Nat_eq, hback, List.getElem!_setSlice!_middle _ _ _ _
      ⟨Nat.zero_le _, by simp [hs2len, hs1l, hi], hlen⟩, Nat.sub_zero, Slice.getElem!_Nat_eq]
  have hXeq : (back s2).asNat 64 = self.asNat :=
    self.asNat_def ▸ Array.asNat_limbs_eq 8 4 (back s2) self.bytes (by simp) (by simp)
      (fun i _ => by simpa using ((back s2)[i]!).hBounds)
      (fun i hi j hj => by
        rw [hlimb i hi, hs2 i (by rw [hs1l]; exact hi) j hj, hs, Slice.getElem!_Nat_eq,
          Array.getElem!_Nat_eq, Array.val_to_slice])
      (fun i hi hi5 => by
        rw [Array.getElem!_Nat_eq, hback, List.getElem!_setSlice!_suffix _ _ _ _
          (by simp only [hs2len, Slice.length, hs1l, zero_add]; scalar_tac), Array.repeat_val,
          List.getElem!_replicate _ (by scalar_tac)]
        rfl)
  exact naf_loop_spec w (back s2) width mask self.asNat hXeq hself hw hwidth
    (by rw [hmask, hwidth])

end Curve25519Dalek.scalar.Scalar
