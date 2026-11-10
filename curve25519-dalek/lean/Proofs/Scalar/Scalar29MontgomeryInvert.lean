/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar29
import Curve25519.Prime
import Mathlib.FieldTheory.Finite.Basic
import Proofs.Backend.Serial.U32.Scalar.MontgomeryMul
import Proofs.Backend.Serial.U32.Scalar.MontgomerySquare
import Proofs.Helpers.Scalar29
import Proofs.Helpers.ZMod
import Proofs.Helpers.Radix
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u32.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar29.montgomery_invert

/-! ## `square_multiply`, in `ZMod L` -/

/-- One Montgomery squaring: `y' * R ^ 2 ^ k = y ^ 2 ^ k * R` is kept for `k + 1`. -/
private theorem sq_step {R y y' r : ZMod L} (k : ℕ) (hR : R ≠ 0)
    (h : y' * R ^ 2 ^ k = y ^ 2 ^ k * R) (hr : r * R = y' ^ 2) :
    r * R ^ 2 ^ (k + 1) = y ^ 2 ^ (k + 1) * R := by
  apply mul_right_cancel₀ hR
  rw [pow_succ, pow_mul, pow_mul]
  linear_combination (R ^ 2 ^ k) ^ 2 * hr + (y' * R ^ 2 ^ k + y ^ 2 ^ k * R) * h

/-- The final Montgomery multiplication of `square_multiply`. -/
private theorem mul_step {R y y' x r : ZMod L} (k : ℕ) (hR : R ≠ 0)
    (h : y' * R ^ 2 ^ k = y ^ 2 ^ k * R) (hr : r * R = y' * x) :
    r * R ^ 2 ^ k = y ^ 2 ^ k * x := by
  apply mul_right_cancel₀ hR
  linear_combination R ^ 2 ^ k * hr + x * h

@[local step]
private theorem square_multiply_loop_spec (y : backend.serial.u32.scalar.Scalar29)
    (squarings : Usize) (hy : y.LimbsLt 29) (hy' : y.asNat < L) :
    square_multiply_loop { start := 0#usize, «end» := squarings } y
      ⦃ (r : backend.serial.u32.scalar.Scalar29) =>
      (r.asNat : ZMod L) * montgomeryRadix ^ 2 ^ squarings.val =
        (y.asNat : ZMod L) ^ 2 ^ squarings.val * montgomeryRadix ∧
      r.asNat < L ∧ r.LimbsLt 29 ⦄ := by
  unfold square_multiply_loop
  apply loop.spec_decr_nat (measure := fun (iter, _) => squarings.val - iter.start.val)
    (inv := fun (iter, y1) => iter.end = squarings ∧ iter.start.val ≤ squarings.val ∧
      (y1.asNat : ZMod L) * montgomeryRadix ^ 2 ^ iter.start.val =
        (y.asNat : ZMod L) ^ 2 ^ iter.start.val * montgomeryRadix ∧
      y1.asNat < L ∧ y1.LimbsLt 29)
  · rintro ⟨iter, y1⟩ ⟨hend, hstart, hinv, hy1, hy1b⟩
    unfold square_multiply_loop.body
    by_cases hlt : iter.start.val < squarings.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as
        ⟨o, iter1, ho, hstart1, hend1⟩
      subst ho
      have hsq : y1.asNat ^ 2 < montgomeryRadix * L := by
        rw [Nat.pow_two]
        exact Nat.mul_lt_mul'' (hy1.trans backend.serial.u32.scalar.L_lt_montgomeryRadix) hy1
      step with backend.serial.u32.scalar.Scalar29.montgomery_square_spec y1 hy1b hsq as
        ⟨y2, hy2, hy2L, hy2b⟩
      have hy2' : (y2.asNat : ZMod L) * montgomeryRadix = (y1.asNat : ZMod L) ^ 2 := by
        exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hy2
      refine ⟨by rw [hend1, hend], by scalar_tac, ?_, hy2L, hy2b, by scalar_tac⟩
      rw [hstart1]
      exact sq_step _ backend.serial.u32.scalar.montgomeryRadix_natCast_ne_zero hinv hy2'
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, iter1, ho, hiter1⟩
      subst ho
      have hk : iter.start.val = squarings.val := by scalar_tac
      rw [hk] at hinv
      simp only [WP.spec_ok]
      exact ⟨hinv, hy1, hy1b⟩
  · exact ⟨rfl, by simp, by simp, hy', hy⟩

@[step]
theorem square_multiply_spec (y : backend.serial.u32.scalar.Scalar29)
    (squarings : Usize) (x : backend.serial.u32.scalar.Scalar29) (hy : y.LimbsLt 29)
    (hy' : y.asNat < L) (hx : x.LimbsLt 29) (hx' : x.asNat < L) :
    square_multiply y squarings x ⦃ (r : backend.serial.u32.scalar.Scalar29) =>
      r.asNat * montgomeryRadix ^ 2 ^ squarings.val % L =
        y.asNat ^ 2 ^ squarings.val * x.asNat % L ∧
      r.asNat < L ∧ r.LimbsLt 29 ⦄ := by
  unfold square_multiply
  step as ⟨y1, hy1, hy1L, hy1b⟩
  step with backend.serial.u32.scalar.Scalar29.montgomery_mul_spec y1 x hy1b hx
    (Nat.mul_lt_mul'' (hy1L.trans backend.serial.u32.scalar.L_lt_montgomeryRadix) hx') as
    ⟨r, hr, hrL, hrb⟩
  refine ⟨?_, hrL, hrb⟩
  have hr' : (r.asNat : ZMod L) * montgomeryRadix = y1.asNat * x.asNat := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hr
  rw [← ZMod.natCast_eq_natCast_iff']
  push_cast
  exact mul_step _ backend.serial.u32.scalar.montgomeryRadix_natCast_ne_zero hy1 hr'

end Curve25519Dalek.scalar.Scalar29.montgomery_invert

namespace Curve25519Dalek.scalar.Scalar29

/-! ## The addition chain of `montgomery_invert`, in the Montgomery domain -/

/-- `v` is the Montgomery form `α ^ e * R` of `α ^ e`, reduced and with 52-bit limbs. Kept
irreducible so that the large exponents are never expanded. -/
@[irreducible] private def Mont (α : ZMod L) (e : ℕ) (v : backend.serial.u32.scalar.Scalar29) :
    Prop :=
  (v.asNat : ZMod L) = α ^ e * montgomeryRadix ∧ v.asNat < L ∧ v.LimbsLt 29

private theorem mont_mul_spec {α : ZMod L} {e f : ℕ} {a b : backend.serial.u32.scalar.Scalar29}
    (ha : Mont α e a) (hb : Mont α f b) :
    backend.serial.u32.scalar.Scalar29.montgomery_mul a b
      ⦃ (r : backend.serial.u32.scalar.Scalar29) => Mont α (e + f) r ⦄ := by
  unfold Mont at ha hb ⊢
  obtain ⟨ha, haL, hab⟩ := ha
  obtain ⟨hb, hbL, hbb⟩ := hb
  step with backend.serial.u32.scalar.Scalar29.montgomery_mul_spec a b hab hbb
    (Nat.mul_lt_mul'' (haL.trans backend.serial.u32.scalar.L_lt_montgomeryRadix) hbL) as
    ⟨r, hr, hrL, hrb⟩
  refine ⟨?_, hrL, hrb⟩
  have hr' : (r.asNat : ZMod L) * montgomeryRadix = a.asNat * b.asNat := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hr
  apply mul_right_cancel₀ backend.serial.u32.scalar.montgomeryRadix_natCast_ne_zero
  rw [hr', ha, hb, pow_add]
  ring

private theorem mont_square_spec {α : ZMod L} {e : ℕ} {a : backend.serial.u32.scalar.Scalar29}
    (ha : Mont α e a) :
    backend.serial.u32.scalar.Scalar29.montgomery_square a
      ⦃ (r : backend.serial.u32.scalar.Scalar29) => Mont α (e + e) r ⦄ := by
  have ha' := ha
  unfold Mont at ha' ⊢
  obtain ⟨ha', haL, hab⟩ := ha'
  have hsq : a.asNat ^ 2 < montgomeryRadix * L := by
    rw [Nat.pow_two]
    exact Nat.mul_lt_mul'' (haL.trans backend.serial.u32.scalar.L_lt_montgomeryRadix) haL
  step with backend.serial.u32.scalar.Scalar29.montgomery_square_spec a hab hsq as
    ⟨r, hr, hrL, hrb⟩
  refine ⟨?_, hrL, hrb⟩
  have hr' : (r.asNat : ZMod L) * montgomeryRadix = a.asNat ^ 2 := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hr
  apply mul_right_cancel₀ backend.serial.u32.scalar.montgomeryRadix_natCast_ne_zero
  rw [hr', ha', pow_add]
  ring

private theorem mont_square_multiply_spec {α : ZMod L} {e f : ℕ}
    {y x : backend.serial.u32.scalar.Scalar29} (squarings : Usize)
    (hy : Mont α e y) (hx : Mont α f x) :
    montgomery_invert.square_multiply y squarings x
      ⦃ (r : backend.serial.u32.scalar.Scalar29) => Mont α (e * 2 ^ squarings.val + f) r ⦄ := by
  unfold Mont at hy hx ⊢
  obtain ⟨hy, hyL, hyb⟩ := hy
  obtain ⟨hx, hxL, hxb⟩ := hx
  step with montgomery_invert.square_multiply_spec y squarings x hyb hyL hxb hxL as
    ⟨r, hr, hrL, hrb⟩
  refine ⟨?_, hrL, hrb⟩
  have hr' : (r.asNat : ZMod L) * montgomeryRadix ^ 2 ^ squarings.val =
      (y.asNat : ZMod L) ^ 2 ^ squarings.val * x.asNat := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hr
  apply mul_right_cancel₀
    (pow_ne_zero (2 ^ squarings.val) backend.serial.u32.scalar.montgomeryRadix_natCast_ne_zero)
  rw [hr', hy, hx, pow_add, pow_mul, mul_pow]
  ring

private theorem mont_congr {α : ZMod L} {e e' : ℕ} {v : backend.serial.u32.scalar.Scalar29}
    (h : Mont α e v) (he : e = e') : Mont α e' v :=
  he ▸ h

/-- `self` is the Montgomery form of `self / R`. -/
private theorem mont_self (self : backend.serial.u32.scalar.Scalar29)
    (hself : self.LimbsLt 29) (hself' : self.asNat < L) :
    Mont ((self.asNat : ZMod L) * (montgomeryRadix : ZMod L)⁻¹) 1 self := by
  unfold Mont
  refine ⟨?_, hself', hself⟩
  rw [pow_one, mul_assoc,
    inv_mul_cancel₀ backend.serial.u32.scalar.montgomeryRadix_natCast_ne_zero, mul_one]

/-- The Montgomery form of `(self / R) ^ (L - 2)` is the Montgomery inverse of `self`. -/
private theorem mont_inv (self r : backend.serial.u32.scalar.Scalar29)
    (hr : Mont ((self.asNat : ZMod L) * (montgomeryRadix : ZMod L)⁻¹) (L - 2) r) :
    (self.asNat % L ≠ 0 → r.asNat * self.asNat % L = montgomeryRadix ^ 2 % L) ∧
      (self.asNat % L = 0 → r.asNat = 0) ∧ r.asNat < L ∧ r.LimbsLt 29 := by
  unfold Mont at hr
  obtain ⟨hr, hrL, hrb⟩ := hr
  have hR := backend.serial.u32.scalar.montgomeryRadix_natCast_ne_zero
  have hL2 : 2 < L := (show 2 < 2 ^ 252 by decide).trans two_pow_252_lt_L
  refine ⟨fun h => ?_, fun h => ?_, hrL, hrb⟩
  · have hs : (self.asNat : ZMod L) ≠ 0 := fun h' => h (ZMod.natCast_eq_zero_iff_mod.mp h')
    have hα : (self.asNat : ZMod L) * (montgomeryRadix : ZMod L)⁻¹ ≠ 0 :=
      mul_ne_zero hs (inv_ne_zero hR)
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    have hferm := ZMod.pow_card_sub_one_eq_one hα
    rw [show L - 1 = L - 2 + 1 by omega, pow_succ] at hferm
    calc (r.asNat : ZMod L) * self.asNat
        = ((self.asNat : ZMod L) * (montgomeryRadix : ZMod L)⁻¹) ^ (L - 2) *
            ((self.asNat : ZMod L) * (montgomeryRadix : ZMod L)⁻¹) * montgomeryRadix ^ 2 := by
          rw [hr]
          field_simp
      _ = montgomeryRadix ^ 2 := by rw [hferm, one_mul]
  · have hs : (self.asNat : ZMod L) = 0 := ZMod.natCast_eq_zero_iff_mod.mpr h
    rw [hs, zero_mul, zero_pow (n := L - 2) (by omega), zero_mul] at hr
    have h0 := ZMod.natCast_eq_zero_iff_mod.mp hr
    rwa [Nat.mod_eq_of_lt hrL] at h0

@[step]
theorem montgomery_invert_spec (self : backend.serial.u32.scalar.Scalar29)
    (hself : self.LimbsLt 29) (hself' : self.asNat < L) :
    montgomery_invert self ⦃ (r : backend.serial.u32.scalar.Scalar29) =>
      (self.asNat % L ≠ 0 → r.asNat * self.asNat % L = montgomeryRadix ^ 2 % L) ∧
      (self.asNat % L = 0 → r.asNat = 0) ∧ r.asNat < L ∧ r.LimbsLt 29 ⦄ := by
  unfold montgomery_invert
  have h1 := mont_self self hself hself'
  step with mont_square_spec h1 as ⟨x10, h10⟩
  step with mont_square_spec h10 as ⟨x100, h100⟩
  step with mont_mul_spec h10 h1 as ⟨x11, h11⟩
  step with mont_mul_spec h10 h11 as ⟨x101, h101⟩
  step with mont_mul_spec h10 h101 as ⟨x111, h111⟩
  step with mont_mul_spec h10 h111 as ⟨x1001, h1001⟩
  step with mont_mul_spec h10 h1001 as ⟨x1011, h1011⟩
  step with mont_mul_spec h100 h1011 as ⟨x1111, h1111⟩
  step with mont_mul_spec h1111 h1 as ⟨y, hy⟩
  step as ⟨i, hi⟩
  step with mont_square_multiply_spec i hy h101 as ⟨y1, hy1⟩
  step as ⟨i1, hi1⟩
  step with mont_square_multiply_spec i1 hy1 h11 as ⟨y2, hy2⟩
  step as ⟨i2, hi2⟩
  step with mont_square_multiply_spec i2 hy2 h1111 as ⟨y3, hy3⟩
  step with mont_square_multiply_spec i2 hy3 h1111 as ⟨y4, hy4⟩
  step with mont_square_multiply_spec 4#usize hy4 h1001 as ⟨y5, hy5⟩
  step with mont_square_multiply_spec 2#usize hy5 h11 as ⟨y6, hy6⟩
  step with mont_square_multiply_spec i2 hy6 h1111 as ⟨y7, hy7⟩
  step as ⟨i3, hi3⟩
  step with mont_square_multiply_spec i3 hy7 h101 as ⟨y8, hy8⟩
  step as ⟨i4, hi4⟩
  step with mont_square_multiply_spec i4 hy8 h101 as ⟨y9, hy9⟩
  step with mont_square_multiply_spec 3#usize hy9 h111 as ⟨y10, hy10⟩
  step with mont_square_multiply_spec i2 hy10 h1111 as ⟨y11, hy11⟩
  step as ⟨i5, hi5⟩
  step with mont_square_multiply_spec i5 hy11 h111 as ⟨y12, hy12⟩
  step with mont_square_multiply_spec i1 hy12 h11 as ⟨y13, hy13⟩
  step with mont_square_multiply_spec i2 hy13 h1011 as ⟨y14, hy14⟩
  step as ⟨i6, hi6⟩
  step with mont_square_multiply_spec i6 hy14 h1011 as ⟨y15, hy15⟩
  step as ⟨i7, hi7⟩
  step with mont_square_multiply_spec i7 hy15 h1001 as ⟨y16, hy16⟩
  step with mont_square_multiply_spec i1 hy16 h11 as ⟨y17, hy17⟩
  step as ⟨i8, hi8⟩
  step with mont_square_multiply_spec i8 hy17 h11 as ⟨y18, hy18⟩
  step with mont_square_multiply_spec i8 hy18 h11 as ⟨y19, hy19⟩
  step with mont_square_multiply_spec i2 hy19 h1001 as ⟨y20, hy20⟩
  step with mont_square_multiply_spec i3 hy20 h111 as ⟨y21, hy21⟩
  step with mont_square_multiply_spec i6 hy21 h1111 as ⟨y22, hy22⟩
  step with mont_square_multiply_spec i2 hy22 h1011 as ⟨y23, hy23⟩
  step with mont_square_multiply_spec 3#usize hy23 h101 as ⟨y24, hy24⟩
  step with mont_square_multiply_spec i6 hy24 h1111 as ⟨y25, hy25⟩
  step with mont_square_multiply_spec 3#usize hy25 h101 as ⟨y26, hy26⟩
  step as ⟨i9, hi9⟩
  step with mont_square_multiply_spec i9 hy26 h11 as ⟨r, hr⟩
  refine mont_inv self r (mont_congr hr ?_)
  rw [hi, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, L_eq_limbs]
  norm_num

end Curve25519Dalek.scalar.Scalar29
