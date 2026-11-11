module
public import Proofs.Curve25519.Basic
public import Curve25519Dalek.Funs
public import Proofs.Representation.Scalar29
import Proofs.Curve25519.Prime
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
private theorem square_n_loop_spec (y : backend.serial.u32.scalar.Scalar29)
    (squarings : Usize) (hy : y.LimbsLt 29) (hy' : y.asNat < L) :
    square_n_loop { start := 0#usize, «end» := squarings } y
      ⦃ (r : backend.serial.u32.scalar.Scalar29) =>
      (r.asNat : ZMod L) * montgomeryRadix ^ 2 ^ squarings.val =
        (y.asNat : ZMod L) ^ 2 ^ squarings.val * montgomeryRadix ∧
      r.asNat < L ∧ r.LimbsLt 29 ⦄ := by
  unfold square_n_loop
  apply loop.spec_decr_nat (measure := fun (iter, _) => squarings.val - iter.start.val)
    (inv := fun (iter, y1) => iter.end = squarings ∧ iter.start.val ≤ squarings.val ∧
      (y1.asNat : ZMod L) * montgomeryRadix ^ 2 ^ iter.start.val =
        (y.asNat : ZMod L) ^ 2 ^ iter.start.val * montgomeryRadix ∧
      y1.asNat < L ∧ y1.LimbsLt 29)
  · rintro ⟨iter, y1⟩ ⟨hend, hstart, hinv, hy1, hy1b⟩
    unfold square_n_loop.body
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
theorem square_n_spec (y : backend.serial.u32.scalar.Scalar29)
    (squarings : Usize) (hy : y.LimbsLt 29) (hy' : y.asNat < L) :
    square_n y squarings
      ⦃ (r : backend.serial.u32.scalar.Scalar29) =>
      (r.asNat : ZMod L) * montgomeryRadix ^ 2 ^ squarings.val =
        (y.asNat : ZMod L) ^ 2 ^ squarings.val * montgomeryRadix ∧
      r.asNat < L ∧ r.LimbsLt 29 ⦄ := by
  unfold square_n
  exact square_n_loop_spec y squarings hy hy'

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
      ⦃ (r : backend.serial.u32.scalar.Scalar29) => Mont α (2 * e) r ⦄ := by
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
  rw [hr', ha', two_mul, pow_add]
  ring

private theorem mont_square_n_spec {α : ZMod L} {e : ℕ}
    {y : backend.serial.u32.scalar.Scalar29} (squarings : Usize) (hy : Mont α e y) :
    montgomery_invert.square_n y squarings
      ⦃ (r : backend.serial.u32.scalar.Scalar29) => Mont α (e * 2 ^ squarings.val) r ⦄ := by
  unfold Mont at hy ⊢
  obtain ⟨hy, hyL, hyb⟩ := hy
  step with montgomery_invert.square_n_spec y squarings hyb hyL as ⟨r, hr, hrL, hrb⟩
  refine ⟨?_, hrL, hrb⟩
  apply mul_right_cancel₀
    (pow_ne_zero (2 ^ squarings.val) backend.serial.u32.scalar.montgomeryRadix_natCast_ne_zero)
  rw [hr, hy, pow_mul, mul_pow]
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
  step with mont_square_spec h100 as ⟨x1000, h1000⟩
  step with mont_square_spec h1000 as ⟨x10000, h10000⟩
  step with mont_mul_spec h10000 h1 as ⟨x10001, h10001⟩
  step with mont_mul_spec h10001 h10000 as ⟨x100001, h100001⟩
  step with mont_square_spec h100001 as ⟨x1000010, h1000010⟩
  step with mont_mul_spec h1000010 h100001 as ⟨x1100011, h1100011⟩
  step with mont_square_spec h1100011 as ⟨x11000110, h11000110⟩
  step with mont_square_spec h11000110 as ⟨x110001100, h110001100⟩
  step with mont_mul_spec h110001100 h10001 as ⟨x110011101, h110011101⟩
  step with mont_mul_spec h110011101 h110001100 as ⟨x1100101001, h1100101001⟩
  step with mont_square_spec h1100101001 as ⟨x11001010010, h11001010010⟩
  step with mont_square_spec h11001010010 as ⟨x110010100100, h110010100100⟩
  step with mont_square_spec h110010100100 as ⟨x1100101001000, h1100101001000⟩
  step with mont_mul_spec h1100101001000 h1 as ⟨x1100101001001, h1100101001001⟩
  step with mont_mul_spec h1100101001001 h1100101001000 as ⟨x11001010010001, h11001010010001⟩
  step with mont_square_spec h11001010010001 as ⟨x110010100100010, h110010100100010⟩
  step with mont_mul_spec h110010100100010 h1100101001001 as ⟨x111111001101011, h111111001101011⟩
  step with mont_square_spec h111111001101011 as ⟨x1111110011010110, h1111110011010110⟩
  step with mont_mul_spec h1111110011010110 h1100101001 as ⟨x1111111111111111, h1111111111111111⟩
  step with mont_mul_spec h1111111111111111 h1 as ⟨y, hy⟩
  step with mont_square_n_spec 4#usize hy as ⟨y1, hy1⟩
  step with mont_mul_spec hy1 h1100011 as ⟨x100000000000001100011, h100000000000001100011⟩
  step with mont_square_n_spec 19#usize hy1 as ⟨y2, hy2⟩
  step with mont_mul_spec hy2 h1100101001001 as
    ⟨x1000000000000000000000000001100101001001, h1000000000000000000000000001100101001001⟩
  step with mont_square_n_spec 3#usize hy2 as ⟨y3, hy3⟩
  step with mont_mul_spec hy3 h1000000000000000000000000001100101001001 as
    ⟨x1001000000000000000000000000001100101001001, h1001000000000000000000000000001100101001001⟩
  step as ⟨i, hi⟩
  step with mont_square_multiply_spec i hy3 h10001 as ⟨y4, hy4⟩
  step with mont_square_multiply_spec 8#usize hy4 h110011101 as ⟨y5, hy5⟩
  step with mont_square_multiply_spec 14#usize hy5 h111111001101011 as ⟨y6, hy6⟩
  step with mont_square_multiply_spec 6#usize hy6 h1100101001 as ⟨y7, hy7⟩
  step with mont_square_multiply_spec 13#usize hy7 h1001000000000000000000000000001100101001001 as
    ⟨y8, hy8⟩
  step with mont_square_multiply_spec 2#usize hy8 h11001010010001 as ⟨y9, hy9⟩
  step with mont_square_multiply_spec 12#usize hy9 h111111001101011 as ⟨y10, hy10⟩
  step as ⟨i1, hi1⟩
  step with mont_square_multiply_spec i1 hy10 h100000000000001100011 as ⟨y11, hy11⟩
  step as ⟨i2, hi2⟩
  step with mont_square_multiply_spec i2 hy11 h1100011 as ⟨y12, hy12⟩
  step with mont_square_multiply_spec 10#usize hy12 h1001000000000000000000000000001100101001001 as
    ⟨y13, hy13⟩
  step with mont_square_multiply_spec 10#usize hy13 h1001000000000000000000000000001100101001001 as
    ⟨y14, hy14⟩
  step with mont_square_multiply_spec 3#usize hy14 h100000000000001100011 as ⟨y15, hy15⟩
  step with mont_square_multiply_spec 7#usize hy15 h111111001101011 as ⟨r, hr⟩
  refine mont_inv self r (mont_congr hr ?_)
  rw [hi, hi1, hi2, L_eq_limbs]
  norm_num

end Curve25519Dalek.scalar.Scalar29
