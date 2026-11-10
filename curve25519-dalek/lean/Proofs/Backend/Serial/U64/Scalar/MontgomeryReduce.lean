/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar52
public import Curve25519.Basic
public import Mathlib.Tactic.LinearCombination
import Proofs.Backend.Serial.U64.Constants.L
import Proofs.Backend.Serial.U64.Constants.Lfactor
import Proofs.Backend.Serial.U64.Scalar.M
import Proofs.Backend.Serial.U64.Scalar.Sub
import Proofs.Helpers.Limbs
import Subtle
import Proofs.Helpers.StepSpecs
public import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ReduceModChar
import Proofs.Backend.Serial.U64.Scalar.Index
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
import Proofs.Helpers.Bitwise
import Proofs.Helpers.Radix
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

open scoped Helpers.IndexStep Helpers.UpdateStep Helpers.MaskStep

namespace montgomery_reduce

/-- Adding `(s * lf mod m)` times `l` to `s` clears the low digit, when `lf * l ≡ -1 [MOD m]`. -/
private theorem add_mul_lfactor_mod {s lf l l0 m : ℕ} (hlf : (lf * l + 1) % m = 0)
    (hl : l % m = l0) : (s + s * lf % m * l0) % m = 0 := by
  rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff] at hlf ⊢
  rw [← hl]
  push_cast [ZMod.natCast_mod] at hlf ⊢
  linear_combination (s : ZMod m) * hlf

private theorem L_mod_two_pow_52_eq : curve25519.L % 2 ^ 52 = constants.L[0]!.val := by
  rw [L_mod_two_pow_52]
  unfold constants.L
  decide

open scoped Helpers.MLtStep

/-- `part1` under the weaker bound on `sum` met inside `montgomery_reduce`, with the bounds on
its outputs. -/
private theorem part1_lt_spec (sum : U128) (hsum : sum.val + 2 ^ 104 ≤ 2 ^ 128) :
    part1 sum ⦃ (c : U128) (p : U64) =>
      p.val = sum.val * constants.LFACTOR.val % 2 ^ 52 ∧
      c.val * 2 ^ 52 = sum.val + p.val * constants.L[0]!.val ∧ p.val < 2 ^ 52 ∧
      c.val < 2 ^ 76 ⦄ := by
  unfold part1
  have hL0 : constants.L[0]!.val < 2 ^ 52 := constants.L_spec.2 0 (by decide)
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨two_pow_52, h_two_pow_52⟩
  step as ⟨mask, h_mask⟩
  have h_mask' : mask.val = 2 ^ 52 - 1 := by scalar_tac
  step as ⟨p, hp⟩
  step as ⟨l0, hl0⟩
  step as ⟨pl0, hpl0, _⟩
  step as ⟨t, ht⟩
  step as ⟨c, hc, _⟩
  have hp' : p.val = sum.val * constants.LFACTOR.val % 2 ^ 52 := by
    rw [hp, hi1, core.num.U64.wrapping_mul_val_eq, hi, UScalar.cast_val_eq,
      UScalar.size_def, UScalarTy.U64_numBits_eq, Nat.mod_mod_of_dvd _ (by norm_num),
      Nat.mul_mod, Nat.mod_mod_of_dvd _ (by norm_num), ← Nat.mul_mod]
  rw [Nat.shiftRight_eq_div_pow] at hc
  refine ⟨hp', ?_, by scalar_tac, by scalar_tac⟩
  rw [hc, ht, hpl0, hl0]
  refine Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero ?_)
  rw [hp']
  exact add_mul_lfactor_mod constants.LFACTOR_spec.2 L_mod_two_pow_52_eq

@[step]
theorem part1_spec (sum : U128) (hsum : sum.val + 2 ^ 104 ≤ 2 ^ 128) :
    part1 sum ⦃ (c : U128) (p : U64) =>
      p.val = sum.val * constants.LFACTOR.val % 2 ^ 52 ∧
      c.val * 2 ^ 52 = sum.val + p.val * constants.L[0]!.val ⦄ := by
  step with part1_lt_spec as ⟨c, p, hp, hc, _⟩
  exact ⟨hp, hc⟩

@[step]
theorem part2_spec (sum : U128) :
    part2 sum ⦃ (c : U128) (w : U64) =>
      c.val * 2 ^ 52 + w.val = sum.val ∧ w.val < 2 ^ 52 ⦄ := by
  unfold part2
  step as ⟨i, hi⟩
  step as ⟨two_pow_52, h_two_pow_52⟩
  step as ⟨mask, h_mask⟩
  have h_mask' : mask.val = 2 ^ 52 - 1 := by scalar_tac
  step as ⟨w, hw⟩
  step as ⟨c, hc, _⟩
  have hw' : w.val = sum.val % 2 ^ 52 := by
    rw [hw, hi, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq,
      Nat.mod_mod_of_dvd _ (by norm_num)]
  refine ⟨?_, hw' ▸ Nat.mod_lt _ (by norm_num)⟩
  rw [hc, hw', Nat.shiftRight_eq_div_pow, Nat.div_add_mod']

end montgomery_reduce

set_option linter.hashCommand false in
#decompose montgomery_reduce montgomery_reduce_eq
  letRange 0 33 => montgomery_reduce.low
  letRange 1 26 => montgomery_reduce.high

attribute [nolint docBlame defsWithUnderscore] montgomery_reduce.low montgomery_reduce.high

/-- `L` from the limbs of the constant `L` (its limb 3 is zero). -/
private theorem L_eq_limbs' :
    curve25519.L = constants.L[0]!.val + 2 ^ 52 * constants.L[1]!.val +
      2 ^ 104 * constants.L[2]!.val + 2 ^ 208 * constants.L[4]!.val := by
  rw [L_eq_limbs]
  unfold constants.L
  decide

/-- The first five steps of the reduction, in closed form. -/
private theorem low_eq {l0 l1 l2 l3 l4 n0 n1 n2 n3 n4 c0 c1 c2 c3 c4 L0 L1 L2 L4 : ℕ}
    (h0 : c0 * 2 ^ 52 = l0 + n0 * L0) (h1 : c1 * 2 ^ 52 = c0 + l1 + n0 * L1 + n1 * L0)
    (h2 : c2 * 2 ^ 52 = c1 + l2 + n0 * L2 + n1 * L1 + n2 * L0)
    (h3 : c3 * 2 ^ 52 = c2 + l3 + n1 * L2 + n2 * L1 + n3 * L0)
    (h4 : c4 * 2 ^ 52 = c3 + l4 + n0 * L4 + n2 * L2 + n3 * L1 + n4 * L0) :
    l0 + 2 ^ 52 * l1 + 2 ^ 104 * l2 + 2 ^ 156 * l3 + 2 ^ 208 * l4 +
      (n0 + 2 ^ 52 * n1 + 2 ^ 104 * n2 + 2 ^ 156 * n3 + 2 ^ 208 * n4) *
        (L0 + 2 ^ 52 * L1 + 2 ^ 104 * L2 + 2 ^ 208 * L4) =
      montgomeryRadix * (c4 + n1 * L4 + n3 * L2 + n4 * L1 + 2 ^ 52 * (n2 * L4 + n4 * L2) +
        2 ^ 104 * (n3 * L4) + 2 ^ 156 * (n4 * L4)) := by
  rw [montgomeryRadix_def, show (2 : ℕ) ^ 104 = (2 ^ 52) ^ 2 by rw [← pow_mul],
    show (2 : ℕ) ^ 156 = (2 ^ 52) ^ 3 by rw [← pow_mul],
    show (2 : ℕ) ^ 208 = (2 ^ 52) ^ 4 by rw [← pow_mul],
    show (2 : ℕ) ^ 260 = (2 ^ 52) ^ 5 by rw [← pow_mul]]
  generalize (2 : ℕ) ^ 52 = B at *
  linear_combination -h0 - B * h1 - B ^ 2 * h2 - B ^ 3 * h3 - B ^ 4 * h4

attribute [local step] montgomery_reduce.part1_lt_spec

private theorem low_spec (limbs : Array U128 9#usize)
    (hlimbs : ∀ i : ℕ, i < 9 → limbs[i]!.val < 2 ^ 127) :
    montgomery_reduce.low limbs ⦃ (L1 n1 L2 n2 n3 L4 : U64) (c4 : U128) (n4 : U64) =>
      L1 = constants.L[1]! ∧ L2 = constants.L[2]! ∧ L4 = constants.L[4]! ∧
      n1.val < 2 ^ 52 ∧ n2.val < 2 ^ 52 ∧ n3.val < 2 ^ 52 ∧ n4.val < 2 ^ 52 ∧ c4.val < 2 ^ 76 ∧
      ∃ n0 < 2 ^ 52, limbs[0]!.val + 2 ^ 52 * limbs[1]!.val + 2 ^ 104 * limbs[2]!.val +
        2 ^ 156 * limbs[3]!.val + 2 ^ 208 * limbs[4]!.val +
        (n0 + 2 ^ 52 * n1.val + 2 ^ 104 * n2.val + 2 ^ 156 * n3.val + 2 ^ 208 * n4.val) * L =
        montgomeryRadix * (c4.val + n1.val * L4.val + n3.val * L2.val + n4.val * L1.val +
          2 ^ 52 * (n2.val * L4.val + n4.val * L2.val) + 2 ^ 104 * (n3.val * L4.val) +
          2 ^ 156 * (n4.val * L4.val)) ⦄ := by
  unfold montgomery_reduce.low
  have hl0 := hlimbs 0 (by decide)
  have hl1 := hlimbs 1 (by decide)
  have hl2 := hlimbs 2 (by decide)
  have hl3 := hlimbs 3 (by decide)
  have hl4 := hlimbs 4 (by decide)
  have hL1 : constants.L[1]!.val < 2 ^ 52 := constants.L_spec.2 1 (by decide)
  have hL2 : constants.L[2]!.val < 2 ^ 52 := constants.L_spec.2 2 (by decide)
  have hL4 : constants.L[4]!.val < 2 ^ 52 := constants.L_spec.2 4 (by decide)
  step*
  refine ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
    by assumption, by assumption, by assumption, n0, by assumption, ?_⟩
  subst_vars
  rw [L_eq_limbs']
  exact low_eq (c0 := carry.val) (c1 := carry1.val) (c2 := carry2.val) (c3 := carry3.val)
    (by simp only [*]) (by simp only [*]) (by simp only [*]) (by simp only [*])
    (by simp only [*])

/-- The two halves of the reduction combined: `limbs + n * L = montgomeryRadix * T`. -/
private theorem combine_eq (limbs : Array U128 9#usize) {n X T : ℕ}
    (hlow : limbs[0]!.val + 2 ^ 52 * limbs[1]!.val + 2 ^ 104 * limbs[2]!.val +
      2 ^ 156 * limbs[3]!.val + 2 ^ 208 * limbs[4]!.val + n * L = montgomeryRadix * X)
    (hhigh : X + (limbs[5]!.val + 2 ^ 52 * limbs[6]!.val + 2 ^ 104 * limbs[7]!.val +
      2 ^ 156 * limbs[8]!.val) = T) :
    limbs.asNat 52 + n * L = montgomeryRadix * T := by
  rw [Array.asNat_nine, montgomeryRadix_def]
  simp only [pow_mul']
  have h104 : (2 : ℕ) ^ 104 = (2 ^ 52) ^ 2 := by rw [← pow_mul]
  have h156 : (2 : ℕ) ^ 156 = (2 ^ 52) ^ 3 := by rw [← pow_mul]
  have h208 : (2 : ℕ) ^ 208 = (2 ^ 52) ^ 4 := by rw [← pow_mul]
  have h260 : (2 : ℕ) ^ 260 = (2 ^ 52) ^ 5 := by rw [← pow_mul]
  rw [montgomeryRadix_def, h104, h156, h208, h260] at hlow
  rw [h104, h156] at hhigh
  rw [h260]
  generalize (2 : ℕ) ^ 52 = B at *
  linear_combination hlow + B ^ 5 * hhigh

private theorem five_limbs_lt {a b c d e : ℕ} (ha : a < 2 ^ 52) (hb : b < 2 ^ 52)
    (hc : c < 2 ^ 52) (hd : d < 2 ^ 52) (he : e < 2 ^ 52) :
    a + 2 ^ 52 * b + 2 ^ 104 * c + 2 ^ 156 * d + 2 ^ 208 * e < montgomeryRadix := by
  rw [montgomeryRadix_def, show (2 : ℕ) ^ 104 = (2 ^ 52) ^ 2 by rw [← pow_mul],
    show (2 : ℕ) ^ 156 = (2 ^ 52) ^ 3 by rw [← pow_mul],
    show (2 : ℕ) ^ 208 = (2 ^ 52) ^ 4 by rw [← pow_mul],
    show (2 : ℕ) ^ 260 = (2 ^ 52) ^ 5 by rw [← pow_mul]]
  generalize (2 : ℕ) ^ 52 = B at *
  have key {x y C : ℕ} (hx : x < B) (hy : y < C) : x + B * y < B * C := by nlinarith
  calc a + B * b + B ^ 2 * c + B ^ 3 * d + B ^ 4 * e = a + B * (b + B * (c + B * (d + B * e))) :=
        by ring
    _ < B * (B * (B * (B * B))) := key ha (key hb (key hc (key hd he)))
    _ = B ^ 5 := by ring

private theorem reduce_lt {N n R T : ℕ} (h : N + n * L = R * T) (hN : N < R * L) (hn : n < R) :
    T < 2 * L := by
  have hnL : n * L < R * L := Nat.mul_lt_mul_of_pos_right hn L_pos
  have h' : R * T < R * (2 * L) := by rw [← h]; linarith
  exact Nat.lt_of_mul_lt_mul_left h'

private theorem reduce_mod {N n R T r : ℕ} (h : N + n * L = R * T)
    (hr : (r + L) % L = T % L) : r * R % L = N % L := by
  rw [Nat.add_mod_right] at hr
  calc r * R % L = T * R % L := Nat.ModEq.mul_right _ hr
    _ = (N + n * L) % L := by rw [h, mul_comm]
    _ = N % L := Nat.add_mul_mod_self_right _ _ _

private theorem high_spec (limbs : Array U128 9#usize) (L1 n1 L2 n2 n3 L4 : U64) (c4 : U128)
    (n4 : U64) (hlimbs : ∀ i : ℕ, i < 9 → limbs[i]!.val < 2 ^ 127) (hL1 : L1.val < 2 ^ 52)
    (hL2 : L2.val < 2 ^ 52) (hL4 : L4.val < 2 ^ 52) (hn1 : n1.val < 2 ^ 52)
    (hn2 : n2.val < 2 ^ 52) (hn3 : n3.val < 2 ^ 52) (hn4 : n4.val < 2 ^ 52)
    (hc4 : c4.val < 2 ^ 76) :
    montgomery_reduce.high limbs L1 n1 L2 n2 n3 L4 c4 n4 ⦃ (r0 r1 r2 : U64) (c8 : U128)
        (r3 : U64) =>
      r0.val < 2 ^ 52 ∧ r1.val < 2 ^ 52 ∧ r2.val < 2 ^ 52 ∧ r3.val < 2 ^ 52 ∧
      c4.val + n1.val * L4.val + n3.val * L2.val + n4.val * L1.val +
          2 ^ 52 * (n2.val * L4.val + n4.val * L2.val) + 2 ^ 104 * (n3.val * L4.val) +
          2 ^ 156 * (n4.val * L4.val) +
        (limbs[5]!.val + 2 ^ 52 * limbs[6]!.val + 2 ^ 104 * limbs[7]!.val +
          2 ^ 156 * limbs[8]!.val) =
      r0.val + 2 ^ 52 * r1.val + 2 ^ 104 * r2.val + 2 ^ 156 * r3.val + 2 ^ 208 * c8.val ⦄ := by
  unfold montgomery_reduce.high
  have hl5 := hlimbs 5 (by decide)
  have hl6 := hlimbs 6 (by decide)
  have hl7 := hlimbs 7 (by decide)
  have hl8 := hlimbs 8 (by decide)
  step*

@[step]
theorem montgomery_reduce_spec (limbs : Array U128 9#usize)
    (hlimbs : ∀ i : ℕ, i < 9 → limbs[i]!.val < 2 ^ 127)
    (hlimbs' : limbs.asNat 52 < montgomeryRadix * L) :
    montgomery_reduce limbs ⦃ (r : Scalar52) =>
      r.asNat * montgomeryRadix % L = limbs.asNat 52 % L ∧ r.asNat < L ∧
      r.LimbsLt 52 ⦄ := by
  rw [montgomery_reduce_eq]
  have hl5 := hlimbs 5 (by decide)
  have hl6 := hlimbs 6 (by decide)
  have hl7 := hlimbs 7 (by decide)
  have hl8 := hlimbs 8 (by decide)
  have hL1 : constants.L[1]!.val < 2 ^ 52 := constants.L_spec.2 1 (by decide)
  have hL2 : constants.L[2]!.val < 2 ^ 52 := constants.L_spec.2 2 (by decide)
  have hL4 : constants.L[4]!.val < 2 ^ 52 := constants.L_spec.2 4 (by decide)
  step with low_spec as ⟨L1, n1, L2, n2, n3, L4, c4, n4, hL1', hL2', hL4', hn1, hn2, hn3, hn4,
    hc4, n0, hn0, hlow⟩
  subst hL1' hL2' hL4'
  step with high_spec as ⟨r0, r1, r2, c8, r3, hr0, hr1, hr2, hr3, hhigh⟩
  have hT := combine_eq limbs hlow hhigh
  have hTlt := reduce_lt hT hlimbs' (five_limbs_lt hn0 hn1 hn2 hn3 hn4)
  clear hlimbs' hlow hhigh
  have hc8 : c8.val < 2 ^ 52 := by
    have := L_lt_two_pow_253
    scalar_tac
  step as ⟨r4, hr4⟩
  have hr4' : r4.val = c8.val := by
    rw [hr4, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  have hmake : Scalar52.asNat (Array.make 5#usize [r0, r1, r2, r3, r4]) =
      r0.val + 2 ^ 52 * r1.val + 2 ^ 104 * r2.val + 2 ^ 156 * r3.val + 2 ^ 208 * c8.val := by
    rw [Scalar52.asNat_eq]
    simp only [Array.getElem!_make, List.getElem!_cons_succ, List.getElem!_cons_zero, hr4']
  have ha : Scalar52.LimbsLt 52 (Array.make 5#usize [r0, r1, r2, r3, r4]) := by
    rw [Scalar52.LimbsLt, Nat.forall_lt_five]
    simp only [Array.getElem!_make, List.getElem!_cons_succ, List.getElem!_cons_zero, hr4']
    exact ⟨hr0, hr1, hr2, hr3, hc8⟩
  have ha' : Scalar52.asNat (Array.make 5#usize [r0, r1, r2, r3, r4]) < constants.L.asNat + L := by
    rw [hmake, constants.L_spec.1]
    scalar_tac
  step with sub_spec _ _ ha constants.L_spec.2 ha' constants.L_spec.1.le as ⟨r, hr, hrL, hrlimbs⟩
  rw [hmake, constants.L_spec.1] at hr
  exact ⟨reduce_mod hT hr, hrL, hrlimbs⟩

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52
