/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga, Wojciech Aleksander Wołoszyn
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar29
public import Curve25519.Basic
public import Mathlib.Tactic.LinearCombination
import Proofs.Backend.Serial.U32.Constants.L
import Proofs.Backend.Serial.U32.Constants.Lfactor
import Proofs.Backend.Serial.U32.Scalar.Index
import Proofs.Backend.Serial.U32.Scalar.M
import Proofs.Backend.Serial.U32.Scalar.Sub
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
import Proofs.Helpers.Bitwise
import Proofs.Helpers.Scalar29
import Proofs.Helpers.StepSpecs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Proofs.Helpers.Radix
public section

/-! # `Scalar29::montgomery_reduce`

Seventeen rows of carries: in rows 0 to 8 the factor `n_i` is chosen so that the row sum is a
multiple of `2 ^ 29`, in rows 9 to 16 the low 29 bits of the row sum are the limbs of the result.
Together the rows give `limbs + N * L = R * T`, with `N = Σ 2 ^ (29 * i) * n_i` and `T` the value
of the limbs `r_i` and the last carry. The function is decomposed into its rows. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29)

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

open scoped Helpers.IndexStep Helpers.MaskStep

namespace montgomery_reduce

/-- Adding `(s * lf mod m)` times `l` to `s` clears the low digit, when `lf * l ≡ -1 [MOD m]`. -/
private theorem add_mul_lfactor_mod {s lf l l0 m : ℕ} (hlf : (lf * l + 1) % m = 0)
    (hl : l % m = l0) : (s + s * lf % m * l0) % m = 0 := by
  rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff] at hlf ⊢
  rw [← hl]
  push_cast [ZMod.natCast_mod] at hlf ⊢
  linear_combination (s : ZMod m) * hlf

private theorem L_mod_two_pow_29_eq : curve25519.L % 2 ^ 29 = constants.L[0]!.val := by
  rw [L_mod_two_pow_29]
  unfold constants.L
  decide

/-- `part1` under the bound on `sum` met inside `montgomery_reduce`, with the bounds on its
outputs. -/
private theorem part1_lt_spec (sum : U64) (hsum : sum.val < 2 ^ 63 + 2 ^ 61) :
    part1 sum ⦃ (c : U64) (p : U32) =>
      p.val = sum.val * constants.LFACTOR.val % 2 ^ 29 ∧
      c.val * 2 ^ 29 = sum.val + p.val * constants.L[0]!.val ∧ p.val < 2 ^ 29 ∧
      c.val < 2 ^ 35 ⦄ := by
  unfold part1
  have hL0 : constants.L[0]!.val < 2 ^ 29 := constants.L_spec.2 0 (by decide)
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨two_pow_29, h_two_pow_29⟩
  step as ⟨mask, h_mask⟩
  have h_mask' : mask.val = 2 ^ 29 - 1 := by scalar_tac
  step as ⟨p, hp⟩
  step as ⟨l0, hl0⟩
  step as ⟨pl0, hpl0⟩
  have hp29 : p.val < 2 ^ 29 := by rw [hp]; exact Nat.mod_lt _ (by norm_num)
  have hpl0' : pl0.val < 2 ^ 58 := by
    rw [hpl0, hl0]
    exact (Nat.mul_lt_mul'' hp29 hL0).trans_eq (by norm_num)
  step as ⟨t, ht⟩
  step as ⟨c, hc, _⟩
  have hp' : p.val = sum.val * constants.LFACTOR.val % 2 ^ 29 := by
    rw [hp, hi1, core.num.U32.wrapping_mul_val_eq, hi, UScalar.cast_val_eq,
      UScalar.size_def, UScalarTy.U32_numBits_eq, Nat.mod_mod_of_dvd _ (by norm_num),
      Nat.mul_mod, Nat.mod_mod_of_dvd _ (by norm_num), ← Nat.mul_mod]
  rw [Nat.shiftRight_eq_div_pow] at hc
  have hc' : c.val * 2 ^ 29 = sum.val + p.val * constants.L[0]!.val := by
    rw [hc, ht, hpl0, hl0]
    refine Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero ?_)
    rw [hp']
    exact add_mul_lfactor_mod constants.LFACTOR_spec.2 L_mod_two_pow_29_eq
  refine ⟨hp', hc', hp29, ?_⟩
  have : p.val * constants.L[0]!.val < 2 ^ 58 := by rw [← hl0, ← hpl0]; exact hpl0'
  omega

@[step]
theorem part1_spec (sum : U64) (hsum : sum.val < 2 ^ 63 + 2 ^ 61) :
    part1 sum ⦃ (c : U64) (p : U32) =>
      p.val = sum.val * constants.LFACTOR.val % 2 ^ 29 ∧
      c.val * 2 ^ 29 = sum.val + p.val * constants.L[0]!.val ⦄ := by
  step with part1_lt_spec as ⟨c, p, hp, hc, _⟩
  exact ⟨hp, hc⟩

@[step]
theorem part2_spec (sum : U64) :
    part2 sum ⦃ (c : U64) (w : U32) =>
      c.val * 2 ^ 29 + w.val = sum.val ∧ w.val < 2 ^ 29 ⦄ := by
  unfold part2
  step as ⟨i, hi⟩
  step as ⟨two_pow_29, h_two_pow_29⟩
  step as ⟨mask, h_mask⟩
  have h_mask' : mask.val = 2 ^ 29 - 1 := by scalar_tac
  step as ⟨w, hw⟩
  step as ⟨c, hc, _⟩
  have hw' : w.val = sum.val % 2 ^ 29 := by
    rw [hw, hi, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq,
      Nat.mod_mod_of_dvd _ (by norm_num)]
  refine ⟨?_, hw' ▸ Nat.mod_lt _ (by norm_num)⟩
  rw [hc, hw', Nat.shiftRight_eq_div_pow, Nat.div_add_mod']

end montgomery_reduce

set_option linter.hashCommand false in
#decompose montgomery_reduce montgomery_reduce_eq
  letRange 0 2 => montgomery_reduce.row0
  letRange 1 6 => montgomery_reduce.row1
  letRange 2 8 => montgomery_reduce.row2
  letRange 3 10 => montgomery_reduce.row3
  letRange 4 12 => montgomery_reduce.row4
  letRange 5 11 => montgomery_reduce.row5
  letRange 6 11 => montgomery_reduce.row6
  letRange 7 11 => montgomery_reduce.row7
  letRange 8 14 => montgomery_reduce.row8
  letRange 9 13 => montgomery_reduce.row9
  letRange 10 11 => montgomery_reduce.row10
  letRange 11 9 => montgomery_reduce.row11
  letRange 12 7 => montgomery_reduce.row12
  letRange 13 5 => montgomery_reduce.row13
  letRange 14 5 => montgomery_reduce.row14
  letRange 15 5 => montgomery_reduce.row15
  letRange 16 5 => montgomery_reduce.row16

attribute [nolint docBlame defsWithUnderscore]
  montgomery_reduce.row0 montgomery_reduce.row1 montgomery_reduce.row2 montgomery_reduce.row3
  montgomery_reduce.row4 montgomery_reduce.row5 montgomery_reduce.row6 montgomery_reduce.row7
  montgomery_reduce.row8 montgomery_reduce.row9 montgomery_reduce.row10 montgomery_reduce.row11
  montgomery_reduce.row12 montgomery_reduce.row13 montgomery_reduce.row14 montgomery_reduce.row15
  montgomery_reduce.row16

/-- `m` on two factors below `2 ^ 29`. -/
private theorem m_lt_two_pow_58_spec (x y : U32) (hx : x.val < 2 ^ 29) (hy : y.val < 2 ^ 29) :
    m x y ⦃ (r : U64) => r.val = x.val * y.val ∧ r.val < 2 ^ 58 ⦄ := by
  step*

attribute [local step] montgomery_reduce.part1_lt_spec m_lt_two_pow_58_spec

/-- Row 0: `n0` makes the sum a multiple of `2 ^ 29`. -/
private theorem row0_spec (limbs : Array U64 17#usize) (hl : limbs[0]!.val < 2 ^ 63) :
    montgomery_reduce.row0 limbs ⦃ (c' : U64) (n0 : U32) =>
      c'.val * 2 ^ 29 = limbs[0]!.val + n0.val * constants.L[0]!.val ∧ c'.val < 2 ^ 35 ∧
        n0.val < 2 ^ 29 ⦄ := by
  unfold montgomery_reduce.row0
  step*

/-- Row 1: `n1` makes the sum a multiple of `2 ^ 29`. -/
private theorem row1_spec (limbs : Array U64 17#usize) (c : U64) (n0 : U32)
    (hl : limbs[1]!.val < 2 ^ 63) (hc : c.val < 2 ^ 35) (hn0 : n0.val < 2 ^ 29) :
    montgomery_reduce.row1 limbs c n0 ⦃ (L1 : U32) (c' : U64) (n1 : U32) =>
      L1 = constants.L[1]! ∧ c'.val * 2 ^ 29 = c.val + limbs[1]!.val + n0.val * L1.val +
        n1.val * constants.L[0]!.val ∧ c'.val < 2 ^ 35 ∧ n1.val < 2 ^ 29 ⦄ := by
  have := constants.L_spec.2 1 (by decide)
  unfold montgomery_reduce.row1
  step*

/-- Row 2: `n2` makes the sum a multiple of `2 ^ 29`. -/
private theorem row2_spec (limbs : Array U64 17#usize) (n0 L1 : U32) (c : U64) (n1 : U32)
    (hl : limbs[2]!.val < 2 ^ 63) (hc : c.val < 2 ^ 35) (hn0 : n0.val < 2 ^ 29)
    (hL1 : L1.val < 2 ^ 29) (hn1 : n1.val < 2 ^ 29) :
    montgomery_reduce.row2 limbs n0 L1 c n1 ⦃ (L2 : U32) (c' : U64) (n2 : U32) =>
      L2 = constants.L[2]! ∧ c'.val * 2 ^ 29 = c.val + limbs[2]!.val + n0.val * L2.val +
        n1.val * L1.val + n2.val * constants.L[0]!.val ∧ c'.val < 2 ^ 35 ∧ n2.val < 2 ^ 29 ⦄ := by
  have := constants.L_spec.2 2 (by decide)
  unfold montgomery_reduce.row2
  step*

/-- Row 3: `n3` makes the sum a multiple of `2 ^ 29`. -/
private theorem row3_spec (limbs : Array U64 17#usize) (n0 L1 n1 L2 : U32) (c : U64) (n2 : U32)
    (hl : limbs[3]!.val < 2 ^ 63) (hc : c.val < 2 ^ 35) (hn0 : n0.val < 2 ^ 29)
    (hL1 : L1.val < 2 ^ 29) (hn1 : n1.val < 2 ^ 29) (hL2 : L2.val < 2 ^ 29)
    (hn2 : n2.val < 2 ^ 29) :
    montgomery_reduce.row3 limbs n0 L1 n1 L2 c n2 ⦃ (L3 : U32) (c' : U64) (n3 : U32) =>
      L3 = constants.L[3]! ∧ c'.val * 2 ^ 29 = c.val + limbs[3]!.val + n0.val * L3.val +
        n1.val * L2.val + n2.val * L1.val + n3.val * constants.L[0]!.val ∧ c'.val < 2 ^ 35 ∧
        n3.val < 2 ^ 29 ⦄ := by
  have := constants.L_spec.2 3 (by decide)
  unfold montgomery_reduce.row3
  step*

/-- Row 4: `n4` makes the sum a multiple of `2 ^ 29`. -/
private theorem row4_spec (limbs : Array U64 17#usize) (n0 L1 n1 L2 n2 L3 : U32) (c : U64)
    (n3 : U32) (hl : limbs[4]!.val < 2 ^ 63) (hc : c.val < 2 ^ 35) (hn0 : n0.val < 2 ^ 29)
    (hL1 : L1.val < 2 ^ 29) (hn1 : n1.val < 2 ^ 29) (hL2 : L2.val < 2 ^ 29) (hn2 : n2.val < 2 ^ 29)
    (hL3 : L3.val < 2 ^ 29) (hn3 : n3.val < 2 ^ 29) :
    montgomery_reduce.row4 limbs n0 L1 n1 L2 n2 L3 c n3 ⦃ (L4 : U32) (c' : U64) (n4 : U32) =>
      L4 = constants.L[4]! ∧ c'.val * 2 ^ 29 = c.val + limbs[4]!.val + n0.val * L4.val +
        n1.val * L3.val + n2.val * L2.val + n3.val * L1.val + n4.val * constants.L[0]!.val ∧
        c'.val < 2 ^ 35 ∧ n4.val < 2 ^ 29 ⦄ := by
  have := constants.L_spec.2 4 (by decide)
  unfold montgomery_reduce.row4
  step*

/-- Row 5: `n5` makes the sum a multiple of `2 ^ 29`. -/
private theorem row5_spec (limbs : Array U64 17#usize) (L1 n1 L2 n2 L3 n3 L4 : U32) (c : U64)
    (n4 : U32) (hl : limbs[5]!.val < 2 ^ 63) (hc : c.val < 2 ^ 35) (hL1 : L1.val < 2 ^ 29)
    (hn1 : n1.val < 2 ^ 29) (hL2 : L2.val < 2 ^ 29) (hn2 : n2.val < 2 ^ 29) (hL3 : L3.val < 2 ^ 29)
    (hn3 : n3.val < 2 ^ 29) (hL4 : L4.val < 2 ^ 29) (hn4 : n4.val < 2 ^ 29) :
    montgomery_reduce.row5 limbs L1 n1 L2 n2 L3 n3 L4 c n4 ⦃ (c' : U64) (n5 : U32) =>
      c'.val * 2 ^ 29 = c.val + limbs[5]!.val + n1.val * L4.val + n2.val * L3.val + n3.val * L2.val
        + n4.val * L1.val + n5.val * constants.L[0]!.val ∧ c'.val < 2 ^ 35 ∧ n5.val < 2 ^ 29 ⦄ := by
  unfold montgomery_reduce.row5
  step*

/-- Row 6: `n6` makes the sum a multiple of `2 ^ 29`. -/
private theorem row6_spec (limbs : Array U64 17#usize) (L1 L2 n2 L3 n3 L4 n4 : U32) (c : U64)
    (n5 : U32) (hl : limbs[6]!.val < 2 ^ 63) (hc : c.val < 2 ^ 35) (hL1 : L1.val < 2 ^ 29)
    (hL2 : L2.val < 2 ^ 29) (hn2 : n2.val < 2 ^ 29) (hL3 : L3.val < 2 ^ 29) (hn3 : n3.val < 2 ^ 29)
    (hL4 : L4.val < 2 ^ 29) (hn4 : n4.val < 2 ^ 29) (hn5 : n5.val < 2 ^ 29) :
    montgomery_reduce.row6 limbs L1 L2 n2 L3 n3 L4 n4 c n5 ⦃ (c' : U64) (n6 : U32) =>
      c'.val * 2 ^ 29 = c.val + limbs[6]!.val + n2.val * L4.val + n3.val * L3.val + n4.val * L2.val
        + n5.val * L1.val + n6.val * constants.L[0]!.val ∧ c'.val < 2 ^ 35 ∧ n6.val < 2 ^ 29 ⦄ := by
  unfold montgomery_reduce.row6
  step*

/-- Row 7: `n7` makes the sum a multiple of `2 ^ 29`. -/
private theorem row7_spec (limbs : Array U64 17#usize) (L1 L2 L3 n3 L4 n4 n5 : U32) (c : U64)
    (n6 : U32) (hl : limbs[7]!.val < 2 ^ 63) (hc : c.val < 2 ^ 35) (hL1 : L1.val < 2 ^ 29)
    (hL2 : L2.val < 2 ^ 29) (hL3 : L3.val < 2 ^ 29) (hn3 : n3.val < 2 ^ 29) (hL4 : L4.val < 2 ^ 29)
    (hn4 : n4.val < 2 ^ 29) (hn5 : n5.val < 2 ^ 29) (hn6 : n6.val < 2 ^ 29) :
    montgomery_reduce.row7 limbs L1 L2 L3 n3 L4 n4 n5 c n6 ⦃ (c' : U64) (n7 : U32) =>
      c'.val * 2 ^ 29 = c.val + limbs[7]!.val + n3.val * L4.val + n4.val * L3.val + n5.val * L2.val
        + n6.val * L1.val + n7.val * constants.L[0]!.val ∧ c'.val < 2 ^ 35 ∧ n7.val < 2 ^ 29 ⦄ := by
  unfold montgomery_reduce.row7
  step*

/-- Row 8: `n8` makes the sum a multiple of `2 ^ 29`. -/
private theorem row8_spec (limbs : Array U64 17#usize) (n0 L1 L2 L3 L4 n4 n5 n6 : U32) (c : U64)
    (n7 : U32) (hl : limbs[8]!.val < 2 ^ 63) (hc : c.val < 2 ^ 35) (hn0 : n0.val < 2 ^ 29)
    (hL1 : L1.val < 2 ^ 29) (hL2 : L2.val < 2 ^ 29) (hL3 : L3.val < 2 ^ 29) (hL4 : L4.val < 2 ^ 29)
    (hn4 : n4.val < 2 ^ 29) (hn5 : n5.val < 2 ^ 29) (hn6 : n6.val < 2 ^ 29)
    (hn7 : n7.val < 2 ^ 29) :
    montgomery_reduce.row8 limbs n0 L1 L2 L3 L4 n4 n5 n6 c n7 ⦃ (L8 : U32) (c' : U64) (n8 : U32) =>
      L8 = constants.L[8]! ∧ c'.val * 2 ^ 29 = c.val + limbs[8]!.val + n0.val * L8.val +
        n4.val * L4.val + n5.val * L3.val + n6.val * L2.val + n7.val * L1.val +
        n8.val * constants.L[0]!.val ∧ c'.val < 2 ^ 35 ∧ n8.val < 2 ^ 29 ⦄ := by
  have := constants.L_spec.2 8 (by decide)
  unfold montgomery_reduce.row8
  step*

/-- Row 9: the low 29 bits of the sum are limb 0 of the result. -/
private theorem row9_spec (limbs : Array U64 17#usize) (L1 n1 L2 L3 L4 n5 n6 n7 L8 : U32) (c : U64)
    (n8 : U32) (hl : limbs[9]!.val < 2 ^ 63) (hc : c.val < 2 ^ 35) (hL1 : L1.val < 2 ^ 29)
    (hn1 : n1.val < 2 ^ 29) (hL2 : L2.val < 2 ^ 29) (hL3 : L3.val < 2 ^ 29) (hL4 : L4.val < 2 ^ 29)
    (hn5 : n5.val < 2 ^ 29) (hn6 : n6.val < 2 ^ 29) (hn7 : n7.val < 2 ^ 29) (hL8 : L8.val < 2 ^ 29)
    (hn8 : n8.val < 2 ^ 29) :
    montgomery_reduce.row9 limbs L1 n1 L2 L3 L4 n5 n6 n7 L8 c n8 ⦃ (c' : U64) (r0 : U32) =>
      c'.val * 2 ^ 29 + r0.val = c.val + limbs[9]!.val + n1.val * L8.val + n5.val * L4.val +
        n6.val * L3.val + n7.val * L2.val + n8.val * L1.val ∧ c'.val < 2 ^ 35 ∧ r0.val < 2 ^ 29
        ⦄ := by
  unfold montgomery_reduce.row9
  step*

/-- Row 10: the low 29 bits of the sum are limb 1 of the result. -/
private theorem row10_spec (limbs : Array U64 17#usize) (L2 n2 L3 L4 n6 n7 L8 n8 : U32) (c : U64)
    (hl : limbs[10]!.val < 2 ^ 63) (hc : c.val < 2 ^ 35) (hL2 : L2.val < 2 ^ 29)
    (hn2 : n2.val < 2 ^ 29) (hL3 : L3.val < 2 ^ 29) (hL4 : L4.val < 2 ^ 29) (hn6 : n6.val < 2 ^ 29)
    (hn7 : n7.val < 2 ^ 29) (hL8 : L8.val < 2 ^ 29) (hn8 : n8.val < 2 ^ 29) :
    montgomery_reduce.row10 limbs L2 n2 L3 L4 n6 n7 L8 n8 c ⦃ (c' : U64) (r1 : U32) =>
      c'.val * 2 ^ 29 + r1.val = c.val + limbs[10]!.val + n2.val * L8.val + n6.val * L4.val +
        n7.val * L3.val + n8.val * L2.val ∧ c'.val < 2 ^ 35 ∧ r1.val < 2 ^ 29 ⦄ := by
  unfold montgomery_reduce.row10
  step*

/-- Row 11: the low 29 bits of the sum are limb 2 of the result. -/
private theorem row11_spec (limbs : Array U64 17#usize) (L3 n3 L4 n7 L8 n8 : U32) (c : U64)
    (hl : limbs[11]!.val < 2 ^ 63) (hc : c.val < 2 ^ 35) (hL3 : L3.val < 2 ^ 29)
    (hn3 : n3.val < 2 ^ 29) (hL4 : L4.val < 2 ^ 29) (hn7 : n7.val < 2 ^ 29) (hL8 : L8.val < 2 ^ 29)
    (hn8 : n8.val < 2 ^ 29) :
    montgomery_reduce.row11 limbs L3 n3 L4 n7 L8 n8 c ⦃ (c' : U64) (r2 : U32) =>
      c'.val * 2 ^ 29 + r2.val = c.val + limbs[11]!.val + n3.val * L8.val + n7.val * L4.val +
        n8.val * L3.val ∧ c'.val < 2 ^ 35 ∧ r2.val < 2 ^ 29 ⦄ := by
  unfold montgomery_reduce.row11
  step*

/-- Row 12: the low 29 bits of the sum are limb 3 of the result. -/
private theorem row12_spec (limbs : Array U64 17#usize) (L4 n4 L8 n8 : U32) (c : U64)
    (hl : limbs[12]!.val < 2 ^ 63) (hc : c.val < 2 ^ 35) (hL4 : L4.val < 2 ^ 29)
    (hn4 : n4.val < 2 ^ 29) (hL8 : L8.val < 2 ^ 29) (hn8 : n8.val < 2 ^ 29) :
    montgomery_reduce.row12 limbs L4 n4 L8 n8 c ⦃ (c' : U64) (r3 : U32) =>
      c'.val * 2 ^ 29 + r3.val = c.val + limbs[12]!.val + n4.val * L8.val + n8.val * L4.val ∧
        c'.val < 2 ^ 35 ∧ r3.val < 2 ^ 29 ⦄ := by
  unfold montgomery_reduce.row12
  step*

/-- Row 13: the low 29 bits of the sum are limb 4 of the result. -/
private theorem row13_spec (limbs : Array U64 17#usize) (n5 L8 : U32) (c : U64)
    (hl : limbs[13]!.val < 2 ^ 63) (hc : c.val < 2 ^ 35) (hn5 : n5.val < 2 ^ 29)
    (hL8 : L8.val < 2 ^ 29) :
    montgomery_reduce.row13 limbs n5 L8 c ⦃ (c' : U64) (r4 : U32) =>
      c'.val * 2 ^ 29 + r4.val = c.val + limbs[13]!.val + n5.val * L8.val ∧ c'.val < 2 ^ 35 ∧
        r4.val < 2 ^ 29 ⦄ := by
  unfold montgomery_reduce.row13
  step*

/-- Row 14: the low 29 bits of the sum are limb 5 of the result. -/
private theorem row14_spec (limbs : Array U64 17#usize) (n6 L8 : U32) (c : U64)
    (hl : limbs[14]!.val < 2 ^ 63) (hc : c.val < 2 ^ 35) (hn6 : n6.val < 2 ^ 29)
    (hL8 : L8.val < 2 ^ 29) :
    montgomery_reduce.row14 limbs n6 L8 c ⦃ (c' : U64) (r5 : U32) =>
      c'.val * 2 ^ 29 + r5.val = c.val + limbs[14]!.val + n6.val * L8.val ∧ c'.val < 2 ^ 35 ∧
        r5.val < 2 ^ 29 ⦄ := by
  unfold montgomery_reduce.row14
  step*

/-- Row 15: the low 29 bits of the sum are limb 6 of the result. -/
private theorem row15_spec (limbs : Array U64 17#usize) (n7 L8 : U32) (c : U64)
    (hl : limbs[15]!.val < 2 ^ 63) (hc : c.val < 2 ^ 35) (hn7 : n7.val < 2 ^ 29)
    (hL8 : L8.val < 2 ^ 29) :
    montgomery_reduce.row15 limbs n7 L8 c ⦃ (c' : U64) (r6 : U32) =>
      c'.val * 2 ^ 29 + r6.val = c.val + limbs[15]!.val + n7.val * L8.val ∧ c'.val < 2 ^ 35 ∧
        r6.val < 2 ^ 29 ⦄ := by
  unfold montgomery_reduce.row15
  step*

/-- Row 16: the low 29 bits of the sum are limb 7 of the result. -/
private theorem row16_spec (limbs : Array U64 17#usize) (L8 n8 : U32) (c : U64)
    (hl : limbs[16]!.val < 2 ^ 63) (hc : c.val < 2 ^ 35) (hL8 : L8.val < 2 ^ 29)
    (hn8 : n8.val < 2 ^ 29) :
    montgomery_reduce.row16 limbs L8 n8 c ⦃ (c' : U64) (r7 : U32) =>
      c'.val * 2 ^ 29 + r7.val = c.val + limbs[16]!.val + n8.val * L8.val ∧ c'.val < 2 ^ 35 ∧
        r7.val < 2 ^ 29 ⦄ := by
  unfold montgomery_reduce.row16
  step*

/-- `L` from the limbs of the constant `L` (its limbs 5 to 7 are zero). -/
private theorem L_eq_limbs' :
    curve25519.L = constants.L[0]!.val + 2 ^ 29 * constants.L[1]!.val +
      2 ^ 58 * constants.L[2]!.val + 2 ^ 87 * constants.L[3]!.val +
      2 ^ 116 * constants.L[4]!.val + 2 ^ 232 * constants.L[8]!.val := by
  rw [L_eq_limbs29]
  unfold constants.L
  decide

/-- Nine limbs below `2 ^ 29`, with these weights, are below the Montgomery radix. -/
private theorem nine_limbs_lt {a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℕ} (h0 : a0 < 2 ^ 29) (h1 : a1 < 2 ^ 29)
    (h2 : a2 < 2 ^ 29) (h3 : a3 < 2 ^ 29) (h4 : a4 < 2 ^ 29) (h5 : a5 < 2 ^ 29)
    (h6 : a6 < 2 ^ 29) (h7 : a7 < 2 ^ 29) (h8 : a8 < 2 ^ 29) :
    a0 + 2 ^ 29 * a1 + 2 ^ 58 * a2 + 2 ^ 87 * a3 + 2 ^ 116 * a4 + 2 ^ 145 * a5 + 2 ^ 174 * a6 +
      2 ^ 203 * a7 + 2 ^ 232 * a8 < montgomeryRadix := by
  rw [montgomeryRadix_def,
      show (2 : ℕ) ^ 58 = (2 ^ 29) ^ 2 by rw [← pow_mul],
      show (2 : ℕ) ^ 87 = (2 ^ 29) ^ 3 by rw [← pow_mul],
      show (2 : ℕ) ^ 116 = (2 ^ 29) ^ 4 by rw [← pow_mul],
      show (2 : ℕ) ^ 145 = (2 ^ 29) ^ 5 by rw [← pow_mul],
      show (2 : ℕ) ^ 174 = (2 ^ 29) ^ 6 by rw [← pow_mul],
      show (2 : ℕ) ^ 203 = (2 ^ 29) ^ 7 by rw [← pow_mul],
      show (2 : ℕ) ^ 232 = (2 ^ 29) ^ 8 by rw [← pow_mul],
      show (2 : ℕ) ^ 261 = (2 ^ 29) ^ 9 by rw [← pow_mul]]
  generalize (2 : ℕ) ^ 29 = B at *
  have key {x y C : ℕ} (hx : x < B) (hy : y < C) : x + B * y < B * C := by nlinarith
  calc _ = a0 + B * (a1 + B * (a2 + B * (a3 + B * (a4 + B * (a5 + B * (a6 + B * (a7 +
        B * a8))))))) := by ring
    _ < B * (B * (B * (B * (B * (B * (B * (B * B))))))) :=
      key h0 (key h1 (key h2 (key h3 (key h4 (key h5 (key h6 (key h7 h8)))))))
    _ = B ^ 9 := by ring

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

/-- **Spec for `backend.serial.u32.scalar.Scalar29.montgomery_reduce`**:
- The result is `limbs / R` modulo `L`, reduced below `L`, with limbs below `2 ^ 29`. -/
@[step]
theorem montgomery_reduce_spec (limbs : Array U64 17#usize)
    (hlimbs : ∀ i : ℕ, i < 17 → limbs[i]!.val < 2 ^ 63)
    (hlimbs' : limbs.asNat 29 < montgomeryRadix * L) :
    montgomery_reduce limbs ⦃ (r : Scalar29) =>
      r.asNat * montgomeryRadix % L = limbs.asNat 29 % L ∧ r.asNat < L ∧ r.LimbsLt 29 ⦄ := by
  rw [montgomery_reduce_eq]
  have := hlimbs 0 (by decide)
  have := hlimbs 1 (by decide)
  have := hlimbs 2 (by decide)
  have := hlimbs 3 (by decide)
  have := hlimbs 4 (by decide)
  have := hlimbs 5 (by decide)
  have := hlimbs 6 (by decide)
  have := hlimbs 7 (by decide)
  have := hlimbs 8 (by decide)
  have := hlimbs 9 (by decide)
  have := hlimbs 10 (by decide)
  have := hlimbs 11 (by decide)
  have := hlimbs 12 (by decide)
  have := hlimbs 13 (by decide)
  have := hlimbs 14 (by decide)
  have := hlimbs 15 (by decide)
  have := hlimbs 16 (by decide)
  have := constants.L_spec.2 0 (by decide)
  have := constants.L_spec.2 1 (by decide)
  have := constants.L_spec.2 2 (by decide)
  have := constants.L_spec.2 3 (by decide)
  have := constants.L_spec.2 4 (by decide)
  have := constants.L_spec.2 8 (by decide)
  step with row0_spec as ⟨c0, n0, h0, hc0, hn0⟩
  step with row1_spec as ⟨L1, c1, n1, hL1, h1, hc1, hn1⟩
  subst hL1
  step with row2_spec as ⟨L2, c2, n2, hL2, h2, hc2, hn2⟩
  subst hL2
  step with row3_spec as ⟨L3, c3, n3, hL3, h3, hc3, hn3⟩
  subst hL3
  step with row4_spec as ⟨L4, c4, n4, hL4, h4, hc4, hn4⟩
  subst hL4
  step with row5_spec as ⟨c5, n5, h5, hc5, hn5⟩
  step with row6_spec as ⟨c6, n6, h6, hc6, hn6⟩
  step with row7_spec as ⟨c7, n7, h7, hc7, hn7⟩
  step with row8_spec as ⟨L8, c8, n8, hL8, h8, hc8, hn8⟩
  subst hL8
  step with row9_spec as ⟨c9, r0, h9, hc9, hr0⟩
  step with row10_spec as ⟨c10, r1, h10, hc10, hr1⟩
  step with row11_spec as ⟨c11, r2, h11, hc11, hr2⟩
  step with row12_spec as ⟨c12, r3, h12, hc12, hr3⟩
  step with row13_spec as ⟨c13, r4, h13, hc13, hr4⟩
  step with row14_spec as ⟨c14, r5, h14, hc14, hr5⟩
  step with row15_spec as ⟨c15, r6, h15, hc15, hr6⟩
  step with row16_spec as ⟨c16, r7, h16, hc16, hr7⟩
  have hT : limbs.asNat 29 + (n0.val + 2 ^ 29 * n1.val + 2 ^ 58 * n2.val + 2 ^ 87 * n3.val +
      2 ^ 116 * n4.val + 2 ^ 145 * n5.val + 2 ^ 174 * n6.val + 2 ^ 203 * n7.val +
      2 ^ 232 * n8.val) * L =
      montgomeryRadix * (r0.val + 2 ^ 29 * r1.val + 2 ^ 58 * r2.val + 2 ^ 87 * r3.val +
        2 ^ 116 * r4.val + 2 ^ 145 * r5.val + 2 ^ 174 * r6.val + 2 ^ 203 * r7.val +
        2 ^ 232 * c16.val) := by
    rw [Array.asNat_eq_sum, montgomeryRadix_def, L_eq_limbs',
        show (2 : ℕ) ^ 58 = (2 ^ 29) ^ 2 by rw [← pow_mul],
        show (2 : ℕ) ^ 87 = (2 ^ 29) ^ 3 by rw [← pow_mul],
        show (2 : ℕ) ^ 116 = (2 ^ 29) ^ 4 by rw [← pow_mul],
        show (2 : ℕ) ^ 145 = (2 ^ 29) ^ 5 by rw [← pow_mul],
        show (2 : ℕ) ^ 174 = (2 ^ 29) ^ 6 by rw [← pow_mul],
        show (2 : ℕ) ^ 203 = (2 ^ 29) ^ 7 by rw [← pow_mul],
        show (2 : ℕ) ^ 232 = (2 ^ 29) ^ 8 by rw [← pow_mul],
        show (2 : ℕ) ^ 261 = (2 ^ 29) ^ 9 by rw [← pow_mul]]
    simp only [UScalar.ofNatCore_val_eq, pow_mul]
    generalize (2 : ℕ) ^ 29 = B at *
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one, one_mul]
    linear_combination -h0 - B * h1 - B ^ 2 * h2 - B ^ 3 * h3 - B ^ 4 * h4 - B ^ 5 * h5
      - B ^ 6 * h6 - B ^ 7 * h7 - B ^ 8 * h8 - B ^ 9 * h9 - B ^ 10 * h10 - B ^ 11 * h11
      - B ^ 12 * h12 - B ^ 13 * h13 - B ^ 14 * h14 - B ^ 15 * h15 - B ^ 16 * h16
  have hTlt := reduce_lt hT hlimbs' (nine_limbs_lt hn0 hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8)
  clear hlimbs' h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  have hc16' : c16.val < 2 ^ 29 := by
    have := L_lt_two_pow_253
    scalar_tac
  step as ⟨r8, hr8⟩
  have hr8' : r8.val = c16.val := by
    rw [hr8, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  have hmake : Scalar29.asNat (Array.make 9#usize [r0, r1, r2, r3, r4, r5, r6, r7, r8]) =
      r0.val + 2 ^ 29 * r1.val + 2 ^ 58 * r2.val + 2 ^ 87 * r3.val +
        2 ^ 116 * r4.val + 2 ^ 145 * r5.val + 2 ^ 174 * r6.val + 2 ^ 203 * r7.val +
        2 ^ 232 * c16.val := by
    rw [Scalar29.asNat_eq]
    simp only [Array.getElem!_make, List.getElem!_cons_succ, List.getElem!_cons_zero, hr8']
  have ha : Scalar29.LimbsLt 29 (Array.make 9#usize [r0, r1, r2, r3, r4, r5, r6, r7, r8]) := by
    intro i hi
    interval_cases i <;>
      simp only [Array.getElem!_make, List.getElem!_cons_succ, List.getElem!_cons_zero, hr8'] <;>
      assumption
  have ha' : Scalar29.asNat (Array.make 9#usize [r0, r1, r2, r3, r4, r5, r6, r7, r8]) <
      constants.L.asNat + L := by
    rw [hmake, constants.L_spec.1]
    scalar_tac
  step with sub_spec _ _ ha constants.L_spec.2 ha' constants.L_spec.1.le as ⟨r, hr, hrL, hrlimbs⟩
  rw [hmake, constants.L_spec.1] at hr
  exact ⟨reduce_mod hT hr, hrL, hrlimbs⟩

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29
