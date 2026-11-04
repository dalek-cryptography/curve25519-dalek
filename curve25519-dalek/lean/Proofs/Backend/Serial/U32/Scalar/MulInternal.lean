/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Aleksander Wołoszyn
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar29
public import Curve25519.Basic
import Proofs.Backend.Serial.U32.Scalar.Index
import Proofs.Backend.Serial.U32.Scalar.M
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
import Proofs.Helpers.Scalar29
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
public section

/-! # `Scalar29::mul_internal`

Multiplies nine radix-`2^29` limbs into seventeen coefficients with a one-level Karatsuba
decomposition: the middle coefficients are computed with wrapping arithmetic from the sums of the
low and high halves. The function is split into five blocks (`mulLow`, `mulHigh`, `mulFix`,
`mulMidLow`, `mulMidHigh`); after each, every coefficient modulo `2^64` is a fixed polynomial in
the limbs (`S1` … `S5`). The final coefficients are the schoolbook ones
(`productCoefficients`), which are below `2^62`, so the residues determine them. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29)

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

open scoped Helpers.M32LtStep

set_option linter.hashCommand false in
#decompose mul_internal mul_internal_eq
  letRange 1 62 => mulLow
  letRange 2 46 => mulHigh
  letRange 3 28 => mulFix
  letRange 4 44 => mulMidLow
  letRange 5 34 => mulMidHigh

/-- Coefficients 0 to 8 of the low halves. -/
add_decl_doc mulLow

/-- Coefficients 10 to 16 of the high halves, combined with 5 to 7. -/
add_decl_doc mulHigh

/-- The wrapping corrections of coefficients 5 to 11. -/
add_decl_doc mulFix

/-- The sums of the halves and the middle coefficients 5 to 8. -/
add_decl_doc mulMidLow

/-- The middle coefficients 9 to 11 and the terms of coefficient 12. -/
add_decl_doc mulMidHigh

local notation "Z" => ZMod (2 ^ 64)

/-- A limb as an element of `ℤ/2^64`. -/
private abbrev L (a : Scalar29) (i : ℕ) : Z := ((a[i]!).val : Z)

/-- `wrapping_sub` in `ℤ/2^64`. -/
private theorem wrapping_sub_cast (x y : U64) :
    ((core.num.U64.wrapping_sub x y).val : Z) = (x.val : Z) - (y.val : Z) := by
  have hy : y.val ≤ 2 ^ 64 := y.hBounds.le
  have h_cast : ((x.val + (2 ^ 64 - y.val) : ℕ) : Z) = (x.val : Z) - (y.val : Z) := by
    rw [Nat.cast_add, Nat.cast_sub hy, ZMod.natCast_self]
    ring
  rw [← h_cast]
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  simp only [core.num.U64.wrapping_sub_val_eq, UScalar.size, UScalarTy.numBits, Nat.mod_mod]

/-- `wrapping_add` in `ℤ/2^64`. -/
private theorem wrapping_add_cast (x y : U64) :
    ((core.num.U64.wrapping_add x y).val : Z) = (x.val : Z) + (y.val : Z) := by
  rw [← Nat.cast_add]
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  simp only [core.num.U64.wrapping_add_val_eq, UScalar.size, UScalarTy.numBits, Nat.mod_mod]

/-- The coefficients after `mulLow`. -/
private def S1 (a b : Scalar29) : List Z :=
  [(L a 0) * (L b 0),
   (L a 0) * (L b 1) + (L a 1) * (L b 0),
   (L a 0) * (L b 2) + (L a 1) * (L b 1) + (L a 2) * (L b 0),
   (L a 0) * (L b 3) + (L a 1) * (L b 2) + (L a 2) * (L b 1) + (L a 3) * (L b 0),
   (L a 0) * (L b 4) + (L a 1) * (L b 3) + (L a 2) * (L b 2) + (L a 3) * (L b 1) + (L a 4) * (L b
     0),
   (L a 1) * (L b 4) + (L a 2) * (L b 3) + (L a 3) * (L b 2) + (L a 4) * (L b 1),
   (L a 2) * (L b 4) + (L a 3) * (L b 3) + (L a 4) * (L b 2),
   (L a 3) * (L b 4) + (L a 4) * (L b 3),
   ((L a 4) * (L b 4)) - (((L a 0) * (L b 3) + (L a 1) * (L b 2) + (L a 2) * (L b 1) + (L a 3) * (L
     b 0))),
   0,
   0,
   0,
   0,
   0,
   0,
   0,
   0]

/-- The coefficients after `mulHigh`. -/
private def S2 (a b : Scalar29) : List Z :=
  [(S1 a b)[0]!,
   (S1 a b)[1]!,
   (S1 a b)[2]!,
   (S1 a b)[3]!,
   (S1 a b)[4]!,
   (S1 a b)[5]!,
   (S1 a b)[6]!,
   (S1 a b)[7]!,
   (S1 a b)[8]!,
   (S1 a b)[9]!,
   (((S1 a b)[5]!)) - ((L a 5) * (L b 5)),
   (((S1 a b)[6]!)) - ((L a 5) * (L b 6) + (L a 6) * (L b 5)),
   (((S1 a b)[7]!)) - ((L a 5) * (L b 7) + (L a 6) * (L b 6) + (L a 7) * (L b 5)),
   (L a 5) * (L b 8) + (L a 6) * (L b 7) + (L a 7) * (L b 6) + (L a 8) * (L b 5),
   (L a 6) * (L b 8) + (L a 7) * (L b 7) + (L a 8) * (L b 6),
   (L a 7) * (L b 8) + (L a 8) * (L b 7),
   (L a 8) * (L b 8)]

/-- The coefficients after `mulFix`. -/
private def S3 (a b : Scalar29) : List Z :=
  [(S2 a b)[0]!,
   (S2 a b)[1]!,
   (S2 a b)[2]!,
   (S2 a b)[3]!,
   (S2 a b)[4]!,
   (((S2 a b)[10]!)) - (((S2 a b)[0]!)),
   (((S2 a b)[11]!)) - (((S2 a b)[1]!)),
   (((S2 a b)[12]!)) - (((S2 a b)[2]!)),
   (((S2 a b)[8]!)) - (((S2 a b)[13]!)),
   (((S2 a b)[14]!)) + (((S2 a b)[4]!)),
   (((S2 a b)[15]!)) + (((S2 a b)[10]!)),
   (((S2 a b)[16]!)) + (((S2 a b)[11]!)),
   (S2 a b)[12]!,
   (S2 a b)[13]!,
   (S2 a b)[14]!,
   (S2 a b)[15]!,
   (S2 a b)[16]!]

/-- The coefficients after `mulMidLow`. -/
private def S4 (a b : Scalar29) : List Z :=
  [(S3 a b)[0]!,
   (S3 a b)[1]!,
   (S3 a b)[2]!,
   (S3 a b)[3]!,
   (S3 a b)[4]!,
   ((L a 0 + L a 5) * (L b 0 + L b 5)) + (((S3 a b)[5]!)),
   ((L a 0 + L a 5) * (L b 1 + L b 6) + (L a 1 + L a 6) * (L b 0 + L b 5)) + (((S3 a b)[6]!)),
   ((L a 0 + L a 5) * (L b 2 + L b 7) + (L a 1 + L a 6) * (L b 1 + L b 6) + (L a 2 + L a 7) * (L b
     0 + L b 5)) + (((S3 a b)[7]!)),
   ((L a 0 + L a 5) * (L b 3 + L b 8) + (L a 1 + L a 6) * (L b 2 + L b 7) + (L a 2 + L a 7) * (L b
     1 + L b 6) + (L a 3 + L a 8) * (L b 0 + L b 5)) + (((S3 a b)[8]!)),
   (S3 a b)[9]!,
   (S3 a b)[10]!,
   (S3 a b)[11]!,
   (S3 a b)[12]!,
   (S3 a b)[13]!,
   (S3 a b)[14]!,
   (S3 a b)[15]!,
   (S3 a b)[16]!]

/-- The coefficients after `mulMidHigh` (coefficient 12 still holds `c₇ - c₁₂`). -/
private def S5 (a b : Scalar29) : List Z :=
  [(S4 a b)[0]!,
   (S4 a b)[1]!,
   (S4 a b)[2]!,
   (S4 a b)[3]!,
   (S4 a b)[4]!,
   (S4 a b)[5]!,
   (S4 a b)[6]!,
   (S4 a b)[7]!,
   (S4 a b)[8]!,
   ((L a 0 + L a 5) * (L b 4) + (L a 1 + L a 6) * (L b 3 + L b 8) + (L a 2 + L a 7) * (L b 2 + L b
     7) + (L a 3 + L a 8) * (L b 1 + L b 6) + (L a 4) * (L b 0 + L b 5)) - (((S4 a b)[9]!)),
   ((L a 1 + L a 6) * (L b 4) + (L a 2 + L a 7) * (L b 3 + L b 8) + (L a 3 + L a 8) * (L b 2 + L b
     7) + (L a 4) * (L b 1 + L b 6)) - (((S4 a b)[10]!)),
   ((L a 2 + L a 7) * (L b 4) + (L a 3 + L a 8) * (L b 3 + L b 8) + (L a 4) * (L b 2 + L b 7)) -
     (((S4 a b)[11]!)),
   (S4 a b)[12]!,
   (S4 a b)[13]!,
   (S4 a b)[14]!,
   (S4 a b)[15]!,
   (S4 a b)[16]!]

/-- The first block: coefficients 0 to 8 of the low halves. -/
private theorem mulLow_spec (a b : Scalar29) (ha : a.LimbsLt 29) (hb : b.LimbsLt 29)
    (z : Array U64 17#usize) (hz : ∀ i : ℕ, i < 17 → z[i]!.val = 0) :
    mulLow a b z ⦃ (a0 b0 b1 a1 b2 a2 b3 a3 b4 a4 : U32) (z' : Array U64 17#usize) =>
      a0 = a[0]! ∧ a1 = a[1]! ∧ a2 = a[2]! ∧ a3 = a[3]! ∧ a4 = a[4]! ∧
      b0 = b[0]! ∧ b1 = b[1]! ∧ b2 = b[2]! ∧ b3 = b[3]! ∧ b4 = b[4]! ∧
      ∀ i : ℕ, i < 17 → ((z'[i]!).val : Z) = (S1 a b)[i]! ⦄ := by
  have := ha 0 (by decide); have := ha 1 (by decide); have := ha 2 (by decide)
  have := ha 3 (by decide); have := ha 4 (by decide); have := hb 0 (by decide)
  have := hb 1 (by decide); have := hb 2 (by decide); have := hb 3 (by decide)
  have := hb 4 (by decide)
  unfold mulLow
  step*
  refine ⟨i_post, i5_post, i12_post, i21_post, i32_post, i1_post, i3_post, i8_post, i15_post,
    i24_post, fun k hk => ?_⟩
  interval_cases k <;>
    simp (disch := simp) only [z9_post, z8_post, z7_post, z6_post, z5_post, z4_post, z3_post,
      z2_post, z1_post, i52_post, i51_post, i2_post, i4_post, i6_post, i7_post, i9_post, i10_post,
      i11_post, i13_post, i14_post, i16_post, i17_post, i18_post, i19_post, i20_post, i22_post,
      i23_post, i25_post, i26_post, i27_post, i28_post, i29_post, i30_post, i31_post, i33_post,
      i34_post, i35_post, i36_post, i37_post, i38_post, i39_post, i40_post, i41_post, i42_post,
      i43_post, i44_post, i45_post, i46_post, i47_post, i48_post, i49_post, i50_post, i_post,
      i1_post, i3_post, i5_post, i8_post, i12_post, i15_post, i21_post, i24_post, i32_post, hz, S1,
      Array.getElem!_Nat_set_ne, Array.getElem!_Nat_set_eq, Array.getElem_val_eq_getElem!,
      wrapping_sub_cast, Nat.cast_add, Nat.cast_mul, Nat.cast_zero, L,
      List.getElem!_cons_zero, List.getElem!_cons_succ]

/-- The second block: coefficients 10 to 16 of the high halves. -/
private theorem mulHigh_spec (a b : Scalar29) (ha : a.LimbsLt 29) (hb : b.LimbsLt 29)
    (z : Array U64 17#usize) (hS : ∀ i : ℕ, i < 17 → ((z[i]!).val : Z) = (S1 a b)[i]!) :
    mulHigh a b z ⦃ (a5 b5 b6 a6 b7 a7 b8 a8 : U32) (z' : Array U64 17#usize) =>
      a5 = a[5]! ∧ a6 = a[6]! ∧ a7 = a[7]! ∧ a8 = a[8]! ∧
      b5 = b[5]! ∧ b6 = b[6]! ∧ b7 = b[7]! ∧ b8 = b[8]! ∧
      ∀ i : ℕ, i < 17 → ((z'[i]!).val : Z) = (S2 a b)[i]! ⦄ := by
  have := ha 5 (by decide); have := ha 6 (by decide); have := ha 7 (by decide)
  have := ha 8 (by decide); have := hb 5 (by decide); have := hb 6 (by decide)
  have := hb 7 (by decide); have := hb 8 (by decide)
  unfold mulHigh
  step*
  refine ⟨i54_post, i61_post, i70_post, i80_post, i55_post, i59_post, i66_post, i74_post,
    fun k hk => ?_⟩
  interval_cases k <;>
    simp (disch := simp) only [z16_post, z15_post, z14_post, z13_post, z12_post, z11_post,
      z10_post, i57_post, i64_post, i73_post, i53_post, i58_post, i65_post, i56_post, i60_post,
      i62_post, i63_post, i67_post, i68_post, i69_post, i71_post, i72_post, i75_post, i76_post,
      i77_post, i78_post, i79_post, i81_post, i82_post, i83_post, i84_post, i85_post, i86_post,
      i87_post, i88_post, i89_post, i90_post, i91_post, i54_post, i55_post, i59_post, i61_post,
      i66_post, i70_post, i74_post, i80_post, hS, S2, Array.getElem!_Nat_set_ne,
      Array.getElem!_Nat_set_eq, Array.getElem_val_eq_getElem!, wrapping_sub_cast,
      Nat.cast_add, Nat.cast_mul, L, List.getElem!_cons_zero,
      List.getElem!_cons_succ]

/-- The third block: the wrapping corrections. -/
private theorem mulFix_spec (a b : Scalar29) (z : Array U64 17#usize)
    (hS : ∀ i : ℕ, i < 17 → ((z[i]!).val : Z) = (S2 a b)[i]!) :
    mulFix z ⦃ (z' : Array U64 17#usize) => ∀ i : ℕ, i < 17 →
      ((z'[i]!).val : Z) = (S3 a b)[i]! ⦄ := by
  unfold mulFix
  step*
  interval_cases i <;>
    simp (disch := simp) only [z'_post, z22_post, z21_post, z20_post, z19_post, z18_post,
      z17_post, i94_post, i97_post, i100_post, i103_post, i106_post, i109_post, i112_post,
      i92_post, i93_post, i95_post, i96_post, i98_post, i99_post, i101_post, i102_post, i104_post,
      i105_post, i107_post, i108_post, i110_post, i111_post, hS, S3, Array.getElem!_Nat_set_ne,
      Array.getElem!_Nat_set_eq, Array.getElem_val_eq_getElem!, wrapping_sub_cast,
      wrapping_add_cast, List.getElem!_cons_zero,
      List.getElem!_cons_succ]

/-- Indexing a literal array of four elements. -/
private theorem index_usize_make_four {α : Type} [Inhabited α] (x0 x1 x2 x3 : α) (h) :
    (Array.make 4#usize [x0, x1, x2, x3] h).index_usize 0#usize = ok x0 ∧
    (Array.make 4#usize [x0, x1, x2, x3] h).index_usize 1#usize = ok x1 ∧
    (Array.make 4#usize [x0, x1, x2, x3] h).index_usize 2#usize = ok x2 ∧
    (Array.make 4#usize [x0, x1, x2, x3] h).index_usize 3#usize = ok x3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Array.index_usize_eq _ _ (by decide)] <;> rfl

/-- The fourth block: the sums of the halves and the middle coefficients 5 to 8. -/
private theorem mulMidLow_spec (a b : Scalar29) (ha : a.LimbsLt 29) (hb : b.LimbsLt 29)
    (a0 b0 b1 a1 b2 a2 b3 a3 a5 b5 b6 a6 b7 a7 b8 a8 : U32)
    (ha0 : a0 = a[0]!) (hb0 : b0 = b[0]!) (hb1 : b1 = b[1]!) (ha1 : a1 = a[1]!) (hb2 : b2 = b[2]!)
    (ha2 : a2 = a[2]!) (hb3 : b3 = b[3]!) (ha3 : a3 = a[3]!) (ha5 : a5 = a[5]!) (hb5 : b5 = b[5]!)
    (hb6 : b6 = b[6]!) (ha6 : a6 = a[6]!) (hb7 : b7 = b[7]!) (ha7 : a7 = a[7]!) (hb8 : b8 = b[8]!)
    (ha8 : a8 = a[8]!)
    (z : Array U64 17#usize) (hS : ∀ i : ℕ, i < 17 → ((z[i]!).val : Z) = (S3 a b)[i]!) :
    mulMidLow a0 b0 b1 a1 b2 a2 b3 a3 a5 b5 b6 a6 b7 a7 b8 a8 z ⦃
      (aa0 bb0 bb1 aa1 bb2 aa2 bb3 aa3 : U32) (z' : Array U64 17#usize) =>
      aa0.val = a[0]!.val + a[5]!.val ∧ aa1.val = a[1]!.val + a[6]!.val ∧
      aa2.val = a[2]!.val + a[7]!.val ∧ aa3.val = a[3]!.val + a[8]!.val ∧
      bb0.val = b[0]!.val + b[5]!.val ∧ bb1.val = b[1]!.val + b[6]!.val ∧
      bb2.val = b[2]!.val + b[7]!.val ∧ bb3.val = b[3]!.val + b[8]!.val ∧
      ∀ i : ℕ, i < 17 → ((z'[i]!).val : Z) = (S4 a b)[i]! ⦄ := by
  subst ha0 hb0 hb1 ha1 hb2 ha2 hb3 ha3
  subst ha5 hb5 hb6 ha6 hb7 ha7 hb8 ha8
  have := ha 0 (by decide); have := ha 1 (by decide); have := ha 2 (by decide)
  have := ha 3 (by decide); have := ha 5 (by decide); have := ha 6 (by decide)
  have := ha 7 (by decide); have := ha 8 (by decide); have := hb 0 (by decide)
  have := hb 1 (by decide); have := hb 2 (by decide); have := hb 3 (by decide)
  have := hb 5 (by decide); have := hb 6 (by decide); have := hb 7 (by decide)
  have := hb 8 (by decide)
  unfold mulMidLow
  simp only [index_usize_make_four]
  step*
  refine ⟨by assumption, by assumption, by assumption, by assumption,
    by assumption, by assumption, by assumption, by assumption, fun k hk => ?_⟩
  interval_cases k <;>
    simp (disch := simp) only [z27_post, z26_post, z25_post, z24_post, i125_post, i132_post,
      i141_post, i152_post, i124_post, i131_post, i140_post, i151_post, i113_post, i114_post,
      i115_post, i116_post, i117_post, i118_post, i119_post, i120_post, i123_post, i127_post,
      i129_post, i130_post, i134_post, i135_post, i136_post, i138_post, i139_post, i143_post,
      i144_post, i145_post, i146_post, i147_post, i149_post, i150_post, hS, S4,
      Array.getElem!_Nat_set_ne,
      Array.getElem!_Nat_set_eq, Array.getElem_val_eq_getElem!, 
      wrapping_add_cast, Nat.cast_add, Nat.cast_mul, L, List.getElem!_cons_zero,
      List.getElem!_cons_succ]

/-- The fifth block: the middle coefficients 9 to 11 and the terms of coefficient 12. -/
private theorem mulMidHigh_spec (a b : Scalar29) (ha : a.LimbsLt 29) (hb : b.LimbsLt 29)
    (b4 a4 aa0 bb0 bb1 aa1 bb2 aa2 bb3 aa3 : U32) (hb4 : b4 = b[4]!) (ha4 : a4 = a[4]!)
    (haa0 : aa0.val = a[0]!.val + a[5]!.val) (haa1 : aa1.val = a[1]!.val + a[6]!.val)
    (haa2 : aa2.val = a[2]!.val + a[7]!.val) (haa3 : aa3.val = a[3]!.val + a[8]!.val)
    (hbb0 : bb0.val = b[0]!.val + b[5]!.val) (hbb1 : bb1.val = b[1]!.val + b[6]!.val)
    (hbb2 : bb2.val = b[2]!.val + b[7]!.val) (hbb3 : bb3.val = b[3]!.val + b[8]!.val)
    (z : Array U64 17#usize) (hS : ∀ i : ℕ, i < 17 → ((z[i]!).val : Z) = (S4 a b)[i]!) :
    mulMidHigh b4 a4 aa0 bb0 bb1 aa1 bb2 aa2 bb3 aa3 z ⦃
      (z' : Array U64 17#usize) (x y : U64) =>
      (∀ i : ℕ, i < 17 → ((z'[i]!).val : Z) = (S5 a b)[i]!) ∧
      (x.val : Z) = (L a 3 + L a 8) * L b 4 + L a 4 * (L b 3 + L b 8) ∧ y = z'[12]! ⦄ := by
  have := ha 0 (by decide); have := ha 1 (by decide); have := ha 2 (by decide)
  have := ha 3 (by decide); have := ha 4 (by decide); have := ha 5 (by decide)
  have := ha 6 (by decide); have := ha 7 (by decide); have := ha 8 (by decide)
  have := hb 0 (by decide); have := hb 1 (by decide); have := hb 2 (by decide)
  have := hb 3 (by decide); have := hb 4 (by decide); have := hb 5 (by decide)
  have := hb 6 (by decide); have := hb 7 (by decide); have := hb 8 (by decide)
  subst hb4 ha4
  unfold mulMidHigh
  step*
  refine ⟨fun k hk => ?_, ?_, by rw [i183_post, Array.getElem_val_eq_getElem!]⟩
  · interval_cases k <;>
      simp (disch := simp) only [z30_post, z29_post, z28_post, i163_post, i172_post, i179_post,
        i162_post, i171_post, i178_post, i153_post, i154_post, i155_post, i156_post,
        i157_post, i158_post, i159_post, i160_post, i161_post, i164_post, i165_post, i166_post,
        i167_post, i168_post, i169_post, i170_post, i173_post, i174_post, i175_post, i176_post,
        i177_post, hS, S5, haa0, haa1, haa2, haa3, hbb0,
        hbb1, hbb2, hbb3, Array.getElem!_Nat_set_ne, Array.getElem!_Nat_set_eq,
        Array.getElem_val_eq_getElem!, wrapping_sub_cast, Nat.cast_add,
        Nat.cast_mul, L, List.getElem!_cons_zero, List.getElem!_cons_succ]
  · simp (disch := simp) only [
      
      
      
      i180_post, i181_post, i182_post, haa3, 
      hbb3, 
      Nat.cast_add,
      Nat.cast_mul, L]

/-- The schoolbook coefficients of the product. -/
private def productCoefficients (a b : Scalar29) : List ℕ :=
  [a[0]!.val * b[0]!.val,
   a[0]!.val * b[1]!.val + a[1]!.val * b[0]!.val,
   a[0]!.val * b[2]!.val + a[1]!.val * b[1]!.val + a[2]!.val * b[0]!.val,
   a[0]!.val * b[3]!.val + a[1]!.val * b[2]!.val + a[2]!.val * b[1]!.val + a[3]!.val * b[0]!.val,
   a[0]!.val * b[4]!.val + a[1]!.val * b[3]!.val + a[2]!.val * b[2]!.val +
      a[3]!.val * b[1]!.val + a[4]!.val * b[0]!.val,
   a[0]!.val * b[5]!.val + a[1]!.val * b[4]!.val + a[2]!.val * b[3]!.val +
      a[3]!.val * b[2]!.val + a[4]!.val * b[1]!.val + a[5]!.val * b[0]!.val,
   a[0]!.val * b[6]!.val + a[1]!.val * b[5]!.val + a[2]!.val * b[4]!.val +
      a[3]!.val * b[3]!.val + a[4]!.val * b[2]!.val + a[5]!.val * b[1]!.val +
      a[6]!.val * b[0]!.val,
   a[0]!.val * b[7]!.val + a[1]!.val * b[6]!.val + a[2]!.val * b[5]!.val +
      a[3]!.val * b[4]!.val + a[4]!.val * b[3]!.val + a[5]!.val * b[2]!.val +
      a[6]!.val * b[1]!.val + a[7]!.val * b[0]!.val,
   a[0]!.val * b[8]!.val + a[1]!.val * b[7]!.val + a[2]!.val * b[6]!.val +
      a[3]!.val * b[5]!.val + a[4]!.val * b[4]!.val + a[5]!.val * b[3]!.val +
      a[6]!.val * b[2]!.val + a[7]!.val * b[1]!.val + a[8]!.val * b[0]!.val,
   a[1]!.val * b[8]!.val + a[2]!.val * b[7]!.val + a[3]!.val * b[6]!.val +
      a[4]!.val * b[5]!.val + a[5]!.val * b[4]!.val + a[6]!.val * b[3]!.val +
      a[7]!.val * b[2]!.val + a[8]!.val * b[1]!.val,
   a[2]!.val * b[8]!.val + a[3]!.val * b[7]!.val + a[4]!.val * b[6]!.val +
      a[5]!.val * b[5]!.val + a[6]!.val * b[4]!.val + a[7]!.val * b[3]!.val +
      a[8]!.val * b[2]!.val,
   a[3]!.val * b[8]!.val + a[4]!.val * b[7]!.val + a[5]!.val * b[6]!.val +
      a[6]!.val * b[5]!.val + a[7]!.val * b[4]!.val + a[8]!.val * b[3]!.val,
   a[4]!.val * b[8]!.val + a[5]!.val * b[7]!.val + a[6]!.val * b[6]!.val +
      a[7]!.val * b[5]!.val + a[8]!.val * b[4]!.val,
   a[5]!.val * b[8]!.val + a[6]!.val * b[7]!.val + a[7]!.val * b[6]!.val + a[8]!.val * b[5]!.val,
   a[6]!.val * b[8]!.val + a[7]!.val * b[7]!.val + a[8]!.val * b[6]!.val,
   a[7]!.val * b[8]!.val + a[8]!.val * b[7]!.val,
   a[8]!.val * b[8]!.val]

private theorem productCoefficients_lt (a b : Scalar29) (ha : a.LimbsLt 29) (hb : b.LimbsLt 29) :
    ∀ i : ℕ, i < 17 → (productCoefficients a b)[i]! < 2 ^ 62 := by
  have h (i : ℕ) (hi : i < 9) (j : ℕ) (hj : j < 9) : a[i]!.val * b[j]!.val ≤ 2 ^ 58 :=
    (Nat.mul_le_mul (ha i hi).le (hb j hj).le).trans_eq (by norm_num)
  simp only [Nat.forall_lt_succ_right] at h
  intro i hi
  interval_cases i <;>
    simp only [productCoefficients, List.getElem!_cons_zero, List.getElem!_cons_succ] <;>
    omega

private theorem productCoefficients_value (a b : Scalar29) :
    ∑ i ∈ Finset.range 17, 2 ^ (29 * i) * (productCoefficients a b)[i]! = a.asNat * b.asNat := by
  rw [Scalar29.asNat_def, Scalar29.asNat_def, Array.asNat_eq_sum, Array.asNat_eq_sum]
  simp only [UScalar.ofNatCore_val_eq, pow_mul]
  generalize (2 ^ 29 : ℕ) = B
  simp only [productCoefficients, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    List.getElem!_cons_zero, List.getElem!_cons_succ]
  ring

/-- The Karatsuba coefficients modulo `2^64` are the schoolbook ones. -/
private theorem karatsuba_eq (a b : Scalar29) :
    ∀ i : ℕ, i < 17 → (if i = 12 then
        (L a 3 + L a 8) * L b 4 + L a 4 * (L b 3 + L b 8) - (S5 a b)[12]!
      else (S5 a b)[i]!) = (((productCoefficients a b)[i]! : ℕ) : Z) := by
  intro i hi
  interval_cases i <;>
    simp only [S5, S4, S3, S2, S1, L, productCoefficients, List.getElem!_cons_zero,
      List.getElem!_cons_succ, Nat.cast_add, Nat.cast_mul, Nat.reduceEqDiff, ↓reduceIte] <;>
    ring

private theorem val_eq_of_cast_eq (x : U64) {n : ℕ} (hn : n < 2 ^ 64)
    (h : (x.val : Z) = (n : Z)) : x.val = n := by
  have hx : x.val < 2 ^ 64 := x.hBounds
  have h_mod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hn] at h_mod

/-- **Spec for `backend.serial.u32.scalar.Scalar29.mul_internal`**:
- The result is the product `a * b` in radix `2^29`, with every coefficient below `2^62`. -/
@[step]
theorem mul_internal_spec (a b : Scalar29) (ha : a.LimbsLt 29) (hb : b.LimbsLt 29) :
    mul_internal a b ⦃ (r : Array U64 17#usize) =>
      r.asNat 29 = a.asNat * b.asNat ∧ ∀ i : ℕ, i < 17 → r[i]!.val < 2 ^ 62 ⦄ := by
  rw [mul_internal_eq]
  have hz : ∀ i : ℕ, i < 17 → (Array.repeat 17#usize (0#u64))[i]!.val = 0 := by
    intro i hi
    interval_cases i <;> rfl
  step with mulLow_spec a b ha hb _ hz as ⟨a0, b0, b1, a1, b2, a2, b3, a3, b4, a4, z1,
    ha0, ha1, ha2, ha3, ha4, hb0, hb1, hb2, hb3, hb4, h1⟩
  step with mulHigh_spec a b ha hb z1 h1 as ⟨a5, b5, b6, a6, b7, a7, b8, a8, z2,
    ha5, ha6, ha7, ha8, hb5, hb6, hb7, hb8, h2⟩
  step with mulFix_spec a b z2 h2 as ⟨z3, h3⟩
  step with mulMidLow_spec a b ha hb a0 b0 b1 a1 b2 a2 b3 a3 a5 b5 b6 a6 b7 a7 b8 a8
    ha0 hb0 hb1 ha1 hb2 ha2 hb3 ha3 ha5 hb5 hb6 ha6 hb7 ha7 hb8 ha8 z3 h3 as
    ⟨aa0, bb0, bb1, aa1, bb2, aa2, bb3, aa3, z4, haa0, haa1, haa2, haa3, hbb0, hbb1, hbb2, hbb3,
      h4⟩
  step with mulMidHigh_spec a b ha hb b4 a4 aa0 bb0 bb1 aa1 bb2 aa2 bb3 aa3 hb4 ha4
    haa0 haa1 haa2 haa3 hbb0 hbb1 hbb2 hbb3 z4 h4 as ⟨z5, x, y, h5, hx, hy⟩
  simp only [lift, bind_ok, Array.update_eq z5 12#usize _ (by decide), WP.spec_ok]
  have hr : ∀ i : ℕ, i < 17 → ((z5.set 12#usize (core.num.U64.wrapping_sub x y))[i]!).val =
      (productCoefficients a b)[i]! := by
    intro i hi
    apply val_eq_of_cast_eq _ ((productCoefficients_lt a b ha hb i hi).trans (by decide))
    rw [← karatsuba_eq a b i hi]
    split_ifs with h12
    · subst h12
      rw [Array.getElem!_Nat_set_eq _ _ _ _ (by simp), wrapping_sub_cast, hx, hy,
        h5 12 (by decide)]
    · rw [Array.getElem!_Nat_set_ne _ _ _ _ (by simp; omega), h5 i hi]
  refine ⟨?_, fun i hi => hr i hi ▸ productCoefficients_lt a b ha hb i hi⟩
  rw [Array.asNat_eq_sum, ← productCoefficients_value]
  exact Finset.sum_congr rfl fun i hi => by rw [hr i (Finset.mem_range.mp hi)]

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29
