/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
import Proofs.Backend.Serial.CurveModels.AddAffineNiels
import Proofs.Backend.Serial.CurveModels.AddProjectiveNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.CurveModels.CompletedAsProjective
import Proofs.Backend.Serial.CurveModels.ProjectiveAsExtended
import Proofs.Backend.Serial.CurveModels.ProjectiveDouble
import Proofs.Backend.Serial.CurveModels.ProjectiveIdentity
import Proofs.Backend.Serial.CurveModels.SubAffineNiels
import Proofs.Backend.Serial.CurveModels.SubProjectiveNiels
import Proofs.Backend.Serial.U64.Constants.AffineOddMultiplesOfBasepoint
import Proofs.Backend.Serial.U64.Constants.AffineOddMultiplesOfBasepoint128
import Proofs.Backend.Serial.U64.Constants.Ed25519Basepoint128Point
import Proofs.Backend.Serial.U64.Constants.Ed25519BasepointPoint
import Proofs.Helpers.Iterator
import Proofs.Helpers.Naf
import Proofs.Helpers.StepSpecs
import Proofs.Scalar.HalfWidthNonAdjacentForm
import Proofs.Scalar.SplitAt128
import Proofs.Window.NafLookupTable5From
import Proofs.Window.NafLookupTable5Select
import Proofs.Window.NafLookupTable8Select
import Proofs.Backend.Serial.U32.Constants.AffineOddMultiplesOfBasepoint
import Proofs.Backend.Serial.U32.Constants.AffineOddMultiplesOfBasepoint128
import Proofs.Backend.Serial.U32.Constants.Ed25519Basepoint128Point
import Proofs.Backend.Serial.U32.Constants.Ed25519BasepointPoint
public import Proofs.Helpers.EdwardsOps.Instances
public import Proofs.Backend.Serial.ScalarMul.VartimeTripleBase.Mul128128256Generic
public section

/-! # `vartime_triple_base::mul_128_128_256`

`a₁ • A₁ + a₂ • A₂ + b • B` for the basepoint `B`, in variable time, for `a₁, a₂ < 2^128`: `b` is
split as `b_lo + 2^128 b_hi`, the four `128`-bit scalars are recoded as width-`5` non-adjacent
forms, whose digits above index `128` vanish (`naf5_digits_eq_zero_of_lt`), and Horner's rule runs
from the highest nonzero digit (at most `HEEA_MAX_INDEX = 129`) down, adding `d • A₁`, `d • A₂`,
`d • B` and `d • 2^128 B` for each nonzero digit `d` from tables of odd multiples. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.vartime_triple_base

section
open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
  renaming add → add_pn, add_spec_point → add_pn_spec_point
open «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
  renaming sub → sub_pn, sub_spec_point → sub_pn_spec_point
open «CoreOpsArithAddSharedAAffineNielsPointx86_64-tablesCompletedPointx86_64-tables»
  renaming add → add_an, add_spec_point → add_an_spec_point
open «CoreOpsArithSubSharedAAffineNielsPointx86_64-tablesCompletedPointx86_64-tables»
  renaming sub → sub_an, sub_spec_point → sub_an_spec_point
open window.«NafLookupTable5ProjectiveNielsPointx86_64-tables».Insts
open «CoreConvertFromSharedAEdwardsPointx86_64-tables» renaming from_spec → naf5_from_spec
open ProjectivePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity

namespace «x86_64-tables»

private theorem loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.RangeInclusive Usize))
    (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize) :
    mul_128_128_256.«x86_64-tables_loop0» iter a₁ a₂ c₁ c₂ i =
      EdwardsOps.vtbLoop0 iter a₁ a₂ c₁ c₂ i := by
  unfold mul_128_128_256.«x86_64-tables_loop0» EdwardsOps.vtbLoop0
  congr 1

private theorem loop1_eq (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize)
    (table_A1 table_A2 : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables»)
    (table_B : window.NafLookupTable8 AffineNielsPoint.«x86_64-tables»)
    (table_B_128 : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables»)
    (r : ProjectivePoint.«x86_64-tables») :
    mul_128_128_256.«x86_64-tables_loop1» a₁ a₂ c₁ c₂ i table_A1 table_A2 table_B table_B_128 r =
      EdwardsOps.X86Tables.vtbLoop1T a₁ a₂ c₁ c₂ i table_A1 table_A2 table_B table_B_128 r := by
  unfold mul_128_128_256.«x86_64-tables_loop1» EdwardsOps.vtbLoop1T
  congr 1

open scoped Helpers.IndexStep in
/-- The first loop of `mul_128_128_256`, over `HEEA_MAX_INDEX, …, 0`: the highest index `≤ 129` at
which a digit of one of the four recodings is nonzero (`0` if there is none), given that all
digits above the iterator's range vanish. -/
@[local step]
private theorem loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.RangeInclusive Usize))
    (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize) (hstart : iter.iter.start.val = 0)
    (hend : iter.iter.end.val ≤ 129) (hex : iter.iter.exhausted = false) (hi : i.val ≤ 129)
    (hz : ∀ k, iter.iter.end.val < k → k < 256 → DigitsZero a₁ a₂ c₁ c₂ k) :
    mul_128_128_256.«x86_64-tables_loop0» iter a₁ a₂ c₁ c₂ i ⦃ (r : Usize) =>
      r.val ≤ 129 ∧ ∀ k, r.val < k → k < 256 → DigitsZero a₁ a₂ c₁ c₂ k ⦄ := by
  rw [loop0_eq]
  exact EdwardsOps.vtbLoop0_spec iter a₁ a₂ c₁ c₂ i hstart hend hex hi hz

/-- The digit facts of `non_adjacent_form` at width `5`. -/
private abbrev Naf5Digits (d : Array I8 256#usize) : Prop :=
  ∀ k : ℕ, k < 256 → d[k]!.val ≠ 0 → d[k]!.val % 2 = 1 ∧ 2 * |d[k]!.val| < 2 ^ 5

open scoped Helpers.IndexStep in
/-- The second loop of `mul_128_128_256`: after the digits `i, …, 255`, the accumulator represents
`∑ nafTail dₖ i • Pₖ` over the four recodings and points. -/
@[local step]
private theorem loop1_spec (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize)
    (table_A1 table_A2 : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables»)
    (table_B : window.NafLookupTable8 AffineNielsPoint.«x86_64-tables»)
    (table_B_128 : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables»)
    (r : ProjectivePoint.«x86_64-tables») (P₁ P₂ P₃ P₄ : curve25519.edwards.Point)
    (h₁ : table_A1.Represents P₁) (h₁b : table_A1.LimbsLt 54)
    (h₂ : table_A2.Represents P₂) (h₂b : table_A2.LimbsLt 54)
    (h₃ : table_B.Represents P₃) (h₃b : table_B.LimbsLt 54)
    (h₄ : table_B_128.Represents P₄) (h₄b : table_B_128.LimbsLt 54)
    (ha₁ : Naf5Digits a₁) (ha₂ : Naf5Digits a₂) (hc₁ : Naf5Digits c₁) (hc₂ : Naf5Digits c₂)
    (hi : i.val < 256) (hr : r.OnCurve) (hrb : r.LimbsLt 52)
    (hrp : r.toPoint = nafTail a₁ (i.val + 1) • P₁ + nafTail a₂ (i.val + 1) • P₂ +
      nafTail c₁ (i.val + 1) • P₃ + nafTail c₂ (i.val + 1) • P₄) :
    mul_128_128_256.«x86_64-tables_loop1» a₁ a₂ c₁ c₂ i table_A1 table_A2 table_B table_B_128 r
      ⦃ (res : edwards.EdwardsPoint.«x86_64-tables») => res.OnCurve ∧
        res.toPoint =
          nafTail a₁ 0 • P₁ + nafTail a₂ 0 • P₂ + nafTail c₁ 0 • P₃ + nafTail c₂ 0 • P₄ ∧
        res.LimbsLt 52 ⦄ := by
  rw [loop1_eq]
  exact EdwardsOps.X86Tables.vtbLoop1T_spec
    EdwardsOps.X86Tables.addN_spec EdwardsOps.X86Tables.subN_spec EdwardsOps.X86Tables.addA_spec
    EdwardsOps.X86Tables.subA_spec EdwardsOps.X86Tables.asExtended_spec
    EdwardsOps.X86Tables.pDouble_spec EdwardsOps.X86Tables.cAsProjective_spec
    EdwardsOps.X86Tables.pAsExtended_spec a₁ a₂ c₁ c₂ i table_A1 table_A2 table_B table_B_128 r P₁
    P₂ P₃ P₄ h₁ h₁b h₂ h₂b h₃ h₃b h₄ h₄b ha₁ ha₂ hc₁ hc₂ hi hr hrb hrp

open scoped Helpers.IndexStep in
/-- `vartime_triple_base::mul_128_128_256`: `a1 • A1 + a2 • A2 + b • B` for the basepoint `B`
(`a1, a2 < 2^128`, `b` unrestricted); limbs `< 2^52`. -/
@[step]
theorem mul_128_128_256_spec (a1 : scalar.HalfWidthScalar)
    (A1 : edwards.EdwardsPoint.«x86_64-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : edwards.EdwardsPoint.«x86_64-tables») (b : scalar.Scalar)
    (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 52) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 52) (hA2_on : A2.OnCurve) :
    mul_128_128_256.«x86_64-tables» a1 A1 a2 A2 b
        ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧
        r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.LimbsLt 52 ⦄ := by
  unfold mul_128_128_256.«x86_64-tables»
  have h255 : ∀ x : ℕ, x < 2 ^ 128 → x < 2 ^ 255 := fun x hx => lt_trans hx (by norm_num)
  step as ⟨b_lo, b_hi, hsplit, hlo, hhi⟩
  step with scalar.HalfWidthScalar.non_adjacent_form_spec a1 5#usize ⟨by decide, by decide⟩
    (h255 _ ha1) as ⟨n1, hv1, hd1, hn1⟩
  step with scalar.HalfWidthScalar.non_adjacent_form_spec a2 5#usize ⟨by decide, by decide⟩
    (h255 _ ha2) as ⟨n2, hv2, hd2, hn2⟩
  step with scalar.HalfWidthScalar.non_adjacent_form_spec b_lo 5#usize ⟨by decide, by decide⟩
    (h255 _ hlo) as ⟨n3, hv3, hd3, hn3⟩
  step with scalar.HalfWidthScalar.non_adjacent_form_spec b_hi 5#usize ⟨by decide, by decide⟩
    (h255 _ hhi) as ⟨n4, hv4, hd4, hn4⟩
  step as ⟨ri, hri_start, hri_end, hri_ex⟩
  step as ⟨iter, hiter⟩
  have hmax : scalar.HEEA_MAX_INDEX = 129#usize := by unfold scalar.HEEA_MAX_INDEX; rfl
  rw [hmax] at hri_end ⊢
  step with loop0_spec iter n1 n2 n3 n4 129#usize (by rw [hiter, hri_start]; rfl)
    (by rw [hiter, hri_end]; decide) (by rw [hiter, hri_ex]) (by decide)
    (fun k hk hk' => by
      rw [hiter, hri_end] at hk
      exact ⟨naf_high_zero ha1 hv1 hd1 hn1 k hk hk', naf_high_zero ha2 hv2 hd2 hn2 k hk hk',
        naf_high_zero hlo hv3 hd3 hn3 k hk hk', naf_high_zero hhi hv4 hd4 hn4 k hk hk'⟩)
    as ⟨i, hi, hz⟩
  step with naf5_from_spec A1 hA1 hA1_on as ⟨tA1, htA1, htA1b⟩
  step with naf5_from_spec A2 hA2 hA2_on as ⟨tA2, htA2, htA2b⟩
  step with backend.serial.u64.constants.AFFINE_ODD_MULTIPLES_OF_BASEPOINT_spec as ⟨tB, htB, htBb⟩
  step with backend.serial.u64.constants.AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128_spec
    as ⟨tB', htB', htB'b⟩
  step with identity_spec_point as ⟨r, hron, hrp, hrb⟩
  have hr' : r.toPoint = nafTail n1 (i.val + 1) • A1.toPoint + nafTail n2 (i.val + 1) • A2.toPoint +
      nafTail n3 (i.val + 1) • basepoint + nafTail n4 (i.val + 1) • (2 ^ 128 • basepoint) := by
    rw [hrp, nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2.1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2.2.1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2.2.2]
    simp only [zero_smul, add_zero]
  step with loop1_spec n1 n2 n3 n4 i tA1 tA2 tB tB' r A1.toPoint A2.toPoint basepoint
      (2 ^ 128 • basepoint) htA1 htA1b htA2 htA2b htB htBb htB' htB'b hd1 hd2 hd3 hd4
      (by omega) hron hrb hr'
    as ⟨res, hreson, hresp, hresb⟩
  refine ⟨hreson, ?_, hresb⟩
  rw [hresp, nafTail_zero, nafTail_zero, nafTail_zero, nafTail_zero, hv1, hv2, hv3, hv4,
    natCast_zsmul, natCast_zsmul, natCast_zsmul, natCast_zsmul, add_assoc,
    split_smul _ _ _ hsplit]

end «x86_64-tables»

end

section
open «Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-tablesCompletedPointi686-tables»
  renaming add → add_pn, add_spec_point → add_pn_spec_point
open «CoreOpsArithSubSharedAProjectiveNielsPointi686-tablesCompletedPointi686-tables»
  renaming sub → sub_pn, sub_spec_point → sub_pn_spec_point
open «CoreOpsArithAddSharedAAffineNielsPointi686-tablesCompletedPointi686-tables»
  renaming add → add_an, add_spec_point → add_an_spec_point
open «CoreOpsArithSubSharedAAffineNielsPointi686-tablesCompletedPointi686-tables»
  renaming sub → sub_an, sub_spec_point → sub_an_spec_point
open window.«NafLookupTable5ProjectiveNielsPointi686-tables».Insts
open «CoreConvertFromSharedAEdwardsPointi686-tables» renaming from_spec → naf5_from_spec
open ProjectivePoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity

namespace «i686-tables»

private theorem loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.RangeInclusive Usize))
    (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize) :
    mul_128_128_256.«i686-tables_loop0» iter a₁ a₂ c₁ c₂ i =
      EdwardsOps.vtbLoop0 iter a₁ a₂ c₁ c₂ i := by
  unfold mul_128_128_256.«i686-tables_loop0» EdwardsOps.vtbLoop0
  congr 1

private theorem loop1_eq (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize)
    (table_A1 table_A2 : window.NafLookupTable5 ProjectiveNielsPoint.«i686-tables»)
    (table_B : window.NafLookupTable8 AffineNielsPoint.«i686-tables»)
    (table_B_128 : window.NafLookupTable5 ProjectiveNielsPoint.«i686-tables»)
    (r : ProjectivePoint.«i686-tables») :
    mul_128_128_256.«i686-tables_loop1» a₁ a₂ c₁ c₂ i table_A1 table_A2 table_B table_B_128 r =
      EdwardsOps.I686Tables.vtbLoop1T a₁ a₂ c₁ c₂ i table_A1 table_A2 table_B table_B_128 r := by
  unfold mul_128_128_256.«i686-tables_loop1» EdwardsOps.vtbLoop1T
  congr 1

open scoped Helpers.IndexStep in
/-- The first loop of `mul_128_128_256`, over `HEEA_MAX_INDEX, …, 0`: the highest index `≤ 129` at
which a digit of one of the four recodings is nonzero (`0` if there is none), given that all
digits above the iterator's range vanish. -/
@[local step]
private theorem loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.RangeInclusive Usize))
    (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize) (hstart : iter.iter.start.val = 0)
    (hend : iter.iter.end.val ≤ 129) (hex : iter.iter.exhausted = false) (hi : i.val ≤ 129)
    (hz : ∀ k, iter.iter.end.val < k → k < 256 → DigitsZero a₁ a₂ c₁ c₂ k) :
    mul_128_128_256.«i686-tables_loop0» iter a₁ a₂ c₁ c₂ i ⦃ (r : Usize) =>
      r.val ≤ 129 ∧ ∀ k, r.val < k → k < 256 → DigitsZero a₁ a₂ c₁ c₂ k ⦄ := by
  rw [loop0_eq]
  exact EdwardsOps.vtbLoop0_spec iter a₁ a₂ c₁ c₂ i hstart hend hex hi hz

/-- The digit facts of `non_adjacent_form` at width `5`. -/
private abbrev Naf5Digits (d : Array I8 256#usize) : Prop :=
  ∀ k : ℕ, k < 256 → d[k]!.val ≠ 0 → d[k]!.val % 2 = 1 ∧ 2 * |d[k]!.val| < 2 ^ 5

open scoped Helpers.IndexStep in
/-- The second loop of `mul_128_128_256`: after the digits `i, …, 255`, the accumulator represents
`∑ nafTail dₖ i • Pₖ` over the four recodings and points. -/
@[local step]
private theorem loop1_spec (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize)
    (table_A1 table_A2 : window.NafLookupTable5 ProjectiveNielsPoint.«i686-tables»)
    (table_B : window.NafLookupTable8 AffineNielsPoint.«i686-tables»)
    (table_B_128 : window.NafLookupTable5 ProjectiveNielsPoint.«i686-tables»)
    (r : ProjectivePoint.«i686-tables») (P₁ P₂ P₃ P₄ : curve25519.edwards.Point)
    (h₁ : table_A1.Represents P₁) (h₁b : table_A1.LimbsLt 27)
    (h₂ : table_A2.Represents P₂) (h₂b : table_A2.LimbsLt 27)
    (h₃ : table_B.Represents P₃) (h₃b : table_B.LimbsLt 27)
    (h₄ : table_B_128.Represents P₄) (h₄b : table_B_128.LimbsLt 27)
    (ha₁ : Naf5Digits a₁) (ha₂ : Naf5Digits a₂) (hc₁ : Naf5Digits c₁) (hc₂ : Naf5Digits c₂)
    (hi : i.val < 256) (hr : r.OnCurve) (hrb : r.LimbsLt 26)
    (hrp : r.toPoint = nafTail a₁ (i.val + 1) • P₁ + nafTail a₂ (i.val + 1) • P₂ +
      nafTail c₁ (i.val + 1) • P₃ + nafTail c₂ (i.val + 1) • P₄) :
    mul_128_128_256.«i686-tables_loop1» a₁ a₂ c₁ c₂ i table_A1 table_A2 table_B table_B_128 r
      ⦃ (res : edwards.EdwardsPoint.«i686-tables») => res.OnCurve ∧
        res.toPoint =
          nafTail a₁ 0 • P₁ + nafTail a₂ 0 • P₂ + nafTail c₁ 0 • P₃ + nafTail c₂ 0 • P₄ ∧
        res.LimbsLt 26 ⦄ := by
  rw [loop1_eq]
  exact EdwardsOps.I686Tables.vtbLoop1T_spec
    EdwardsOps.I686Tables.addN_spec EdwardsOps.I686Tables.subN_spec EdwardsOps.I686Tables.addA_spec
    EdwardsOps.I686Tables.subA_spec EdwardsOps.I686Tables.asExtended_spec
    EdwardsOps.I686Tables.pDouble_spec EdwardsOps.I686Tables.cAsProjective_spec
    EdwardsOps.I686Tables.pAsExtended_spec a₁ a₂ c₁ c₂ i table_A1 table_A2 table_B table_B_128 r P₁
    P₂ P₃ P₄ h₁ h₁b h₂ h₂b h₃ h₃b h₄ h₄b ha₁ ha₂ hc₁ hc₂ hi hr hrb hrp

open scoped Helpers.IndexStep in
/-- `vartime_triple_base::mul_128_128_256`: `a1 • A1 + a2 • A2 + b • B` for the basepoint `B`
(`a1, a2 < 2^128`, `b` unrestricted); limbs `< 2^26`. -/
@[step]
theorem mul_128_128_256_spec (a1 : scalar.HalfWidthScalar)
    (A1 : edwards.EdwardsPoint.«i686-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : edwards.EdwardsPoint.«i686-tables») (b : scalar.Scalar)
    (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 26) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 26) (hA2_on : A2.OnCurve) :
    mul_128_128_256.«i686-tables» a1 A1 a2 A2 b
        ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧
        r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.LimbsLt 26 ⦄ := by
  unfold mul_128_128_256.«i686-tables»
  have h255 : ∀ x : ℕ, x < 2 ^ 128 → x < 2 ^ 255 := fun x hx => lt_trans hx (by norm_num)
  step as ⟨b_lo, b_hi, hsplit, hlo, hhi⟩
  step with scalar.HalfWidthScalar.non_adjacent_form_spec a1 5#usize ⟨by decide, by decide⟩
    (h255 _ ha1) as ⟨n1, hv1, hd1, hn1⟩
  step with scalar.HalfWidthScalar.non_adjacent_form_spec a2 5#usize ⟨by decide, by decide⟩
    (h255 _ ha2) as ⟨n2, hv2, hd2, hn2⟩
  step with scalar.HalfWidthScalar.non_adjacent_form_spec b_lo 5#usize ⟨by decide, by decide⟩
    (h255 _ hlo) as ⟨n3, hv3, hd3, hn3⟩
  step with scalar.HalfWidthScalar.non_adjacent_form_spec b_hi 5#usize ⟨by decide, by decide⟩
    (h255 _ hhi) as ⟨n4, hv4, hd4, hn4⟩
  step as ⟨ri, hri_start, hri_end, hri_ex⟩
  step as ⟨iter, hiter⟩
  have hmax : scalar.HEEA_MAX_INDEX = 129#usize := by unfold scalar.HEEA_MAX_INDEX; rfl
  rw [hmax] at hri_end ⊢
  step with loop0_spec iter n1 n2 n3 n4 129#usize (by rw [hiter, hri_start]; rfl)
    (by rw [hiter, hri_end]; decide) (by rw [hiter, hri_ex]) (by decide)
    (fun k hk hk' => by
      rw [hiter, hri_end] at hk
      exact ⟨naf_high_zero ha1 hv1 hd1 hn1 k hk hk', naf_high_zero ha2 hv2 hd2 hn2 k hk hk',
        naf_high_zero hlo hv3 hd3 hn3 k hk hk', naf_high_zero hhi hv4 hd4 hn4 k hk hk'⟩)
    as ⟨i, hi, hz⟩
  step with naf5_from_spec A1 hA1 hA1_on as ⟨tA1, htA1, htA1b⟩
  step with naf5_from_spec A2 hA2 hA2_on as ⟨tA2, htA2, htA2b⟩
  step with backend.serial.u32.constants.AFFINE_ODD_MULTIPLES_OF_BASEPOINT_spec as ⟨tB, htB, htBb⟩
  step with backend.serial.u32.constants.AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128_spec
    as ⟨tB', htB', htB'b⟩
  step with identity_spec_point as ⟨r, hron, hrp, hrb⟩
  have hr' : r.toPoint = nafTail n1 (i.val + 1) • A1.toPoint + nafTail n2 (i.val + 1) • A2.toPoint +
      nafTail n3 (i.val + 1) • basepoint + nafTail n4 (i.val + 1) • (2 ^ 128 • basepoint) := by
    rw [hrp, nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2.1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2.2.1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2.2.2]
    simp only [zero_smul, add_zero]
  step with loop1_spec n1 n2 n3 n4 i tA1 tA2 tB tB' r A1.toPoint A2.toPoint basepoint
      (2 ^ 128 • basepoint) htA1 htA1b htA2 htA2b htB htBb htB' htB'b hd1 hd2 hd3 hd4
      (by omega) hron hrb hr'
    as ⟨res, hreson, hresp, hresb⟩
  refine ⟨hreson, ?_, hresb⟩
  rw [hresp, nafTail_zero, nafTail_zero, nafTail_zero, nafTail_zero, hv1, hv2, hv3, hv4,
    natCast_zsmul, natCast_zsmul, natCast_zsmul, natCast_zsmul, add_assoc,
    split_smul _ _ _ hsplit]

end «i686-tables»

end

section
open «Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
  renaming add → add_pn, add_spec_point → add_pn_spec_point
open «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
  renaming sub → sub_pn, sub_spec_point → sub_pn_spec_point
open window.«NafLookupTable5ProjectiveNielsPointx86_64-no-tables».Insts
open «CoreConvertFromSharedAEdwardsPointx86_64-no-tables» renaming from_spec → naf5_from_spec
open ProjectivePoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity

namespace «x86_64-no-tables»

private theorem loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.RangeInclusive Usize))
    (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize) :
    mul_128_128_256.«x86_64-no-tables_loop0» iter a₁ a₂ c₁ c₂ i =
      EdwardsOps.vtbLoop0 iter a₁ a₂ c₁ c₂ i := by
  unfold mul_128_128_256.«x86_64-no-tables_loop0» EdwardsOps.vtbLoop0
  congr 1

private theorem loop1_eq (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize)
    (table_A1 table_A2 : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»)
    (table_B : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»)
    (table_B_128 : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»)
    (r : ProjectivePoint.«x86_64-no-tables») :
    mul_128_128_256.«x86_64-no-tables_loop1» a₁ a₂ c₁ c₂ i table_A1 table_A2 table_B table_B_128 r =
      EdwardsOps.X86NoTables.vtbLoop1N a₁ a₂ c₁ c₂ i table_A1 table_A2 table_B table_B_128 r := by
  unfold mul_128_128_256.«x86_64-no-tables_loop1» EdwardsOps.vtbLoop1N
  congr 1

open scoped Helpers.IndexStep in
/-- The first loop of `mul_128_128_256`, over `HEEA_MAX_INDEX, …, 0`: the highest index `≤ 129` at
which a digit of one of the four recodings is nonzero (`0` if there is none), given that all
digits above the iterator's range vanish. -/
@[local step]
private theorem loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.RangeInclusive Usize))
    (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize) (hstart : iter.iter.start.val = 0)
    (hend : iter.iter.end.val ≤ 129) (hex : iter.iter.exhausted = false) (hi : i.val ≤ 129)
    (hz : ∀ k, iter.iter.end.val < k → k < 256 → DigitsZero a₁ a₂ c₁ c₂ k) :
    mul_128_128_256.«x86_64-no-tables_loop0» iter a₁ a₂ c₁ c₂ i ⦃ (r : Usize) =>
      r.val ≤ 129 ∧ ∀ k, r.val < k → k < 256 → DigitsZero a₁ a₂ c₁ c₂ k ⦄ := by
  rw [loop0_eq]
  exact EdwardsOps.vtbLoop0_spec iter a₁ a₂ c₁ c₂ i hstart hend hex hi hz

/-- The digit facts of `non_adjacent_form` at width `5`. -/
private abbrev Naf5Digits (d : Array I8 256#usize) : Prop :=
  ∀ k : ℕ, k < 256 → d[k]!.val ≠ 0 → d[k]!.val % 2 = 1 ∧ 2 * |d[k]!.val| < 2 ^ 5

open scoped Helpers.IndexStep in
/-- The second loop of `mul_128_128_256`: after the digits `i, …, 255`, the accumulator represents
`∑ nafTail dₖ i • Pₖ` over the four recodings and points. -/
@[local step]
private theorem loop1_spec (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize)
    (table_A1 table_A2 : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»)
    (table_B : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»)
    (table_B_128 : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»)
    (r : ProjectivePoint.«x86_64-no-tables») (P₁ P₂ P₃ P₄ : curve25519.edwards.Point)
    (h₁ : table_A1.Represents P₁) (h₁b : table_A1.LimbsLt 54)
    (h₂ : table_A2.Represents P₂) (h₂b : table_A2.LimbsLt 54)
    (h₃ : table_B.Represents P₃) (h₃b : table_B.LimbsLt 54)
    (h₄ : table_B_128.Represents P₄) (h₄b : table_B_128.LimbsLt 54)
    (ha₁ : Naf5Digits a₁) (ha₂ : Naf5Digits a₂) (hc₁ : Naf5Digits c₁) (hc₂ : Naf5Digits c₂)
    (hi : i.val < 256) (hr : r.OnCurve) (hrb : r.LimbsLt 52)
    (hrp : r.toPoint = nafTail a₁ (i.val + 1) • P₁ + nafTail a₂ (i.val + 1) • P₂ +
      nafTail c₁ (i.val + 1) • P₃ + nafTail c₂ (i.val + 1) • P₄) :
    mul_128_128_256.«x86_64-no-tables_loop1» a₁ a₂ c₁ c₂ i table_A1 table_A2 table_B table_B_128 r
      ⦃ (res : edwards.EdwardsPoint.«x86_64-no-tables») => res.OnCurve ∧
        res.toPoint =
          nafTail a₁ 0 • P₁ + nafTail a₂ 0 • P₂ + nafTail c₁ 0 • P₃ + nafTail c₂ 0 • P₄ ∧
        res.LimbsLt 52 ⦄ := by
  rw [loop1_eq]
  exact EdwardsOps.X86NoTables.vtbLoop1N_spec
    EdwardsOps.X86NoTables.addN_spec EdwardsOps.X86NoTables.subN_spec
    EdwardsOps.X86NoTables.asExtended_spec EdwardsOps.X86NoTables.pDouble_spec
    EdwardsOps.X86NoTables.cAsProjective_spec EdwardsOps.X86NoTables.pAsExtended_spec a₁ a₂ c₁ c₂ i
    table_A1 table_A2 table_B table_B_128 r P₁ P₂ P₃ P₄ h₁ h₁b h₂ h₂b h₃ h₃b h₄ h₄b ha₁ ha₂ hc₁ hc₂
    hi hr hrb hrp

open scoped Helpers.IndexStep in
/-- `vartime_triple_base::mul_128_128_256`: `a1 • A1 + a2 • A2 + b • B` for the basepoint `B`
(`a1, a2 < 2^128`, `b` unrestricted); limbs `< 2^52`. -/
@[step]
theorem mul_128_128_256_spec (a1 : scalar.HalfWidthScalar)
    (A1 : edwards.EdwardsPoint.«x86_64-no-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : edwards.EdwardsPoint.«x86_64-no-tables») (b : scalar.Scalar)
    (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 52) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 52) (hA2_on : A2.OnCurve) :
    mul_128_128_256.«x86_64-no-tables» a1 A1 a2 A2 b
        ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧
        r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.LimbsLt 52 ⦄ := by
  unfold mul_128_128_256.«x86_64-no-tables»
  have h255 : ∀ x : ℕ, x < 2 ^ 128 → x < 2 ^ 255 := fun x hx => lt_trans hx (by norm_num)
  step as ⟨b_lo, b_hi, hsplit, hlo, hhi⟩
  step with scalar.HalfWidthScalar.non_adjacent_form_spec a1 5#usize ⟨by decide, by decide⟩
    (h255 _ ha1) as ⟨n1, hv1, hd1, hn1⟩
  step with scalar.HalfWidthScalar.non_adjacent_form_spec a2 5#usize ⟨by decide, by decide⟩
    (h255 _ ha2) as ⟨n2, hv2, hd2, hn2⟩
  step with scalar.HalfWidthScalar.non_adjacent_form_spec b_lo 5#usize ⟨by decide, by decide⟩
    (h255 _ hlo) as ⟨n3, hv3, hd3, hn3⟩
  step with scalar.HalfWidthScalar.non_adjacent_form_spec b_hi 5#usize ⟨by decide, by decide⟩
    (h255 _ hhi) as ⟨n4, hv4, hd4, hn4⟩
  step as ⟨ri, hri_start, hri_end, hri_ex⟩
  step as ⟨iter, hiter⟩
  have hmax : scalar.HEEA_MAX_INDEX = 129#usize := by unfold scalar.HEEA_MAX_INDEX; rfl
  rw [hmax] at hri_end ⊢
  step with loop0_spec iter n1 n2 n3 n4 129#usize (by rw [hiter, hri_start]; rfl)
    (by rw [hiter, hri_end]; decide) (by rw [hiter, hri_ex]) (by decide)
    (fun k hk hk' => by
      rw [hiter, hri_end] at hk
      exact ⟨naf_high_zero ha1 hv1 hd1 hn1 k hk hk', naf_high_zero ha2 hv2 hd2 hn2 k hk hk',
        naf_high_zero hlo hv3 hd3 hn3 k hk hk', naf_high_zero hhi hv4 hd4 hn4 k hk hk'⟩)
    as ⟨i, hi, hz⟩
  step with naf5_from_spec A1 hA1 hA1_on as ⟨tA1, htA1, htA1b⟩
  step with naf5_from_spec A2 hA2 hA2_on as ⟨tA2, htA2, htA2b⟩
  step with backend.serial.u64.constants.«x86_64-no-tables».ED25519_BASEPOINT_POINT_spec_point
    as ⟨bp, hbp_on, hbp, hbpb⟩
  step with naf5_from_spec bp hbpb hbp_on as ⟨tB, htB, htBb⟩
  step with backend.serial.u64.constants.«x86_64-no-tables».ED25519_BASEPOINT_128_POINT_spec
    as ⟨bp', hbp'_on, hbp', hbp'b⟩
  step with naf5_from_spec bp' hbp'b hbp'_on as ⟨tB', htB', htB'b⟩
  rw [hbp] at htB
  rw [hbp'] at htB'
  step with identity_spec_point as ⟨r, hron, hrp, hrb⟩
  have hr' : r.toPoint = nafTail n1 (i.val + 1) • A1.toPoint + nafTail n2 (i.val + 1) • A2.toPoint +
      nafTail n3 (i.val + 1) • basepoint + nafTail n4 (i.val + 1) • (2 ^ 128 • basepoint) := by
    rw [hrp, nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2.1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2.2.1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2.2.2]
    simp only [zero_smul, add_zero]
  step with loop1_spec n1 n2 n3 n4 i tA1 tA2 tB tB' r A1.toPoint A2.toPoint basepoint
      (2 ^ 128 • basepoint) htA1 htA1b htA2 htA2b htB htBb htB' htB'b hd1 hd2 hd3 hd4
      (by omega) hron hrb hr'
    as ⟨res, hreson, hresp, hresb⟩
  refine ⟨hreson, ?_, hresb⟩
  rw [hresp, nafTail_zero, nafTail_zero, nafTail_zero, nafTail_zero, hv1, hv2, hv3, hv4,
    natCast_zsmul, natCast_zsmul, natCast_zsmul, natCast_zsmul, add_assoc,
    split_smul _ _ _ hsplit]

end «x86_64-no-tables»

end

section
open «Shared0EdwardsPointi686-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»
  renaming add → add_pn, add_spec_point → add_pn_spec_point
open «CoreOpsArithSubSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»
  renaming sub → sub_pn, sub_spec_point → sub_pn_spec_point
open window.«NafLookupTable5ProjectiveNielsPointi686-no-tables».Insts
open «CoreConvertFromSharedAEdwardsPointi686-no-tables» renaming from_spec → naf5_from_spec
open ProjectivePoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity

namespace «i686-no-tables»

private theorem loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.RangeInclusive Usize))
    (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize) :
    mul_128_128_256.«i686-no-tables_loop0» iter a₁ a₂ c₁ c₂ i =
      EdwardsOps.vtbLoop0 iter a₁ a₂ c₁ c₂ i := by
  unfold mul_128_128_256.«i686-no-tables_loop0» EdwardsOps.vtbLoop0
  congr 1

private theorem loop1_eq (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize)
    (table_A1 table_A2 : window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»)
    (table_B : window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»)
    (table_B_128 : window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»)
    (r : ProjectivePoint.«i686-no-tables») :
    mul_128_128_256.«i686-no-tables_loop1» a₁ a₂ c₁ c₂ i table_A1 table_A2 table_B table_B_128 r =
      EdwardsOps.I686NoTables.vtbLoop1N a₁ a₂ c₁ c₂ i table_A1 table_A2 table_B table_B_128 r := by
  unfold mul_128_128_256.«i686-no-tables_loop1» EdwardsOps.vtbLoop1N
  congr 1

open scoped Helpers.IndexStep in
/-- The first loop of `mul_128_128_256`, over `HEEA_MAX_INDEX, …, 0`: the highest index `≤ 129` at
which a digit of one of the four recodings is nonzero (`0` if there is none), given that all
digits above the iterator's range vanish. -/
@[local step]
private theorem loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.RangeInclusive Usize))
    (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize) (hstart : iter.iter.start.val = 0)
    (hend : iter.iter.end.val ≤ 129) (hex : iter.iter.exhausted = false) (hi : i.val ≤ 129)
    (hz : ∀ k, iter.iter.end.val < k → k < 256 → DigitsZero a₁ a₂ c₁ c₂ k) :
    mul_128_128_256.«i686-no-tables_loop0» iter a₁ a₂ c₁ c₂ i ⦃ (r : Usize) =>
      r.val ≤ 129 ∧ ∀ k, r.val < k → k < 256 → DigitsZero a₁ a₂ c₁ c₂ k ⦄ := by
  rw [loop0_eq]
  exact EdwardsOps.vtbLoop0_spec iter a₁ a₂ c₁ c₂ i hstart hend hex hi hz

/-- The digit facts of `non_adjacent_form` at width `5`. -/
private abbrev Naf5Digits (d : Array I8 256#usize) : Prop :=
  ∀ k : ℕ, k < 256 → d[k]!.val ≠ 0 → d[k]!.val % 2 = 1 ∧ 2 * |d[k]!.val| < 2 ^ 5

open scoped Helpers.IndexStep in
/-- The second loop of `mul_128_128_256`: after the digits `i, …, 255`, the accumulator represents
`∑ nafTail dₖ i • Pₖ` over the four recodings and points. -/
@[local step]
private theorem loop1_spec (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize)
    (table_A1 table_A2 : window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»)
    (table_B : window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»)
    (table_B_128 : window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»)
    (r : ProjectivePoint.«i686-no-tables») (P₁ P₂ P₃ P₄ : curve25519.edwards.Point)
    (h₁ : table_A1.Represents P₁) (h₁b : table_A1.LimbsLt 27)
    (h₂ : table_A2.Represents P₂) (h₂b : table_A2.LimbsLt 27)
    (h₃ : table_B.Represents P₃) (h₃b : table_B.LimbsLt 27)
    (h₄ : table_B_128.Represents P₄) (h₄b : table_B_128.LimbsLt 27)
    (ha₁ : Naf5Digits a₁) (ha₂ : Naf5Digits a₂) (hc₁ : Naf5Digits c₁) (hc₂ : Naf5Digits c₂)
    (hi : i.val < 256) (hr : r.OnCurve) (hrb : r.LimbsLt 26)
    (hrp : r.toPoint = nafTail a₁ (i.val + 1) • P₁ + nafTail a₂ (i.val + 1) • P₂ +
      nafTail c₁ (i.val + 1) • P₃ + nafTail c₂ (i.val + 1) • P₄) :
    mul_128_128_256.«i686-no-tables_loop1» a₁ a₂ c₁ c₂ i table_A1 table_A2 table_B table_B_128 r
      ⦃ (res : edwards.EdwardsPoint.«i686-no-tables») => res.OnCurve ∧
        res.toPoint =
          nafTail a₁ 0 • P₁ + nafTail a₂ 0 • P₂ + nafTail c₁ 0 • P₃ + nafTail c₂ 0 • P₄ ∧
        res.LimbsLt 26 ⦄ := by
  rw [loop1_eq]
  exact EdwardsOps.I686NoTables.vtbLoop1N_spec
    EdwardsOps.I686NoTables.addN_spec EdwardsOps.I686NoTables.subN_spec
    EdwardsOps.I686NoTables.asExtended_spec EdwardsOps.I686NoTables.pDouble_spec
    EdwardsOps.I686NoTables.cAsProjective_spec EdwardsOps.I686NoTables.pAsExtended_spec a₁ a₂ c₁ c₂
    i table_A1 table_A2 table_B table_B_128 r P₁ P₂ P₃ P₄ h₁ h₁b h₂ h₂b h₃ h₃b h₄ h₄b ha₁ ha₂ hc₁
    hc₂ hi hr hrb hrp

open scoped Helpers.IndexStep in
/-- `vartime_triple_base::mul_128_128_256`: `a1 • A1 + a2 • A2 + b • B` for the basepoint `B`
(`a1, a2 < 2^128`, `b` unrestricted); limbs `< 2^26`. -/
@[step]
theorem mul_128_128_256_spec (a1 : scalar.HalfWidthScalar)
    (A1 : edwards.EdwardsPoint.«i686-no-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : edwards.EdwardsPoint.«i686-no-tables») (b : scalar.Scalar)
    (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 26) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 26) (hA2_on : A2.OnCurve) :
    mul_128_128_256.«i686-no-tables» a1 A1 a2 A2 b
        ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧
        r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.LimbsLt 26 ⦄ := by
  unfold mul_128_128_256.«i686-no-tables»
  have h255 : ∀ x : ℕ, x < 2 ^ 128 → x < 2 ^ 255 := fun x hx => lt_trans hx (by norm_num)
  step as ⟨b_lo, b_hi, hsplit, hlo, hhi⟩
  step with scalar.HalfWidthScalar.non_adjacent_form_spec a1 5#usize ⟨by decide, by decide⟩
    (h255 _ ha1) as ⟨n1, hv1, hd1, hn1⟩
  step with scalar.HalfWidthScalar.non_adjacent_form_spec a2 5#usize ⟨by decide, by decide⟩
    (h255 _ ha2) as ⟨n2, hv2, hd2, hn2⟩
  step with scalar.HalfWidthScalar.non_adjacent_form_spec b_lo 5#usize ⟨by decide, by decide⟩
    (h255 _ hlo) as ⟨n3, hv3, hd3, hn3⟩
  step with scalar.HalfWidthScalar.non_adjacent_form_spec b_hi 5#usize ⟨by decide, by decide⟩
    (h255 _ hhi) as ⟨n4, hv4, hd4, hn4⟩
  step as ⟨ri, hri_start, hri_end, hri_ex⟩
  step as ⟨iter, hiter⟩
  have hmax : scalar.HEEA_MAX_INDEX = 129#usize := by unfold scalar.HEEA_MAX_INDEX; rfl
  rw [hmax] at hri_end ⊢
  step with loop0_spec iter n1 n2 n3 n4 129#usize (by rw [hiter, hri_start]; rfl)
    (by rw [hiter, hri_end]; decide) (by rw [hiter, hri_ex]) (by decide)
    (fun k hk hk' => by
      rw [hiter, hri_end] at hk
      exact ⟨naf_high_zero ha1 hv1 hd1 hn1 k hk hk', naf_high_zero ha2 hv2 hd2 hn2 k hk hk',
        naf_high_zero hlo hv3 hd3 hn3 k hk hk', naf_high_zero hhi hv4 hd4 hn4 k hk hk'⟩)
    as ⟨i, hi, hz⟩
  step with naf5_from_spec A1 hA1 hA1_on as ⟨tA1, htA1, htA1b⟩
  step with naf5_from_spec A2 hA2 hA2_on as ⟨tA2, htA2, htA2b⟩
  step with backend.serial.u32.constants.«i686-no-tables».ED25519_BASEPOINT_POINT_spec_point
    as ⟨bp, hbp_on, hbp, hbpb⟩
  step with naf5_from_spec bp hbpb hbp_on as ⟨tB, htB, htBb⟩
  step with backend.serial.u32.constants.«i686-no-tables».ED25519_BASEPOINT_128_POINT_spec
    as ⟨bp', hbp'_on, hbp', hbp'b⟩
  step with naf5_from_spec bp' hbp'b hbp'_on as ⟨tB', htB', htB'b⟩
  rw [hbp] at htB
  rw [hbp'] at htB'
  step with identity_spec_point as ⟨r, hron, hrp, hrb⟩
  have hr' : r.toPoint = nafTail n1 (i.val + 1) • A1.toPoint + nafTail n2 (i.val + 1) • A2.toPoint +
      nafTail n3 (i.val + 1) • basepoint + nafTail n4 (i.val + 1) • (2 ^ 128 • basepoint) := by
    rw [hrp, nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2.1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2.2.1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2.2.2]
    simp only [zero_smul, add_zero]
  step with loop1_spec n1 n2 n3 n4 i tA1 tA2 tB tB' r A1.toPoint A2.toPoint basepoint
      (2 ^ 128 • basepoint) htA1 htA1b htA2 htA2b htB htBb htB' htB'b hd1 hd2 hd3 hd4
      (by omega) hron hrb hr'
    as ⟨res, hreson, hresp, hresb⟩
  refine ⟨hreson, ?_, hresb⟩
  rw [hresp, nafTail_zero, nafTail_zero, nafTail_zero, nafTail_zero, hv1, hv2, hv3, hv4,
    natCast_zsmul, natCast_zsmul, natCast_zsmul, natCast_zsmul, add_assoc,
    split_smul _ _ _ hsplit]

end «i686-no-tables»

end

end Curve25519Dalek.backend.serial.scalar_mul.vartime_triple_base
