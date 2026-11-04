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
import Proofs.Backend.Serial.U64.Constants.Ed25519BasepointPoint
import Proofs.Helpers.Iterator
import Proofs.Helpers.Naf
import Proofs.Helpers.StepSpecs
import Proofs.Scalar.NonAdjacentForm
import Proofs.Window.NafLookupTable5From
import Proofs.Window.NafLookupTable5Select
import Proofs.Window.NafLookupTable8Select
import Proofs.Backend.Serial.U64.Constants.AffineOddMultiplesOfBasepoint
import Proofs.Backend.Serial.U32.Constants.Ed25519BasepointPoint
import Proofs.Backend.Serial.U32.Constants.AffineOddMultiplesOfBasepoint
public import Proofs.Helpers.EdwardsOps.Instances
public import Proofs.Backend.Serial.ScalarMul.VartimeDoubleBase.MulGeneric
public section

/-! # `vartime_double_base::mul`

`a • A + b • B` for the basepoint `B`, in variable time: the non-adjacent forms of `a` (width
`5`) and `b` (width `8` with the precomputed table `AFFINE_ODD_MULTIPLES_OF_BASEPOINT` in the
`x86_64-tables` configuration, width `5` with a table built from `ED25519_BASEPOINT_POINT`
otherwise), Horner's rule from the highest nonzero digit down, adding `d • A` and `d • B` for
each nonzero digit from the tables of odd multiples. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.vartime_double_base

section
open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
  (add_spec_point)
open «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
  (sub_spec_point)

namespace «x86_64-tables»

private theorem mul_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) :
    mul.«x86_64-tables_loop0» iter a_naf b_naf i = EdwardsOps.vdbLoop0 iter a_naf b_naf i := by
  unfold mul.«x86_64-tables_loop0» EdwardsOps.vdbLoop0
  congr 1

private theorem mul_loop1_eq (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables»)
    (table_B : window.NafLookupTable8 AffineNielsPoint.«x86_64-tables»)
    (r : ProjectivePoint.«x86_64-tables») :
    mul.«x86_64-tables_loop1» a_naf b_naf i table_A table_B r =
      EdwardsOps.X86Tables.vdbLoop1T a_naf b_naf i table_A table_B r := by
  unfold mul.«x86_64-tables_loop1» EdwardsOps.vdbLoop1T
  congr 1

/-- The first loop of `mul`: the highest index at which a digit of `a` or `b` is nonzero (`0` if
there is none). -/
@[local step]
private theorem mul_loop0_spec (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) (hstart : iter.iter.start.val = 0)
    (hend : iter.iter.end.val ≤ 256) (hi : i.val < 256)
    (hz : ∀ k, iter.iter.end.val ≤ k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0) :
    mul.«x86_64-tables_loop0» iter a_naf b_naf i ⦃ (r : Usize) =>
      r.val < 256 ∧ ∀ k, r.val < k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0 ⦄ := by
  rw [mul_loop0_eq]
  exact EdwardsOps.vdbLoop0_spec iter a_naf b_naf i hstart hend hi hz

/-- The second loop of `mul`: after the digits `i, …, 255`, the accumulator represents
`nafTail a i • A + nafTail b i • B`. -/
@[local step]
private theorem mul_loop1_spec (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables»)
    (table_B : window.NafLookupTable8 AffineNielsPoint.«x86_64-tables»)
    (r : ProjectivePoint.«x86_64-tables») (A B : curve25519.edwards.Point)
    (hA : table_A.Represents A) (hAb : table_A.LimbsLt 54)
    (hB : table_B.Represents B) (hBb : table_B.LimbsLt 54)
    (ha : ∀ k : ℕ, k < 256 → a_naf[k]!.val ≠ 0 → a_naf[k]!.val % 2 = 1 ∧
      2 * |a_naf[k]!.val| < 2 ^ 5)
    (hb : ∀ k : ℕ, k < 256 → b_naf[k]!.val ≠ 0 → b_naf[k]!.val % 2 = 1 ∧
      2 * |b_naf[k]!.val| < 2 ^ 8)
    (hi : i.val < 256) (hr : r.OnCurve) (hrb : r.LimbsLt 52)
    (hrp : r.toPoint = nafTail a_naf (i.val + 1) • A + nafTail b_naf (i.val + 1) • B) :
    mul.«x86_64-tables_loop1» a_naf b_naf i table_A table_B r
      ⦃ (res : edwards.EdwardsPoint.«x86_64-tables») => res.OnCurve ∧
        res.toPoint = nafTail a_naf 0 • A + nafTail b_naf 0 • B ∧ res.LimbsLt 52 ⦄ := by
  rw [mul_loop1_eq]
  exact EdwardsOps.X86Tables.vdbLoop1T_spec
    EdwardsOps.X86Tables.addN_spec EdwardsOps.X86Tables.subN_spec EdwardsOps.X86Tables.addA_spec
    EdwardsOps.X86Tables.subA_spec EdwardsOps.X86Tables.asExtended_spec
    EdwardsOps.X86Tables.pDouble_spec EdwardsOps.X86Tables.cAsProjective_spec
    EdwardsOps.X86Tables.pAsExtended_spec a_naf b_naf i table_A table_B r A B hA hAb hB hBb ha hb hi
    hr hrb hrp

open window.«NafLookupTable5ProjectiveNielsPointx86_64-tables».Insts in
open scoped Helpers.IndexStep in
/-- `vartime_double_base::mul`: `a • A + b • B` for the basepoint `B` (unreduced scalars
`< 2^255`, the precondition of `non_adjacent_form`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (a : scalar.Scalar) (A : edwards.EdwardsPoint.«x86_64-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 52) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    mul.«x86_64-tables» a A b ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul.«x86_64-tables»
  step as ⟨a_naf, haval, hadig, hanaf⟩
  step as ⟨b_naf, hbval, hbdig, hbnaf⟩
  step as ⟨iter, hiter⟩
  step with mul_loop0_spec iter a_naf b_naf 255#usize (by rw [hiter]; rfl) (by rw [hiter]; decide)
    (by decide) (fun k hk hk' => absurd hk' (by rw [hiter] at hk; simp at hk; omega))
    as ⟨i, hi, hz⟩
  step with «CoreConvertFromSharedAEdwardsPointx86_64-tables».from_spec
    as ⟨tA, htA, htAb⟩
  step as ⟨tB, htB, htBb⟩
  step with ProjectivePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨r, hron, hrp, hrb⟩
  have hr' : r.toPoint = nafTail a_naf (i.val + 1) • A.toPoint +
      nafTail b_naf (i.val + 1) • basepoint := by
    rw [hrp, nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2, zero_smul, zero_smul, add_zero]
  step with mul_loop1_spec a_naf b_naf i tA tB r A.toPoint basepoint htA htAb htB htBb
    (fun k hk h => hadig k hk h) (fun k hk h => hbdig k hk h) hi hron hrb hr'
    as ⟨res, hreson, hresp, hresb⟩
  refine ⟨hreson, ?_, hresb⟩
  rw [hresp, nafTail_zero, nafTail_zero, haval, hbval, natCast_zsmul, natCast_zsmul]

end «x86_64-tables»

end

section
open «Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-tablesCompletedPointi686-tables»
  (add_spec_point)
open «CoreOpsArithSubSharedAProjectiveNielsPointi686-tablesCompletedPointi686-tables»
  (sub_spec_point)

namespace «i686-tables»

private theorem mul_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) :
    mul.«i686-tables_loop0» iter a_naf b_naf i = EdwardsOps.vdbLoop0 iter a_naf b_naf i := by
  unfold mul.«i686-tables_loop0» EdwardsOps.vdbLoop0
  congr 1

private theorem mul_loop1_eq (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 ProjectiveNielsPoint.«i686-tables»)
    (table_B : window.NafLookupTable8 AffineNielsPoint.«i686-tables»)
    (r : ProjectivePoint.«i686-tables») :
    mul.«i686-tables_loop1» a_naf b_naf i table_A table_B r =
      EdwardsOps.I686Tables.vdbLoop1T a_naf b_naf i table_A table_B r := by
  unfold mul.«i686-tables_loop1» EdwardsOps.vdbLoop1T
  congr 1

/-- The first loop of `mul`: the highest index at which a digit of `a` or `b` is nonzero (`0` if
there is none). -/
@[local step]
private theorem mul_loop0_spec (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) (hstart : iter.iter.start.val = 0)
    (hend : iter.iter.end.val ≤ 256) (hi : i.val < 256)
    (hz : ∀ k, iter.iter.end.val ≤ k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0) :
    mul.«i686-tables_loop0» iter a_naf b_naf i ⦃ (r : Usize) =>
      r.val < 256 ∧ ∀ k, r.val < k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0 ⦄ := by
  rw [mul_loop0_eq]
  exact EdwardsOps.vdbLoop0_spec iter a_naf b_naf i hstart hend hi hz

/-- The second loop of `mul`: after the digits `i, …, 255`, the accumulator represents
`nafTail a i • A + nafTail b i • B`. -/
@[local step]
private theorem mul_loop1_spec (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 ProjectiveNielsPoint.«i686-tables»)
    (table_B : window.NafLookupTable8 AffineNielsPoint.«i686-tables»)
    (r : ProjectivePoint.«i686-tables») (A B : curve25519.edwards.Point)
    (hA : table_A.Represents A) (hAb : table_A.LimbsLt 27)
    (hB : table_B.Represents B) (hBb : table_B.LimbsLt 27)
    (ha : ∀ k : ℕ, k < 256 → a_naf[k]!.val ≠ 0 → a_naf[k]!.val % 2 = 1 ∧
      2 * |a_naf[k]!.val| < 2 ^ 5)
    (hb : ∀ k : ℕ, k < 256 → b_naf[k]!.val ≠ 0 → b_naf[k]!.val % 2 = 1 ∧
      2 * |b_naf[k]!.val| < 2 ^ 8)
    (hi : i.val < 256) (hr : r.OnCurve) (hrb : r.LimbsLt 26)
    (hrp : r.toPoint = nafTail a_naf (i.val + 1) • A + nafTail b_naf (i.val + 1) • B) :
    mul.«i686-tables_loop1» a_naf b_naf i table_A table_B r
      ⦃ (res : edwards.EdwardsPoint.«i686-tables») => res.OnCurve ∧
        res.toPoint = nafTail a_naf 0 • A + nafTail b_naf 0 • B ∧ res.LimbsLt 26 ⦄ := by
  rw [mul_loop1_eq]
  exact EdwardsOps.I686Tables.vdbLoop1T_spec
    EdwardsOps.I686Tables.addN_spec EdwardsOps.I686Tables.subN_spec EdwardsOps.I686Tables.addA_spec
    EdwardsOps.I686Tables.subA_spec EdwardsOps.I686Tables.asExtended_spec
    EdwardsOps.I686Tables.pDouble_spec EdwardsOps.I686Tables.cAsProjective_spec
    EdwardsOps.I686Tables.pAsExtended_spec a_naf b_naf i table_A table_B r A B hA hAb hB hBb ha hb
    hi hr hrb hrp

open window.«NafLookupTable5ProjectiveNielsPointi686-tables».Insts in
open scoped Helpers.IndexStep in
/-- `vartime_double_base::mul`: `a • A + b • B` for the basepoint `B` (unreduced scalars
`< 2^255`, the precondition of `non_adjacent_form`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (a : scalar.Scalar) (A : edwards.EdwardsPoint.«i686-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 26) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    mul.«i686-tables» a A b ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul.«i686-tables»
  step as ⟨a_naf, haval, hadig, hanaf⟩
  step as ⟨b_naf, hbval, hbdig, hbnaf⟩
  step as ⟨iter, hiter⟩
  step with mul_loop0_spec iter a_naf b_naf 255#usize (by rw [hiter]; rfl) (by rw [hiter]; decide)
    (by decide) (fun k hk hk' => absurd hk' (by rw [hiter] at hk; simp at hk; omega))
    as ⟨i, hi, hz⟩
  step with «CoreConvertFromSharedAEdwardsPointi686-tables».from_spec
    as ⟨tA, htA, htAb⟩
  step as ⟨tB, htB, htBb⟩
  step with ProjectivePoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨r, hron, hrp, hrb⟩
  have hr' : r.toPoint = nafTail a_naf (i.val + 1) • A.toPoint +
      nafTail b_naf (i.val + 1) • basepoint := by
    rw [hrp, nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2, zero_smul, zero_smul, add_zero]
  step with mul_loop1_spec a_naf b_naf i tA tB r A.toPoint basepoint htA htAb htB htBb
    (fun k hk h => hadig k hk h) (fun k hk h => hbdig k hk h) hi hron hrb hr'
    as ⟨res, hreson, hresp, hresb⟩
  refine ⟨hreson, ?_, hresb⟩
  rw [hresp, nafTail_zero, nafTail_zero, haval, hbval, natCast_zsmul, natCast_zsmul]

end «i686-tables»

end

section
open «Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
  (add_spec_point)
open «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
  (sub_spec_point)

namespace «x86_64-no-tables»

private theorem mul_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) :
    mul.«x86_64-no-tables_loop0» iter a_naf b_naf i = EdwardsOps.vdbLoop0 iter a_naf b_naf i := by
  unfold mul.«x86_64-no-tables_loop0» EdwardsOps.vdbLoop0
  congr 1

private theorem mul_loop1_eq (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»)
    (table_B : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»)
    (r : ProjectivePoint.«x86_64-no-tables») :
    mul.«x86_64-no-tables_loop1» a_naf b_naf i table_A table_B r =
      EdwardsOps.X86NoTables.vdbLoop1N a_naf b_naf i table_A table_B r := by
  unfold mul.«x86_64-no-tables_loop1» EdwardsOps.vdbLoop1N
  congr 1

/-- The first loop of `mul`: the highest index at which a digit of `a` or `b` is nonzero (`0` if
there is none). -/
@[local step]
private theorem mul_loop0_spec (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) (hstart : iter.iter.start.val = 0)
    (hend : iter.iter.end.val ≤ 256) (hi : i.val < 256)
    (hz : ∀ k, iter.iter.end.val ≤ k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0) :
    mul.«x86_64-no-tables_loop0» iter a_naf b_naf i ⦃ (r : Usize) =>
      r.val < 256 ∧ ∀ k, r.val < k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0 ⦄ := by
  rw [mul_loop0_eq]
  exact EdwardsOps.vdbLoop0_spec iter a_naf b_naf i hstart hend hi hz

/-- The second loop of `mul`: after the digits `i, …, 255`, the accumulator represents
`nafTail a i • A + nafTail b i • B`. -/
@[local step]
private theorem mul_loop1_spec (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A table_B : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables»)
    (r : ProjectivePoint.«x86_64-no-tables») (A B : curve25519.edwards.Point)
    (hA : table_A.Represents A) (hAb : table_A.LimbsLt 54)
    (hB : table_B.Represents B) (hBb : table_B.LimbsLt 54)
    (ha : ∀ k : ℕ, k < 256 → a_naf[k]!.val ≠ 0 → a_naf[k]!.val % 2 = 1 ∧
      2 * |a_naf[k]!.val| < 2 ^ 5)
    (hb : ∀ k : ℕ, k < 256 → b_naf[k]!.val ≠ 0 → b_naf[k]!.val % 2 = 1 ∧
      2 * |b_naf[k]!.val| < 2 ^ 5)
    (hi : i.val < 256) (hr : r.OnCurve) (hrb : r.LimbsLt 52)
    (hrp : r.toPoint = nafTail a_naf (i.val + 1) • A + nafTail b_naf (i.val + 1) • B) :
    mul.«x86_64-no-tables_loop1» a_naf b_naf i table_A table_B r
      ⦃ (res : edwards.EdwardsPoint.«x86_64-no-tables») => res.OnCurve ∧
        res.toPoint = nafTail a_naf 0 • A + nafTail b_naf 0 • B ∧ res.LimbsLt 52 ⦄ := by
  rw [mul_loop1_eq]
  exact EdwardsOps.X86NoTables.vdbLoop1N_spec
    EdwardsOps.X86NoTables.addN_spec EdwardsOps.X86NoTables.subN_spec
    EdwardsOps.X86NoTables.asExtended_spec EdwardsOps.X86NoTables.pDouble_spec
    EdwardsOps.X86NoTables.cAsProjective_spec EdwardsOps.X86NoTables.pAsExtended_spec a_naf b_naf i
    table_A table_B r A B hA hAb hB hBb ha hb hi hr hrb hrp

open window.«NafLookupTable5ProjectiveNielsPointx86_64-no-tables».Insts in
open scoped Helpers.IndexStep in
/-- `vartime_double_base::mul`: `a • A + b • B` for the basepoint `B` (unreduced scalars
`< 2^255`, the precondition of `non_adjacent_form`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (a : scalar.Scalar) (A : edwards.EdwardsPoint.«x86_64-no-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 52) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    mul.«x86_64-no-tables» a A b ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul.«x86_64-no-tables»
  step as ⟨a_naf, haval, hadig, hanaf⟩
  step as ⟨b_naf, hbval, hbdig, hbnaf⟩
  step as ⟨iter, hiter⟩
  step with mul_loop0_spec iter a_naf b_naf 255#usize (by rw [hiter]; rfl) (by rw [hiter]; decide)
    (by decide) (fun k hk hk' => absurd hk' (by rw [hiter] at hk; simp at hk; omega))
    as ⟨i, hi, hz⟩
  step with «CoreConvertFromSharedAEdwardsPointx86_64-no-tables».from_spec
    as ⟨tA, htA, htAb⟩
  step with backend.serial.u64.constants.«x86_64-no-tables».ED25519_BASEPOINT_POINT_spec_point
    as ⟨bp, hbpon, hbp, hbpb⟩
  step with «CoreConvertFromSharedAEdwardsPointx86_64-no-tables».from_spec
    as ⟨tB, htB, htBb⟩
  step with
      ProjectivePoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨r, hron, hrp, hrb⟩
  have hr' : r.toPoint = nafTail a_naf (i.val + 1) • A.toPoint +
      nafTail b_naf (i.val + 1) • bp.toPoint := by
    rw [hrp, nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2, zero_smul, zero_smul, add_zero]
  step with mul_loop1_spec a_naf b_naf i tA tB r A.toPoint bp.toPoint htA htAb htB htBb
    (fun k hk h => hadig k hk h) (fun k hk h => hbdig k hk h) hi hron hrb hr'
    as ⟨res, hreson, hresp, hresb⟩
  refine ⟨hreson, ?_, hresb⟩
  rw [hresp, nafTail_zero, nafTail_zero, haval, hbval, hbp, natCast_zsmul, natCast_zsmul]

end «x86_64-no-tables»

end

section
open «Shared0EdwardsPointi686-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»
  (add_spec_point)
open «CoreOpsArithSubSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»
  (sub_spec_point)

namespace «i686-no-tables»

private theorem mul_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) :
    mul.«i686-no-tables_loop0» iter a_naf b_naf i = EdwardsOps.vdbLoop0 iter a_naf b_naf i := by
  unfold mul.«i686-no-tables_loop0» EdwardsOps.vdbLoop0
  congr 1

private theorem mul_loop1_eq (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»)
    (table_B : window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»)
    (r : ProjectivePoint.«i686-no-tables») :
    mul.«i686-no-tables_loop1» a_naf b_naf i table_A table_B r =
      EdwardsOps.I686NoTables.vdbLoop1N a_naf b_naf i table_A table_B r := by
  unfold mul.«i686-no-tables_loop1» EdwardsOps.vdbLoop1N
  congr 1

/-- The first loop of `mul`: the highest index at which a digit of `a` or `b` is nonzero (`0` if
there is none). -/
@[local step]
private theorem mul_loop0_spec (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) (hstart : iter.iter.start.val = 0)
    (hend : iter.iter.end.val ≤ 256) (hi : i.val < 256)
    (hz : ∀ k, iter.iter.end.val ≤ k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0) :
    mul.«i686-no-tables_loop0» iter a_naf b_naf i ⦃ (r : Usize) =>
      r.val < 256 ∧ ∀ k, r.val < k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0 ⦄ := by
  rw [mul_loop0_eq]
  exact EdwardsOps.vdbLoop0_spec iter a_naf b_naf i hstart hend hi hz

/-- The second loop of `mul`: after the digits `i, …, 255`, the accumulator represents
`nafTail a i • A + nafTail b i • B`. -/
@[local step]
private theorem mul_loop1_spec (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A table_B : window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»)
    (r : ProjectivePoint.«i686-no-tables») (A B : curve25519.edwards.Point)
    (hA : table_A.Represents A) (hAb : table_A.LimbsLt 27)
    (hB : table_B.Represents B) (hBb : table_B.LimbsLt 27)
    (ha : ∀ k : ℕ, k < 256 → a_naf[k]!.val ≠ 0 → a_naf[k]!.val % 2 = 1 ∧
      2 * |a_naf[k]!.val| < 2 ^ 5)
    (hb : ∀ k : ℕ, k < 256 → b_naf[k]!.val ≠ 0 → b_naf[k]!.val % 2 = 1 ∧
      2 * |b_naf[k]!.val| < 2 ^ 5)
    (hi : i.val < 256) (hr : r.OnCurve) (hrb : r.LimbsLt 26)
    (hrp : r.toPoint = nafTail a_naf (i.val + 1) • A + nafTail b_naf (i.val + 1) • B) :
    mul.«i686-no-tables_loop1» a_naf b_naf i table_A table_B r
      ⦃ (res : edwards.EdwardsPoint.«i686-no-tables») => res.OnCurve ∧
        res.toPoint = nafTail a_naf 0 • A + nafTail b_naf 0 • B ∧ res.LimbsLt 26 ⦄ := by
  rw [mul_loop1_eq]
  exact EdwardsOps.I686NoTables.vdbLoop1N_spec
    EdwardsOps.I686NoTables.addN_spec EdwardsOps.I686NoTables.subN_spec
    EdwardsOps.I686NoTables.asExtended_spec EdwardsOps.I686NoTables.pDouble_spec
    EdwardsOps.I686NoTables.cAsProjective_spec EdwardsOps.I686NoTables.pAsExtended_spec a_naf b_naf
    i table_A table_B r A B hA hAb hB hBb ha hb hi hr hrb hrp

open window.«NafLookupTable5ProjectiveNielsPointi686-no-tables».Insts in
open scoped Helpers.IndexStep in
/-- `vartime_double_base::mul`: `a • A + b • B` for the basepoint `B` (unreduced scalars
`< 2^255`, the precondition of `non_adjacent_form`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (a : scalar.Scalar) (A : edwards.EdwardsPoint.«i686-no-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 26) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    mul.«i686-no-tables» a A b ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul.«i686-no-tables»
  step as ⟨a_naf, haval, hadig, hanaf⟩
  step as ⟨b_naf, hbval, hbdig, hbnaf⟩
  step as ⟨iter, hiter⟩
  step with mul_loop0_spec iter a_naf b_naf 255#usize (by rw [hiter]; rfl) (by rw [hiter]; decide)
    (by decide) (fun k hk hk' => absurd hk' (by rw [hiter] at hk; simp at hk; omega))
    as ⟨i, hi, hz⟩
  step with «CoreConvertFromSharedAEdwardsPointi686-no-tables».from_spec
    as ⟨tA, htA, htAb⟩
  step with backend.serial.u32.constants.«i686-no-tables».ED25519_BASEPOINT_POINT_spec_point
    as ⟨bp, hbpon, hbp, hbpb⟩
  step with «CoreConvertFromSharedAEdwardsPointi686-no-tables».from_spec
    as ⟨tB, htB, htBb⟩
  step with
      ProjectivePoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨r, hron, hrp, hrb⟩
  have hr' : r.toPoint = nafTail a_naf (i.val + 1) • A.toPoint +
      nafTail b_naf (i.val + 1) • bp.toPoint := by
    rw [hrp, nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2, zero_smul, zero_smul, add_zero]
  step with mul_loop1_spec a_naf b_naf i tA tB r A.toPoint bp.toPoint htA htAb htB htBb
    (fun k hk h => hadig k hk h) (fun k hk h => hbdig k hk h) hi hron hrb hr'
    as ⟨res, hreson, hresp, hresb⟩
  refine ⟨hreson, ?_, hresb⟩
  rw [hresp, nafTail_zero, nafTail_zero, haval, hbval, hbp, natCast_zsmul, natCast_zsmul]

end «i686-no-tables»

end
end Curve25519Dalek.backend.serial.scalar_mul.vartime_double_base
