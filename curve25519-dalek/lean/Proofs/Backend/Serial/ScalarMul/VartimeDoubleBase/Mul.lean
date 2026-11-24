module
public import Proofs.Helpers.Represents
public import Proofs.Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
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
`64bit-tables` configuration, width `5` with a table built from `ED25519_BASEPOINT_POINT`
otherwise), Horner's rule from the highest nonzero digit down, adding `d • A` and `d • B` for
each nonzero digit from the tables of odd multiples. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.vartime_double_base

section
open «Shared0EdwardsPoint64bit-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint64bit-tablesCompletedPoint64bit-tables»
  (add_spec)
open «CoreOpsArithSubSharedAProjectiveNielsPoint64bit-tablesCompletedPoint64bit-tables»
  (sub_spec)

namespace «64bit-tables»

private theorem mul_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) :
    mul.«64bit-tables_loop0» iter a_naf b_naf i = EdwardsOps.vdbLoop0 iter a_naf b_naf i := by
  unfold mul.«64bit-tables_loop0» EdwardsOps.vdbLoop0
  congr 1

private theorem mul_loop1_eq (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 ProjectiveNielsPoint.«64bit-tables»)
    (table_B : window.NafLookupTable8 AffineNielsPoint.«64bit-tables»)
    (r : ProjectivePoint.«64bit-tables») :
    mul.«64bit-tables_loop1» a_naf b_naf i table_A table_B r =
      EdwardsOps.Bits64Tables.vdbLoop1T a_naf b_naf i table_A table_B r := by
  unfold mul.«64bit-tables_loop1» EdwardsOps.vdbLoop1T
  congr 1

/-- The first loop of `mul`: the highest index at which a digit of `a` or `b` is nonzero (`0` if
there is none). -/
@[local step]
private theorem mul_loop0_spec (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) (hstart : iter.iter.start.val = 0)
    (hend : iter.iter.end.val ≤ 256) (hi : i.val < 256)
    (hz : ∀ k, iter.iter.end.val ≤ k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0) :
    mul.«64bit-tables_loop0» iter a_naf b_naf i ⦃ (r : Usize) =>
      r.val < 256 ∧ ∀ k, r.val < k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0 ⦄ := by
  rw [mul_loop0_eq]
  exact EdwardsOps.vdbLoop0_spec iter a_naf b_naf i hstart hend hi hz

/-- The second loop of `mul`: after the digits `i, …, 255`, the accumulator represents
`nafTail a i • A + nafTail b i • B`. -/
@[local step]
private theorem mul_loop1_spec (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 ProjectiveNielsPoint.«64bit-tables»)
    (table_B : window.NafLookupTable8 AffineNielsPoint.«64bit-tables»)
    (r : ProjectivePoint.«64bit-tables») (A B : curve25519.edwards.Point)
    (hA : table_A.Represents A) (hAb : table_A.LimbsLt 54)
    (hB : table_B.Represents B) (hBb : table_B.LimbsLt 54)
    (ha : ∀ k : ℕ, k < 256 → a_naf[k]!.val ≠ 0 → a_naf[k]!.val % 2 = 1 ∧
      2 * |a_naf[k]!.val| < 2 ^ 5)
    (hb : ∀ k : ℕ, k < 256 → b_naf[k]!.val ≠ 0 → b_naf[k]!.val % 2 = 1 ∧
      2 * |b_naf[k]!.val| < 2 ^ 8)
    (hi : i.val < 256) (hr : r.OnCurve) (hrb : r.LimbsLt 52)
    (hrp : r.toPoint = nafTail a_naf (i.val + 1) • A + nafTail b_naf (i.val + 1) • B) :
    mul.«64bit-tables_loop1» a_naf b_naf i table_A table_B r
      ⦃ (res : ProjectivePoint.«64bit-tables») => res.OnCurve ∧
        res.toPoint = nafTail a_naf 0 • A + nafTail b_naf 0 • B ∧ res.LimbsLt 52 ⦄ := by
  rw [mul_loop1_eq]
  exact EdwardsOps.Bits64Tables.vdbLoop1T_spec
    EdwardsOps.Bits64Tables.addN_spec EdwardsOps.Bits64Tables.subN_spec
      EdwardsOps.Bits64Tables.addA_spec
    EdwardsOps.Bits64Tables.subA_spec EdwardsOps.Bits64Tables.asExtended_spec
    EdwardsOps.Bits64Tables.pDouble_spec EdwardsOps.Bits64Tables.cAsProjective_spec
    a_naf b_naf i table_A table_B r A B hA hAb hB hBb ha hb hi
    hr hrb hrp

open window.«NafLookupTable5ProjectiveNielsPoint64bit-tables».Insts in
open scoped Helpers.IndexStep in
/-- `vartime_double_base::mul`: `a • A + b • B` for the basepoint `B` (unreduced scalars
`< 2^255`, the precondition of `non_adjacent_form`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (a : scalar.Scalar) (A : edwards.EdwardsPoint.«64bit-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 52) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    mul.«64bit-tables» a A b ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul.«64bit-tables»
  step as ⟨a_naf, haval, hadig, hanaf⟩
  step as ⟨b_naf, hbval, hbdig, hbnaf⟩
  step as ⟨iter, hiter⟩
  step with mul_loop0_spec iter a_naf b_naf 255#usize (by rw [hiter]; rfl) (by rw [hiter]; decide)
    (by decide) (fun k hk hk' => absurd hk' (by rw [hiter] at hk; simp at hk; omega))
    as ⟨i, hi, hz⟩
  step with «CoreConvertFromSharedAEdwardsPoint64bit-tables».from_spec
    as ⟨tA, htA, htAb⟩
  step as ⟨tB, htB, htBb⟩
  step with ProjectivePoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨r, hron, hrp, hrb⟩
  have hr' : r.toPoint = nafTail a_naf (i.val + 1) • A.toPoint +
      nafTail b_naf (i.val + 1) • basepoint := by
    rw [hrp, nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2, zero_smul, zero_smul, add_zero]
  step with mul_loop1_spec a_naf b_naf i tA tB r A.toPoint basepoint htA htAb htB htBb
    (fun k hk h => hadig k hk h) (fun k hk h => hbdig k hk h) hi hron hrb hr'
    as ⟨res, hreson, hresp, hresb⟩
  step with «ProjectivePoint64bit-tables».as_extended_spec res hresb hreson as ⟨e, heon, hep, heb⟩
  refine ⟨heon, ?_, heb⟩
  rw [hep, hresp, nafTail_zero, nafTail_zero, haval, hbval, natCast_zsmul, natCast_zsmul]

end «64bit-tables»

end

section
open «Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint32bit-tablesCompletedPoint32bit-tables»
  (add_spec)
open «CoreOpsArithSubSharedAProjectiveNielsPoint32bit-tablesCompletedPoint32bit-tables»
  (sub_spec)

namespace «32bit-tables»

private theorem mul_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) :
    mul.«32bit-tables_loop0» iter a_naf b_naf i = EdwardsOps.vdbLoop0 iter a_naf b_naf i := by
  unfold mul.«32bit-tables_loop0» EdwardsOps.vdbLoop0
  congr 1

private theorem mul_loop1_eq (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 ProjectiveNielsPoint.«32bit-tables»)
    (table_B : window.NafLookupTable8 AffineNielsPoint.«32bit-tables»)
    (r : ProjectivePoint.«32bit-tables») :
    mul.«32bit-tables_loop1» a_naf b_naf i table_A table_B r =
      EdwardsOps.Bits32Tables.vdbLoop1T a_naf b_naf i table_A table_B r := by
  unfold mul.«32bit-tables_loop1» EdwardsOps.vdbLoop1T
  congr 1

/-- The first loop of `mul`: the highest index at which a digit of `a` or `b` is nonzero (`0` if
there is none). -/
@[local step]
private theorem mul_loop0_spec (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) (hstart : iter.iter.start.val = 0)
    (hend : iter.iter.end.val ≤ 256) (hi : i.val < 256)
    (hz : ∀ k, iter.iter.end.val ≤ k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0) :
    mul.«32bit-tables_loop0» iter a_naf b_naf i ⦃ (r : Usize) =>
      r.val < 256 ∧ ∀ k, r.val < k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0 ⦄ := by
  rw [mul_loop0_eq]
  exact EdwardsOps.vdbLoop0_spec iter a_naf b_naf i hstart hend hi hz

/-- The second loop of `mul`: after the digits `i, …, 255`, the accumulator represents
`nafTail a i • A + nafTail b i • B`. -/
@[local step]
private theorem mul_loop1_spec (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 ProjectiveNielsPoint.«32bit-tables»)
    (table_B : window.NafLookupTable8 AffineNielsPoint.«32bit-tables»)
    (r : ProjectivePoint.«32bit-tables») (A B : curve25519.edwards.Point)
    (hA : table_A.Represents A) (hAb : table_A.LimbsLt 27)
    (hB : table_B.Represents B) (hBb : table_B.LimbsLt 27)
    (ha : ∀ k : ℕ, k < 256 → a_naf[k]!.val ≠ 0 → a_naf[k]!.val % 2 = 1 ∧
      2 * |a_naf[k]!.val| < 2 ^ 5)
    (hb : ∀ k : ℕ, k < 256 → b_naf[k]!.val ≠ 0 → b_naf[k]!.val % 2 = 1 ∧
      2 * |b_naf[k]!.val| < 2 ^ 8)
    (hi : i.val < 256) (hr : r.OnCurve) (hrb : r.LimbsLt 26)
    (hrp : r.toPoint = nafTail a_naf (i.val + 1) • A + nafTail b_naf (i.val + 1) • B) :
    mul.«32bit-tables_loop1» a_naf b_naf i table_A table_B r
      ⦃ (res : ProjectivePoint.«32bit-tables») => res.OnCurve ∧
        res.toPoint = nafTail a_naf 0 • A + nafTail b_naf 0 • B ∧ res.LimbsLt 26 ⦄ := by
  rw [mul_loop1_eq]
  exact EdwardsOps.Bits32Tables.vdbLoop1T_spec
    EdwardsOps.Bits32Tables.addN_spec EdwardsOps.Bits32Tables.subN_spec
      EdwardsOps.Bits32Tables.addA_spec
    EdwardsOps.Bits32Tables.subA_spec EdwardsOps.Bits32Tables.asExtended_spec
    EdwardsOps.Bits32Tables.pDouble_spec EdwardsOps.Bits32Tables.cAsProjective_spec
    a_naf b_naf i table_A table_B r A B hA hAb hB hBb ha hb
    hi hr hrb hrp

open window.«NafLookupTable5ProjectiveNielsPoint32bit-tables».Insts in
open scoped Helpers.IndexStep in
/-- `vartime_double_base::mul`: `a • A + b • B` for the basepoint `B` (unreduced scalars
`< 2^255`, the precondition of `non_adjacent_form`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (a : scalar.Scalar) (A : edwards.EdwardsPoint.«32bit-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 26) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    mul.«32bit-tables» a A b ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul.«32bit-tables»
  step as ⟨a_naf, haval, hadig, hanaf⟩
  step as ⟨b_naf, hbval, hbdig, hbnaf⟩
  step as ⟨iter, hiter⟩
  step with mul_loop0_spec iter a_naf b_naf 255#usize (by rw [hiter]; rfl) (by rw [hiter]; decide)
    (by decide) (fun k hk hk' => absurd hk' (by rw [hiter] at hk; simp at hk; omega))
    as ⟨i, hi, hz⟩
  step with «CoreConvertFromSharedAEdwardsPoint32bit-tables».from_spec
    as ⟨tA, htA, htAb⟩
  step as ⟨tB, htB, htBb⟩
  step with ProjectivePoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨r, hron, hrp, hrb⟩
  have hr' : r.toPoint = nafTail a_naf (i.val + 1) • A.toPoint +
      nafTail b_naf (i.val + 1) • basepoint := by
    rw [hrp, nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2, zero_smul, zero_smul, add_zero]
  step with mul_loop1_spec a_naf b_naf i tA tB r A.toPoint basepoint htA htAb htB htBb
    (fun k hk h => hadig k hk h) (fun k hk h => hbdig k hk h) hi hron hrb hr'
    as ⟨res, hreson, hresp, hresb⟩
  step with «ProjectivePoint32bit-tables».as_extended_spec res hresb hreson as ⟨e, heon, hep, heb⟩
  refine ⟨heon, ?_, heb⟩
  rw [hep, hresp, nafTail_zero, nafTail_zero, haval, hbval, natCast_zsmul, natCast_zsmul]

end «32bit-tables»

end

section
open «Shared0EdwardsPoint64bit-notables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint64bit-notablesCompletedPoint64bit-notables»
  (add_spec)
open «CoreOpsArithSubSharedAProjectiveNielsPoint64bit-notablesCompletedPoint64bit-notables»
  (sub_spec)

namespace «64bit-notables»

private theorem mul_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) :
    mul.«64bit-notables_loop0» iter a_naf b_naf i = EdwardsOps.vdbLoop0 iter a_naf b_naf i := by
  unfold mul.«64bit-notables_loop0» EdwardsOps.vdbLoop0
  congr 1

private theorem mul_loop1_eq (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 ProjectiveNielsPoint.«64bit-notables»)
    (table_B : window.NafLookupTable5 ProjectiveNielsPoint.«64bit-notables»)
    (r : ProjectivePoint.«64bit-notables») :
    mul.«64bit-notables_loop1» a_naf b_naf i table_A table_B r =
      EdwardsOps.Bits64NoTables.vdbLoop1N a_naf b_naf i table_A table_B r := by
  unfold mul.«64bit-notables_loop1» EdwardsOps.vdbLoop1N
  congr 1

/-- The first loop of `mul`: the highest index at which a digit of `a` or `b` is nonzero (`0` if
there is none). -/
@[local step]
private theorem mul_loop0_spec (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) (hstart : iter.iter.start.val = 0)
    (hend : iter.iter.end.val ≤ 256) (hi : i.val < 256)
    (hz : ∀ k, iter.iter.end.val ≤ k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0) :
    mul.«64bit-notables_loop0» iter a_naf b_naf i ⦃ (r : Usize) =>
      r.val < 256 ∧ ∀ k, r.val < k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0 ⦄ := by
  rw [mul_loop0_eq]
  exact EdwardsOps.vdbLoop0_spec iter a_naf b_naf i hstart hend hi hz

/-- The second loop of `mul`: after the digits `i, …, 255`, the accumulator represents
`nafTail a i • A + nafTail b i • B`. -/
@[local step]
private theorem mul_loop1_spec (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A table_B : window.NafLookupTable5 ProjectiveNielsPoint.«64bit-notables»)
    (r : ProjectivePoint.«64bit-notables») (A B : curve25519.edwards.Point)
    (hA : table_A.Represents A) (hAb : table_A.LimbsLt 54)
    (hB : table_B.Represents B) (hBb : table_B.LimbsLt 54)
    (ha : ∀ k : ℕ, k < 256 → a_naf[k]!.val ≠ 0 → a_naf[k]!.val % 2 = 1 ∧
      2 * |a_naf[k]!.val| < 2 ^ 5)
    (hb : ∀ k : ℕ, k < 256 → b_naf[k]!.val ≠ 0 → b_naf[k]!.val % 2 = 1 ∧
      2 * |b_naf[k]!.val| < 2 ^ 5)
    (hi : i.val < 256) (hr : r.OnCurve) (hrb : r.LimbsLt 52)
    (hrp : r.toPoint = nafTail a_naf (i.val + 1) • A + nafTail b_naf (i.val + 1) • B) :
    mul.«64bit-notables_loop1» a_naf b_naf i table_A table_B r
      ⦃ (res : ProjectivePoint.«64bit-notables») => res.OnCurve ∧
        res.toPoint = nafTail a_naf 0 • A + nafTail b_naf 0 • B ∧ res.LimbsLt 52 ⦄ := by
  rw [mul_loop1_eq]
  exact EdwardsOps.Bits64NoTables.vdbLoop1N_spec
    EdwardsOps.Bits64NoTables.addN_spec EdwardsOps.Bits64NoTables.subN_spec
    EdwardsOps.Bits64NoTables.asExtended_spec EdwardsOps.Bits64NoTables.pDouble_spec
    EdwardsOps.Bits64NoTables.cAsProjective_spec a_naf b_naf i
    table_A table_B r A B hA hAb hB hBb ha hb hi hr hrb hrp

open window.«NafLookupTable5ProjectiveNielsPoint64bit-notables».Insts in
open scoped Helpers.IndexStep in
/-- `vartime_double_base::mul`: `a • A + b • B` for the basepoint `B` (unreduced scalars
`< 2^255`, the precondition of `non_adjacent_form`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (a : scalar.Scalar) (A : edwards.EdwardsPoint.«64bit-notables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 52) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    mul.«64bit-notables» a A b ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul.«64bit-notables»
  step as ⟨a_naf, haval, hadig, hanaf⟩
  step as ⟨b_naf, hbval, hbdig, hbnaf⟩
  step as ⟨iter, hiter⟩
  step with mul_loop0_spec iter a_naf b_naf 255#usize (by rw [hiter]; rfl) (by rw [hiter]; decide)
    (by decide) (fun k hk hk' => absurd hk' (by rw [hiter] at hk; simp at hk; omega))
    as ⟨i, hi, hz⟩
  step with «CoreConvertFromSharedAEdwardsPoint64bit-notables».from_spec
    as ⟨tA, htA, htAb⟩
  step with backend.serial.u64.constants.«64bit-notables».ED25519_BASEPOINT_POINT_spec
    as ⟨bp, hbpon, hbp, hbpb⟩
  step with «CoreConvertFromSharedAEdwardsPoint64bit-notables».from_spec
    as ⟨tB, htB, htBb⟩
  step with
      ProjectivePoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨r, hron, hrp, hrb⟩
  have hr' : r.toPoint = nafTail a_naf (i.val + 1) • A.toPoint +
      nafTail b_naf (i.val + 1) • bp.toPoint := by
    rw [hrp, nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2, zero_smul, zero_smul, add_zero]
  step with mul_loop1_spec a_naf b_naf i tA tB r A.toPoint bp.toPoint htA htAb htB htBb
    (fun k hk h => hadig k hk h) (fun k hk h => hbdig k hk h) hi hron hrb hr'
    as ⟨res, hreson, hresp, hresb⟩
  step with «ProjectivePoint64bit-notables».as_extended_spec res hresb hreson
    as ⟨e, heon, hep, heb⟩
  refine ⟨heon, ?_, heb⟩
  rw [hep, hresp, nafTail_zero, nafTail_zero, haval, hbval, hbp, natCast_zsmul, natCast_zsmul]

end «64bit-notables»

end

section
open «Shared0EdwardsPoint32bit-notables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint32bit-notablesCompletedPoint32bit-notables»
  (add_spec)
open «CoreOpsArithSubSharedAProjectiveNielsPoint32bit-notablesCompletedPoint32bit-notables»
  (sub_spec)

namespace «32bit-notables»

private theorem mul_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) :
    mul.«32bit-notables_loop0» iter a_naf b_naf i = EdwardsOps.vdbLoop0 iter a_naf b_naf i := by
  unfold mul.«32bit-notables_loop0» EdwardsOps.vdbLoop0
  congr 1

private theorem mul_loop1_eq (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 ProjectiveNielsPoint.«32bit-notables»)
    (table_B : window.NafLookupTable5 ProjectiveNielsPoint.«32bit-notables»)
    (r : ProjectivePoint.«32bit-notables») :
    mul.«32bit-notables_loop1» a_naf b_naf i table_A table_B r =
      EdwardsOps.Bits32NoTables.vdbLoop1N a_naf b_naf i table_A table_B r := by
  unfold mul.«32bit-notables_loop1» EdwardsOps.vdbLoop1N
  congr 1

/-- The first loop of `mul`: the highest index at which a digit of `a` or `b` is nonzero (`0` if
there is none). -/
@[local step]
private theorem mul_loop0_spec (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) (hstart : iter.iter.start.val = 0)
    (hend : iter.iter.end.val ≤ 256) (hi : i.val < 256)
    (hz : ∀ k, iter.iter.end.val ≤ k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0) :
    mul.«32bit-notables_loop0» iter a_naf b_naf i ⦃ (r : Usize) =>
      r.val < 256 ∧ ∀ k, r.val < k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0 ⦄ := by
  rw [mul_loop0_eq]
  exact EdwardsOps.vdbLoop0_spec iter a_naf b_naf i hstart hend hi hz

/-- The second loop of `mul`: after the digits `i, …, 255`, the accumulator represents
`nafTail a i • A + nafTail b i • B`. -/
@[local step]
private theorem mul_loop1_spec (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A table_B : window.NafLookupTable5 ProjectiveNielsPoint.«32bit-notables»)
    (r : ProjectivePoint.«32bit-notables») (A B : curve25519.edwards.Point)
    (hA : table_A.Represents A) (hAb : table_A.LimbsLt 27)
    (hB : table_B.Represents B) (hBb : table_B.LimbsLt 27)
    (ha : ∀ k : ℕ, k < 256 → a_naf[k]!.val ≠ 0 → a_naf[k]!.val % 2 = 1 ∧
      2 * |a_naf[k]!.val| < 2 ^ 5)
    (hb : ∀ k : ℕ, k < 256 → b_naf[k]!.val ≠ 0 → b_naf[k]!.val % 2 = 1 ∧
      2 * |b_naf[k]!.val| < 2 ^ 5)
    (hi : i.val < 256) (hr : r.OnCurve) (hrb : r.LimbsLt 26)
    (hrp : r.toPoint = nafTail a_naf (i.val + 1) • A + nafTail b_naf (i.val + 1) • B) :
    mul.«32bit-notables_loop1» a_naf b_naf i table_A table_B r
      ⦃ (res : ProjectivePoint.«32bit-notables») => res.OnCurve ∧
        res.toPoint = nafTail a_naf 0 • A + nafTail b_naf 0 • B ∧ res.LimbsLt 26 ⦄ := by
  rw [mul_loop1_eq]
  exact EdwardsOps.Bits32NoTables.vdbLoop1N_spec
    EdwardsOps.Bits32NoTables.addN_spec EdwardsOps.Bits32NoTables.subN_spec
    EdwardsOps.Bits32NoTables.asExtended_spec EdwardsOps.Bits32NoTables.pDouble_spec
    EdwardsOps.Bits32NoTables.cAsProjective_spec a_naf b_naf
    i table_A table_B r A B hA hAb hB hBb ha hb hi hr hrb hrp

open window.«NafLookupTable5ProjectiveNielsPoint32bit-notables».Insts in
open scoped Helpers.IndexStep in
/-- `vartime_double_base::mul`: `a • A + b • B` for the basepoint `B` (unreduced scalars
`< 2^255`, the precondition of `non_adjacent_form`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (a : scalar.Scalar) (A : edwards.EdwardsPoint.«32bit-notables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 26) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    mul.«32bit-notables» a A b ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul.«32bit-notables»
  step as ⟨a_naf, haval, hadig, hanaf⟩
  step as ⟨b_naf, hbval, hbdig, hbnaf⟩
  step as ⟨iter, hiter⟩
  step with mul_loop0_spec iter a_naf b_naf 255#usize (by rw [hiter]; rfl) (by rw [hiter]; decide)
    (by decide) (fun k hk hk' => absurd hk' (by rw [hiter] at hk; simp at hk; omega))
    as ⟨i, hi, hz⟩
  step with «CoreConvertFromSharedAEdwardsPoint32bit-notables».from_spec
    as ⟨tA, htA, htAb⟩
  step with backend.serial.u32.constants.«32bit-notables».ED25519_BASEPOINT_POINT_spec
    as ⟨bp, hbpon, hbp, hbpb⟩
  step with «CoreConvertFromSharedAEdwardsPoint32bit-notables».from_spec
    as ⟨tB, htB, htBb⟩
  step with
      ProjectivePoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨r, hron, hrp, hrb⟩
  have hr' : r.toPoint = nafTail a_naf (i.val + 1) • A.toPoint +
      nafTail b_naf (i.val + 1) • bp.toPoint := by
    rw [hrp, nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').1,
      nafTail_eq_zero _ _ fun k hk hk' => (hz k hk hk').2, zero_smul, zero_smul, add_zero]
  step with mul_loop1_spec a_naf b_naf i tA tB r A.toPoint bp.toPoint htA htAb htB htBb
    (fun k hk h => hadig k hk h) (fun k hk h => hbdig k hk h) hi hron hrb hr'
    as ⟨res, hreson, hresp, hresb⟩
  step with «ProjectivePoint32bit-notables».as_extended_spec res hresb hreson
    as ⟨e, heon, hep, heb⟩
  refine ⟨heon, ?_, heb⟩
  rw [hep, hresp, nafTail_zero, nafTail_zero, haval, hbval, hbp, natCast_zsmul, natCast_zsmul]

end «32bit-notables»

end
end Curve25519Dalek.backend.serial.scalar_mul.vartime_double_base
