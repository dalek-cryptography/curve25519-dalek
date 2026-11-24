module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
import Proofs.Backend.Serial.CurveModels.AddProjectiveNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.CurveModels.CompletedAsProjective
import Proofs.Backend.Serial.CurveModels.ProjectiveDouble
import Proofs.Edwards.Identity
import Proofs.Helpers.AsInt
import Proofs.Helpers.Iterator
import Proofs.Helpers.StepSpecs
import Proofs.Scalar.AsRadix16
import Proofs.Window.LookupTableFrom
import Proofs.Window.LookupTableSelect
public import Proofs.Helpers.EdwardsOps.Instances
public import Proofs.Backend.Serial.ScalarMul.VariableBase.MulGeneric
public section

/-! # `variable_base::mul`

Constant-time variable-base scalar multiplication: the radix-`16` digits `d[0], …, d[63]` of the
scalar (`as_radix_16`), Horner's rule from the top digit down, with `16 • Q` by four doublings and
`d[i] • P` from the lookup table of `P, 2 P, …, 8 P`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.variable_base

section
open «Shared0EdwardsPoint64bit-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint64bit-tablesCompletedPoint64bit-tables»
  (add_spec)
open edwards.EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity
  (identity_spec)

namespace «64bit-tables»

private theorem mul_eq (point : edwards.EdwardsPoint.«64bit-tables») (s : scalar.Scalar) :
    mul.«64bit-tables» point s = EdwardsOps.Bits64Tables.vbMul point s := by
  unfold mul.«64bit-tables» EdwardsOps.vbMul
  congr 1

open scoped Helpers.IndexStep in
/-- `variable_base::mul`: `s • P` for the unreduced value of `s` (`s.asNat < 2^255`, the
precondition of `as_radix_16`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (point : edwards.EdwardsPoint.«64bit-tables») (s : scalar.Scalar)
    (hpoint : point.LimbsLt 52) (hon : point.OnCurve) (hs : s.asNat < 2 ^ 255) :
    mul.«64bit-tables» point s ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  rw [mul_eq]
  exact EdwardsOps.Bits64Tables.vbMul_spec
    EdwardsOps.Bits64Tables.identity_spec EdwardsOps.Bits64Tables.addN_spec
    EdwardsOps.Bits64Tables.asExtended_spec EdwardsOps.Bits64Tables.ltSelect_spec
    EdwardsOps.Bits64Tables.ltFrom_spec EdwardsOps.Bits64Tables.pDouble_spec
    EdwardsOps.Bits64Tables.cAsProjective_spec point s hpoint hon hs

end «64bit-tables»

end

section
open «Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint32bit-tablesCompletedPoint32bit-tables»
  (add_spec)
open edwards.EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity
  (identity_spec)

namespace «32bit-tables»

private theorem mul_eq (point : edwards.EdwardsPoint.«32bit-tables») (s : scalar.Scalar) :
    mul.«32bit-tables» point s = EdwardsOps.Bits32Tables.vbMul point s := by
  unfold mul.«32bit-tables» EdwardsOps.vbMul
  congr 1

open scoped Helpers.IndexStep in
/-- `variable_base::mul`: `s • P` for the unreduced value of `s` (`s.asNat < 2^255`, the
precondition of `as_radix_16`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (point : edwards.EdwardsPoint.«32bit-tables») (s : scalar.Scalar)
    (hpoint : point.LimbsLt 26) (hon : point.OnCurve) (hs : s.asNat < 2 ^ 255) :
    mul.«32bit-tables» point s ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • point.toPoint ∧ r.LimbsLt 26 ⦄ := by
  rw [mul_eq]
  exact EdwardsOps.Bits32Tables.vbMul_spec
    EdwardsOps.Bits32Tables.identity_spec EdwardsOps.Bits32Tables.addN_spec
    EdwardsOps.Bits32Tables.asExtended_spec EdwardsOps.Bits32Tables.ltSelect_spec
    EdwardsOps.Bits32Tables.ltFrom_spec EdwardsOps.Bits32Tables.pDouble_spec
    EdwardsOps.Bits32Tables.cAsProjective_spec point s hpoint hon hs

end «32bit-tables»

end

section
open «Shared0EdwardsPoint64bit-notables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint64bit-notablesCompletedPoint64bit-notables»
  (add_spec)
open edwards.EdwardsPoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity
  (identity_spec)

namespace «64bit-notables»

private theorem mul_eq (point : edwards.EdwardsPoint.«64bit-notables») (s : scalar.Scalar) :
    mul.«64bit-notables» point s = EdwardsOps.Bits64NoTables.vbMul point s := by
  unfold mul.«64bit-notables» EdwardsOps.vbMul
  congr 1

open scoped Helpers.IndexStep in
/-- `variable_base::mul`: `s • P` for the unreduced value of `s` (`s.asNat < 2^255`, the
precondition of `as_radix_16`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (point : edwards.EdwardsPoint.«64bit-notables») (s : scalar.Scalar)
    (hpoint : point.LimbsLt 52) (hon : point.OnCurve) (hs : s.asNat < 2 ^ 255) :
    mul.«64bit-notables» point s ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  rw [mul_eq]
  exact EdwardsOps.Bits64NoTables.vbMul_spec
    EdwardsOps.Bits64NoTables.identity_spec EdwardsOps.Bits64NoTables.addN_spec
    EdwardsOps.Bits64NoTables.asExtended_spec EdwardsOps.Bits64NoTables.ltSelect_spec
    EdwardsOps.Bits64NoTables.ltFrom_spec EdwardsOps.Bits64NoTables.pDouble_spec
    EdwardsOps.Bits64NoTables.cAsProjective_spec point s hpoint hon hs

end «64bit-notables»

end

section
open «Shared0EdwardsPoint32bit-notables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint32bit-notablesCompletedPoint32bit-notables»
  (add_spec)
open edwards.EdwardsPoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity
  (identity_spec)

namespace «32bit-notables»

private theorem mul_eq (point : edwards.EdwardsPoint.«32bit-notables») (s : scalar.Scalar) :
    mul.«32bit-notables» point s = EdwardsOps.Bits32NoTables.vbMul point s := by
  unfold mul.«32bit-notables» EdwardsOps.vbMul
  congr 1

open scoped Helpers.IndexStep in
/-- `variable_base::mul`: `s • P` for the unreduced value of `s` (`s.asNat < 2^255`, the
precondition of `as_radix_16`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (point : edwards.EdwardsPoint.«32bit-notables») (s : scalar.Scalar)
    (hpoint : point.LimbsLt 26) (hon : point.OnCurve) (hs : s.asNat < 2 ^ 255) :
    mul.«32bit-notables» point s ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • point.toPoint ∧ r.LimbsLt 26 ⦄ := by
  rw [mul_eq]
  exact EdwardsOps.Bits32NoTables.vbMul_spec
    EdwardsOps.Bits32NoTables.identity_spec EdwardsOps.Bits32NoTables.addN_spec
    EdwardsOps.Bits32NoTables.asExtended_spec EdwardsOps.Bits32NoTables.ltSelect_spec
    EdwardsOps.Bits32NoTables.ltFrom_spec EdwardsOps.Bits32NoTables.pDouble_spec
    EdwardsOps.Bits32NoTables.cAsProjective_spec point s hpoint hon hs

end «32bit-notables»

end

end Curve25519Dalek.backend.serial.scalar_mul.variable_base
