/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
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
open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
  (add_spec_point)
open edwards.EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity
  (identity_spec_point)

namespace «x86_64-tables»

private theorem mul_eq (point : edwards.EdwardsPoint.«x86_64-tables») (s : scalar.Scalar) :
    mul.«x86_64-tables» point s = EdwardsOps.X86Tables.vbMul point s := by
  unfold mul.«x86_64-tables» EdwardsOps.vbMul
  congr 1

open scoped Helpers.IndexStep in
/-- `variable_base::mul`: `s • P` for the unreduced value of `s` (`s.asNat < 2^255`, the
precondition of `as_radix_16`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (point : edwards.EdwardsPoint.«x86_64-tables») (s : scalar.Scalar)
    (hpoint : point.LimbsLt 52) (hon : point.OnCurve) (hs : s.asNat < 2 ^ 255) :
    mul.«x86_64-tables» point s ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  rw [mul_eq]
  exact EdwardsOps.X86Tables.vbMul_spec
    EdwardsOps.X86Tables.identity_spec EdwardsOps.X86Tables.addN_spec
    EdwardsOps.X86Tables.asExtended_spec EdwardsOps.X86Tables.ltSelect_spec
    EdwardsOps.X86Tables.ltFrom_spec EdwardsOps.X86Tables.pDouble_spec
    EdwardsOps.X86Tables.cAsProjective_spec point s hpoint hon hs

end «x86_64-tables»

end

section
open «Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-tablesCompletedPointi686-tables»
  (add_spec_point)
open edwards.EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity
  (identity_spec_point)

namespace «i686-tables»

private theorem mul_eq (point : edwards.EdwardsPoint.«i686-tables») (s : scalar.Scalar) :
    mul.«i686-tables» point s = EdwardsOps.I686Tables.vbMul point s := by
  unfold mul.«i686-tables» EdwardsOps.vbMul
  congr 1

open scoped Helpers.IndexStep in
/-- `variable_base::mul`: `s • P` for the unreduced value of `s` (`s.asNat < 2^255`, the
precondition of `as_radix_16`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (point : edwards.EdwardsPoint.«i686-tables») (s : scalar.Scalar)
    (hpoint : point.LimbsLt 26) (hon : point.OnCurve) (hs : s.asNat < 2 ^ 255) :
    mul.«i686-tables» point s ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • point.toPoint ∧ r.LimbsLt 26 ⦄ := by
  rw [mul_eq]
  exact EdwardsOps.I686Tables.vbMul_spec
    EdwardsOps.I686Tables.identity_spec EdwardsOps.I686Tables.addN_spec
    EdwardsOps.I686Tables.asExtended_spec EdwardsOps.I686Tables.ltSelect_spec
    EdwardsOps.I686Tables.ltFrom_spec EdwardsOps.I686Tables.pDouble_spec
    EdwardsOps.I686Tables.cAsProjective_spec point s hpoint hon hs

end «i686-tables»

end

section
open «Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
  (add_spec_point)
open edwards.EdwardsPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity
  (identity_spec_point)

namespace «x86_64-no-tables»

private theorem mul_eq (point : edwards.EdwardsPoint.«x86_64-no-tables») (s : scalar.Scalar) :
    mul.«x86_64-no-tables» point s = EdwardsOps.X86NoTables.vbMul point s := by
  unfold mul.«x86_64-no-tables» EdwardsOps.vbMul
  congr 1

open scoped Helpers.IndexStep in
/-- `variable_base::mul`: `s • P` for the unreduced value of `s` (`s.asNat < 2^255`, the
precondition of `as_radix_16`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (point : edwards.EdwardsPoint.«x86_64-no-tables») (s : scalar.Scalar)
    (hpoint : point.LimbsLt 52) (hon : point.OnCurve) (hs : s.asNat < 2 ^ 255) :
    mul.«x86_64-no-tables» point s ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  rw [mul_eq]
  exact EdwardsOps.X86NoTables.vbMul_spec
    EdwardsOps.X86NoTables.identity_spec EdwardsOps.X86NoTables.addN_spec
    EdwardsOps.X86NoTables.asExtended_spec EdwardsOps.X86NoTables.ltSelect_spec
    EdwardsOps.X86NoTables.ltFrom_spec EdwardsOps.X86NoTables.pDouble_spec
    EdwardsOps.X86NoTables.cAsProjective_spec point s hpoint hon hs

end «x86_64-no-tables»

end

section
open «Shared0EdwardsPointi686-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»
  (add_spec_point)
open edwards.EdwardsPoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity
  (identity_spec_point)

namespace «i686-no-tables»

private theorem mul_eq (point : edwards.EdwardsPoint.«i686-no-tables») (s : scalar.Scalar) :
    mul.«i686-no-tables» point s = EdwardsOps.I686NoTables.vbMul point s := by
  unfold mul.«i686-no-tables» EdwardsOps.vbMul
  congr 1

open scoped Helpers.IndexStep in
/-- `variable_base::mul`: `s • P` for the unreduced value of `s` (`s.asNat < 2^255`, the
precondition of `as_radix_16`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (point : edwards.EdwardsPoint.«i686-no-tables») (s : scalar.Scalar)
    (hpoint : point.LimbsLt 26) (hon : point.OnCurve) (hs : s.asNat < 2 ^ 255) :
    mul.«i686-no-tables» point s ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • point.toPoint ∧ r.LimbsLt 26 ⦄ := by
  rw [mul_eq]
  exact EdwardsOps.I686NoTables.vbMul_spec
    EdwardsOps.I686NoTables.identity_spec EdwardsOps.I686NoTables.addN_spec
    EdwardsOps.I686NoTables.asExtended_spec EdwardsOps.I686NoTables.ltSelect_spec
    EdwardsOps.I686NoTables.ltFrom_spec EdwardsOps.I686NoTables.pDouble_spec
    EdwardsOps.I686NoTables.cAsProjective_spec point s hpoint hon hs

end «i686-no-tables»

end

end Curve25519Dalek.backend.serial.scalar_mul.variable_base
