/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Helpers.Coords
public import Proofs.Helpers.EdwardsOps
import Proofs.Backend.Serial.CurveModels.AddAffineNiels
import Proofs.Backend.Serial.CurveModels.AddProjectiveNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.CurveModels.SubAffineNiels
import Proofs.Backend.Serial.CurveModels.SubProjectiveNiels
import Proofs.Edwards.Add
import Proofs.Edwards.AddAssign
import Proofs.Edwards.AsProjectiveNiels
import Proofs.Edwards.Identity
import Proofs.Edwards.MulByPow2
import Proofs.Backend.Serial.CurveModels.CompletedAsProjective
import Proofs.Backend.Serial.CurveModels.ProjectiveAsExtended
import Proofs.Backend.Serial.CurveModels.ProjectiveDouble
import Proofs.Backend.Serial.CurveModels.ProjectiveIdentity
import Proofs.Window.NafLookupTable5From
import Proofs.Window.LookupTableSelect
import Proofs.Window.LookupTableFrom
public section

/-! # The four configurations as `EdwardsOps`

The bounds are those of the point specs: `LimbsLt 52`, `LimbsLt 54`, `LimbsLt 54` on `u64`,
`LimbsLt 26`, `LimbsLt 27`, `MulBounded` on `u32` (extended, projective Niels, completed). The
specs are the configurations' point-level `*_spec` theorems, stated first as separate theorems
    (their
proofs use privately imported modules), then bundled. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

section
open Curve25519Dalek.«Shared0EdwardsPoint64bit-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint64bit-tablesCompletedPoint64bit-tables»
    renaming add → nielsAdd, add_spec → nielsAdd_spec
open «CoreOpsArithSubSharedAProjectiveNielsPoint64bit-tablesCompletedPoint64bit-tables»
    renaming sub → nielsSub, sub_spec → nielsSub_spec
open Curve25519Dalek.edwards.EdwardsPoint.«64bit-tables».Insts
open Curve25519Dalek.window.«NafLookupTable5ProjectiveNielsPoint64bit-tables».Insts
open Curve25519Dalek.«Shared0ProjectiveNielsPoint64bit-tables».Insts
set_option linter.style.longLine false
open Curve25519Dalek.window.«LookupTableProjectiveNielsPoint64bit-tables».Insts.«CoreConvertFromSharedAEdwardsPoint64bit-tables»
    renaming «from» → ltFromFn, from_spec → ltFromFn_spec
set_option linter.style.longLine true
open «CoreOpsArithAddSharedAAffineNielsPoint64bit-tablesCompletedPoint64bit-tables»
    renaming add → affineAdd, add_spec → affineAdd_spec
open «CoreOpsArithSubSharedAAffineNielsPoint64bit-tablesCompletedPoint64bit-tables»
    renaming sub → affineSub, sub_spec → affineSub_spec
open «CoreOpsArithAddEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»
    renaming add → edwardsAdd, add_spec → edwardsAdd_spec

namespace Curve25519Dalek.EdwardsOps

/-- The `«64bit-tables»` point operations. -/
@[expose] noncomputable def Bits64Tables : EdwardsOps where
  E := edwards.EdwardsPoint.«64bit-tables»
  N := ProjectiveNielsPoint.«64bit-tables»
  C := CompletedPoint.«64bit-tables»
  Pr := ProjectivePoint.«64bit-tables»
  An := AffineNielsPoint.«64bit-tables»
  inhE := inferInstance
  inhN := inferInstance
  inhA := inferInstance
  reprN := inferInstance
  copyN := ProjectiveNielsPoint.«64bit-tables».Insts.CoreMarkerCopy
  reprA := inferInstance
  copyA := AffineNielsPoint.«64bit-tables».Insts.CoreMarkerCopy
  aB := 54
  OnCurve r := r.OnCurve
  toPoint r := r.toPoint
  Bnd r := r.LimbsLt 52
  nB := 54
  cOnCurve r := r.OnCurve
  cToPoint r := r.toPoint
  cBnd r := r.LimbsLt 54
  pOnCurve r := r.OnCurve
  pToPoint r := r.toPoint
  pBnd r := r.LimbsLt 52
  identity := edwards.EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity
  add := edwardsAdd
  addAssign := «CoreOpsArithAddAssignEdwardsPoint64bit-tables».add_assign
  mulByPow2 := edwards.«EdwardsPoint64bit-tables».mul_by_pow_2
  addN := nielsAdd
  subN := nielsSub
  asExtended := «CompletedPoint64bit-tables».as_extended
  addA := affineAdd
  subA := affineSub
  asProjectiveNiels := edwards.«EdwardsPoint64bit-tables».as_projective_niels
  pIdentity := ProjectivePoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity
  pDouble := «ProjectivePoint64bit-tables».double
  cAsProjective := «CompletedPoint64bit-tables».as_projective
  pAsExtended := «ProjectivePoint64bit-tables».as_extended
  nafTable5 :=
    «CoreConvertFromSharedAEdwardsPoint64bit-tables».from
  ltSelect := window.LookupTable.select
    ProjectiveNielsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity
    ProjectiveNielsPoint.«64bit-tables».Insts.SubtleConditionallySelectable
    (subtle.ConditionallyNegatable.Blanket
      ProjectiveNielsPoint.«64bit-tables».Insts.SubtleConditionallySelectable
      «CoreOpsArithNegProjectiveNielsPoint64bit-tables»)
  ltFrom := ltFromFn

theorem Bits64Tables.identity_spec : Bits64Tables.IdentitySpec :=
  edwards.EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec

theorem Bits64Tables.add_spec : Bits64Tables.AddSpec :=
  edwardsAdd_spec

theorem Bits64Tables.addAssign_spec : Bits64Tables.AddAssignSpec :=
  «CoreOpsArithAddAssignEdwardsPoint64bit-tables».add_assign_spec

theorem Bits64Tables.mulByPow2_spec : Bits64Tables.MulByPow2Spec :=
  edwards.«EdwardsPoint64bit-tables».mul_by_pow_2_spec

theorem Bits64Tables.addN_spec : Bits64Tables.AddNSpec :=
  nielsAdd_spec

theorem Bits64Tables.subN_spec : Bits64Tables.SubNSpec :=
  nielsSub_spec

theorem Bits64Tables.addA_spec : Bits64Tables.AddASpec := affineAdd_spec

theorem Bits64Tables.subA_spec : Bits64Tables.SubASpec := affineSub_spec

theorem Bits64Tables.asExtended_spec : Bits64Tables.AsExtendedSpec :=
  «CompletedPoint64bit-tables».as_extended_spec

theorem Bits64Tables.asProjectiveNiels_spec : Bits64Tables.AsProjectiveNielsSpec :=
  edwards.«EdwardsPoint64bit-tables».as_projective_niels_spec

theorem Bits64Tables.pIdentity_spec : Bits64Tables.PIdentitySpec :=
  ProjectivePoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec

theorem Bits64Tables.pDouble_spec : Bits64Tables.PDoubleSpec :=
  «ProjectivePoint64bit-tables».double_spec

theorem Bits64Tables.cAsProjective_spec : Bits64Tables.CAsProjectiveSpec :=
  «CompletedPoint64bit-tables».as_projective_spec

theorem Bits64Tables.pAsExtended_spec : Bits64Tables.PAsExtendedSpec :=
  «ProjectivePoint64bit-tables».as_extended_spec

theorem Bits64Tables.nafTable5_spec : Bits64Tables.NafTable5Spec :=
  «CoreConvertFromSharedAEdwardsPoint64bit-tables».from_spec

theorem Bits64Tables.ltSelect_spec : Bits64Tables.LtSelectSpec :=
  window.«LookupTableProjectiveNielsPoint64bit-tables».select_spec

theorem Bits64Tables.ltFrom_spec : Bits64Tables.LtFromSpec :=
  ltFromFn_spec

end Curve25519Dalek.EdwardsOps

end

section
open Curve25519Dalek.«Shared0EdwardsPoint64bit-notables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint64bit-notablesCompletedPoint64bit-notables»
    renaming add → nielsAdd, add_spec → nielsAdd_spec
open «CoreOpsArithSubSharedAProjectiveNielsPoint64bit-notablesCompletedPoint64bit-notables»
    renaming sub → nielsSub, sub_spec → nielsSub_spec
open Curve25519Dalek.edwards.EdwardsPoint.«64bit-notables».Insts
open Curve25519Dalek.window.«NafLookupTable5ProjectiveNielsPoint64bit-notables».Insts
open Curve25519Dalek.«Shared0ProjectiveNielsPoint64bit-notables».Insts
set_option linter.style.longLine false
open Curve25519Dalek.window.«LookupTableProjectiveNielsPoint64bit-notables».Insts.«CoreConvertFromSharedAEdwardsPoint64bit-notables»
    renaming «from» → ltFromFn, from_spec → ltFromFn_spec
set_option linter.style.longLine true
open «CoreOpsArithAddSharedAAffineNielsPoint64bit-notablesCompletedPoint64bit-notables»
    renaming add → affineAdd, add_spec → affineAdd_spec
open «CoreOpsArithSubSharedAAffineNielsPoint64bit-notablesCompletedPoint64bit-notables»
    renaming sub → affineSub, sub_spec → affineSub_spec
open «CoreOpsArithAddEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»
    renaming add → edwardsAdd, add_spec → edwardsAdd_spec

namespace Curve25519Dalek.EdwardsOps

/-- The `«64bit-notables»` point operations. -/
@[expose] noncomputable def Bits64NoTables : EdwardsOps where
  E := edwards.EdwardsPoint.«64bit-notables»
  N := ProjectiveNielsPoint.«64bit-notables»
  C := CompletedPoint.«64bit-notables»
  Pr := ProjectivePoint.«64bit-notables»
  An := AffineNielsPoint.«64bit-notables»
  inhE := inferInstance
  inhN := inferInstance
  inhA := inferInstance
  reprN := inferInstance
  copyN := ProjectiveNielsPoint.«64bit-notables».Insts.CoreMarkerCopy
  reprA := inferInstance
  copyA := AffineNielsPoint.«64bit-notables».Insts.CoreMarkerCopy
  aB := 54
  OnCurve r := r.OnCurve
  toPoint r := r.toPoint
  Bnd r := r.LimbsLt 52
  nB := 54
  cOnCurve r := r.OnCurve
  cToPoint r := r.toPoint
  cBnd r := r.LimbsLt 54
  pOnCurve r := r.OnCurve
  pToPoint r := r.toPoint
  pBnd r := r.LimbsLt 52
  identity := edwards.EdwardsPoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity.identity
  add := edwardsAdd
  addAssign := «CoreOpsArithAddAssignEdwardsPoint64bit-notables».add_assign
  mulByPow2 := edwards.«EdwardsPoint64bit-notables».mul_by_pow_2
  addN := nielsAdd
  subN := nielsSub
  asExtended := «CompletedPoint64bit-notables».as_extended
  addA := affineAdd
  subA := affineSub
  asProjectiveNiels := edwards.«EdwardsPoint64bit-notables».as_projective_niels
  pIdentity := ProjectivePoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity.identity
  pDouble := «ProjectivePoint64bit-notables».double
  cAsProjective := «CompletedPoint64bit-notables».as_projective
  pAsExtended := «ProjectivePoint64bit-notables».as_extended
  nafTable5 :=
    «CoreConvertFromSharedAEdwardsPoint64bit-notables».from
  ltSelect := window.LookupTable.select
    ProjectiveNielsPoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity
    ProjectiveNielsPoint.«64bit-notables».Insts.SubtleConditionallySelectable
    (subtle.ConditionallyNegatable.Blanket
      ProjectiveNielsPoint.«64bit-notables».Insts.SubtleConditionallySelectable
      «CoreOpsArithNegProjectiveNielsPoint64bit-notables»)
  ltFrom := ltFromFn

theorem Bits64NoTables.identity_spec : Bits64NoTables.IdentitySpec :=
  edwards.EdwardsPoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity.identity_spec

theorem Bits64NoTables.add_spec : Bits64NoTables.AddSpec :=
  edwardsAdd_spec

theorem Bits64NoTables.addAssign_spec : Bits64NoTables.AddAssignSpec :=
  «CoreOpsArithAddAssignEdwardsPoint64bit-notables».add_assign_spec

theorem Bits64NoTables.mulByPow2_spec : Bits64NoTables.MulByPow2Spec :=
  edwards.«EdwardsPoint64bit-notables».mul_by_pow_2_spec

theorem Bits64NoTables.addN_spec : Bits64NoTables.AddNSpec :=
  nielsAdd_spec

theorem Bits64NoTables.subN_spec : Bits64NoTables.SubNSpec :=
  nielsSub_spec

theorem Bits64NoTables.addA_spec : Bits64NoTables.AddASpec := affineAdd_spec

theorem Bits64NoTables.subA_spec : Bits64NoTables.SubASpec := affineSub_spec

theorem Bits64NoTables.asExtended_spec : Bits64NoTables.AsExtendedSpec :=
  «CompletedPoint64bit-notables».as_extended_spec

theorem Bits64NoTables.asProjectiveNiels_spec : Bits64NoTables.AsProjectiveNielsSpec :=
  edwards.«EdwardsPoint64bit-notables».as_projective_niels_spec

theorem Bits64NoTables.pIdentity_spec : Bits64NoTables.PIdentitySpec :=
  ProjectivePoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity.identity_spec

theorem Bits64NoTables.pDouble_spec : Bits64NoTables.PDoubleSpec :=
  «ProjectivePoint64bit-notables».double_spec

theorem Bits64NoTables.cAsProjective_spec : Bits64NoTables.CAsProjectiveSpec :=
  «CompletedPoint64bit-notables».as_projective_spec

theorem Bits64NoTables.pAsExtended_spec : Bits64NoTables.PAsExtendedSpec :=
  «ProjectivePoint64bit-notables».as_extended_spec

theorem Bits64NoTables.nafTable5_spec : Bits64NoTables.NafTable5Spec :=
  «CoreConvertFromSharedAEdwardsPoint64bit-notables».from_spec

theorem Bits64NoTables.ltSelect_spec : Bits64NoTables.LtSelectSpec :=
  window.«LookupTableProjectiveNielsPoint64bit-notables».select_spec

theorem Bits64NoTables.ltFrom_spec : Bits64NoTables.LtFromSpec :=
  ltFromFn_spec

end Curve25519Dalek.EdwardsOps

end

section
open Curve25519Dalek.«Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint32bit-tablesCompletedPoint32bit-tables»
    renaming add → nielsAdd, add_spec → nielsAdd_spec
open «CoreOpsArithSubSharedAProjectiveNielsPoint32bit-tablesCompletedPoint32bit-tables»
    renaming sub → nielsSub, sub_spec → nielsSub_spec
open Curve25519Dalek.edwards.EdwardsPoint.«32bit-tables».Insts
open Curve25519Dalek.window.«NafLookupTable5ProjectiveNielsPoint32bit-tables».Insts
open Curve25519Dalek.«Shared0ProjectiveNielsPoint32bit-tables».Insts
set_option linter.style.longLine false
open Curve25519Dalek.window.«LookupTableProjectiveNielsPoint32bit-tables».Insts.«CoreConvertFromSharedAEdwardsPoint32bit-tables»
    renaming «from» → ltFromFn, from_spec → ltFromFn_spec
set_option linter.style.longLine true
open «CoreOpsArithAddSharedAAffineNielsPoint32bit-tablesCompletedPoint32bit-tables»
    renaming add → affineAdd, add_spec → affineAdd_spec
open «CoreOpsArithSubSharedAAffineNielsPoint32bit-tablesCompletedPoint32bit-tables»
    renaming sub → affineSub, sub_spec → affineSub_spec
open «CoreOpsArithAddEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
    renaming add → edwardsAdd, add_spec → edwardsAdd_spec

namespace Curve25519Dalek.EdwardsOps

/-- The `«32bit-tables»` point operations. -/
@[expose] noncomputable def Bits32Tables : EdwardsOps where
  E := edwards.EdwardsPoint.«32bit-tables»
  N := ProjectiveNielsPoint.«32bit-tables»
  C := CompletedPoint.«32bit-tables»
  Pr := ProjectivePoint.«32bit-tables»
  An := AffineNielsPoint.«32bit-tables»
  inhE := inferInstance
  inhN := inferInstance
  inhA := inferInstance
  reprN := inferInstance
  copyN := ProjectiveNielsPoint.«32bit-tables».Insts.CoreMarkerCopy
  reprA := inferInstance
  copyA := AffineNielsPoint.«32bit-tables».Insts.CoreMarkerCopy
  aB := 27
  OnCurve r := r.OnCurve
  toPoint r := r.toPoint
  Bnd r := r.LimbsLt 26
  nB := 27
  cOnCurve r := r.OnCurve
  cToPoint r := r.toPoint
  cBnd r := r.MulBounded
  pOnCurve r := r.OnCurve
  pToPoint r := r.toPoint
  pBnd r := r.LimbsLt 26
  identity := edwards.EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity
  add := edwardsAdd
  addAssign := «CoreOpsArithAddAssignEdwardsPoint32bit-tables».add_assign
  mulByPow2 := edwards.«EdwardsPoint32bit-tables».mul_by_pow_2
  addN := nielsAdd
  subN := nielsSub
  asExtended := «CompletedPoint32bit-tables».as_extended
  addA := affineAdd
  subA := affineSub
  asProjectiveNiels := edwards.«EdwardsPoint32bit-tables».as_projective_niels
  pIdentity := ProjectivePoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity
  pDouble := «ProjectivePoint32bit-tables».double
  cAsProjective := «CompletedPoint32bit-tables».as_projective
  pAsExtended := «ProjectivePoint32bit-tables».as_extended
  nafTable5 :=
    «CoreConvertFromSharedAEdwardsPoint32bit-tables».from
  ltSelect := window.LookupTable.select
    ProjectiveNielsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity
    ProjectiveNielsPoint.«32bit-tables».Insts.SubtleConditionallySelectable
    (subtle.ConditionallyNegatable.Blanket
      ProjectiveNielsPoint.«32bit-tables».Insts.SubtleConditionallySelectable
      «CoreOpsArithNegProjectiveNielsPoint32bit-tables»)
  ltFrom := ltFromFn

theorem Bits32Tables.identity_spec : Bits32Tables.IdentitySpec :=
  edwards.EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec

theorem Bits32Tables.add_spec : Bits32Tables.AddSpec :=
  edwardsAdd_spec

theorem Bits32Tables.addAssign_spec : Bits32Tables.AddAssignSpec :=
  «CoreOpsArithAddAssignEdwardsPoint32bit-tables».add_assign_spec

theorem Bits32Tables.mulByPow2_spec : Bits32Tables.MulByPow2Spec :=
  edwards.«EdwardsPoint32bit-tables».mul_by_pow_2_spec

theorem Bits32Tables.addN_spec : Bits32Tables.AddNSpec :=
  nielsAdd_spec

theorem Bits32Tables.subN_spec : Bits32Tables.SubNSpec :=
  nielsSub_spec

theorem Bits32Tables.addA_spec : Bits32Tables.AddASpec := affineAdd_spec

theorem Bits32Tables.subA_spec : Bits32Tables.SubASpec := affineSub_spec

theorem Bits32Tables.asExtended_spec : Bits32Tables.AsExtendedSpec :=
  «CompletedPoint32bit-tables».as_extended_spec

theorem Bits32Tables.asProjectiveNiels_spec : Bits32Tables.AsProjectiveNielsSpec :=
  edwards.«EdwardsPoint32bit-tables».as_projective_niels_spec

theorem Bits32Tables.pIdentity_spec : Bits32Tables.PIdentitySpec :=
  ProjectivePoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec

theorem Bits32Tables.pDouble_spec : Bits32Tables.PDoubleSpec :=
  «ProjectivePoint32bit-tables».double_spec

theorem Bits32Tables.cAsProjective_spec : Bits32Tables.CAsProjectiveSpec :=
  «CompletedPoint32bit-tables».as_projective_spec

theorem Bits32Tables.pAsExtended_spec : Bits32Tables.PAsExtendedSpec :=
  «ProjectivePoint32bit-tables».as_extended_spec

theorem Bits32Tables.nafTable5_spec : Bits32Tables.NafTable5Spec :=
  «CoreConvertFromSharedAEdwardsPoint32bit-tables».from_spec

theorem Bits32Tables.ltSelect_spec : Bits32Tables.LtSelectSpec :=
  window.«LookupTableProjectiveNielsPoint32bit-tables».select_spec

theorem Bits32Tables.ltFrom_spec : Bits32Tables.LtFromSpec :=
  ltFromFn_spec

end Curve25519Dalek.EdwardsOps

end

section
open Curve25519Dalek.«Shared0EdwardsPoint32bit-notables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint32bit-notablesCompletedPoint32bit-notables»
    renaming add → nielsAdd, add_spec → nielsAdd_spec
open «CoreOpsArithSubSharedAProjectiveNielsPoint32bit-notablesCompletedPoint32bit-notables»
    renaming sub → nielsSub, sub_spec → nielsSub_spec
open Curve25519Dalek.edwards.EdwardsPoint.«32bit-notables».Insts
open Curve25519Dalek.window.«NafLookupTable5ProjectiveNielsPoint32bit-notables».Insts
open Curve25519Dalek.«Shared0ProjectiveNielsPoint32bit-notables».Insts
set_option linter.style.longLine false
open Curve25519Dalek.window.«LookupTableProjectiveNielsPoint32bit-notables».Insts.«CoreConvertFromSharedAEdwardsPoint32bit-notables»
    renaming «from» → ltFromFn, from_spec → ltFromFn_spec
set_option linter.style.longLine true
open «CoreOpsArithAddSharedAAffineNielsPoint32bit-notablesCompletedPoint32bit-notables»
    renaming add → affineAdd, add_spec → affineAdd_spec
open «CoreOpsArithSubSharedAAffineNielsPoint32bit-notablesCompletedPoint32bit-notables»
    renaming sub → affineSub, sub_spec → affineSub_spec
open «CoreOpsArithAddEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
    renaming add → edwardsAdd, add_spec → edwardsAdd_spec

namespace Curve25519Dalek.EdwardsOps

/-- The `«32bit-notables»` point operations. -/
@[expose] noncomputable def Bits32NoTables : EdwardsOps where
  E := edwards.EdwardsPoint.«32bit-notables»
  N := ProjectiveNielsPoint.«32bit-notables»
  C := CompletedPoint.«32bit-notables»
  Pr := ProjectivePoint.«32bit-notables»
  An := AffineNielsPoint.«32bit-notables»
  inhE := inferInstance
  inhN := inferInstance
  inhA := inferInstance
  reprN := inferInstance
  copyN := ProjectiveNielsPoint.«32bit-notables».Insts.CoreMarkerCopy
  reprA := inferInstance
  copyA := AffineNielsPoint.«32bit-notables».Insts.CoreMarkerCopy
  aB := 27
  OnCurve r := r.OnCurve
  toPoint r := r.toPoint
  Bnd r := r.LimbsLt 26
  nB := 27
  cOnCurve r := r.OnCurve
  cToPoint r := r.toPoint
  cBnd r := r.MulBounded
  pOnCurve r := r.OnCurve
  pToPoint r := r.toPoint
  pBnd r := r.LimbsLt 26
  identity := edwards.EdwardsPoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity.identity
  add := edwardsAdd
  addAssign := «CoreOpsArithAddAssignEdwardsPoint32bit-notables».add_assign
  mulByPow2 := edwards.«EdwardsPoint32bit-notables».mul_by_pow_2
  addN := nielsAdd
  subN := nielsSub
  asExtended := «CompletedPoint32bit-notables».as_extended
  addA := affineAdd
  subA := affineSub
  asProjectiveNiels := edwards.«EdwardsPoint32bit-notables».as_projective_niels
  pIdentity := ProjectivePoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity.identity
  pDouble := «ProjectivePoint32bit-notables».double
  cAsProjective := «CompletedPoint32bit-notables».as_projective
  pAsExtended := «ProjectivePoint32bit-notables».as_extended
  nafTable5 :=
    «CoreConvertFromSharedAEdwardsPoint32bit-notables».from
  ltSelect := window.LookupTable.select
    ProjectiveNielsPoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity
    ProjectiveNielsPoint.«32bit-notables».Insts.SubtleConditionallySelectable
    (subtle.ConditionallyNegatable.Blanket
      ProjectiveNielsPoint.«32bit-notables».Insts.SubtleConditionallySelectable
      «CoreOpsArithNegProjectiveNielsPoint32bit-notables»)
  ltFrom := ltFromFn

theorem Bits32NoTables.identity_spec : Bits32NoTables.IdentitySpec :=
  edwards.EdwardsPoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity.identity_spec

theorem Bits32NoTables.add_spec : Bits32NoTables.AddSpec :=
  edwardsAdd_spec

theorem Bits32NoTables.addAssign_spec : Bits32NoTables.AddAssignSpec :=
  «CoreOpsArithAddAssignEdwardsPoint32bit-notables».add_assign_spec

theorem Bits32NoTables.mulByPow2_spec : Bits32NoTables.MulByPow2Spec :=
  edwards.«EdwardsPoint32bit-notables».mul_by_pow_2_spec

theorem Bits32NoTables.addN_spec : Bits32NoTables.AddNSpec :=
  nielsAdd_spec

theorem Bits32NoTables.subN_spec : Bits32NoTables.SubNSpec :=
  nielsSub_spec

theorem Bits32NoTables.addA_spec : Bits32NoTables.AddASpec := affineAdd_spec

theorem Bits32NoTables.subA_spec : Bits32NoTables.SubASpec := affineSub_spec

theorem Bits32NoTables.asExtended_spec : Bits32NoTables.AsExtendedSpec :=
  «CompletedPoint32bit-notables».as_extended_spec

theorem Bits32NoTables.asProjectiveNiels_spec : Bits32NoTables.AsProjectiveNielsSpec :=
  edwards.«EdwardsPoint32bit-notables».as_projective_niels_spec

theorem Bits32NoTables.pIdentity_spec : Bits32NoTables.PIdentitySpec :=
  ProjectivePoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity.identity_spec

theorem Bits32NoTables.pDouble_spec : Bits32NoTables.PDoubleSpec :=
  «ProjectivePoint32bit-notables».double_spec

theorem Bits32NoTables.cAsProjective_spec : Bits32NoTables.CAsProjectiveSpec :=
  «CompletedPoint32bit-notables».as_projective_spec

theorem Bits32NoTables.pAsExtended_spec : Bits32NoTables.PAsExtendedSpec :=
  «ProjectivePoint32bit-notables».as_extended_spec

theorem Bits32NoTables.nafTable5_spec : Bits32NoTables.NafTable5Spec :=
  «CoreConvertFromSharedAEdwardsPoint32bit-notables».from_spec

theorem Bits32NoTables.ltSelect_spec : Bits32NoTables.LtSelectSpec :=
  window.«LookupTableProjectiveNielsPoint32bit-notables».select_spec

theorem Bits32NoTables.ltFrom_spec : Bits32NoTables.LtFromSpec :=
  ltFromFn_spec

end Curve25519Dalek.EdwardsOps

end
