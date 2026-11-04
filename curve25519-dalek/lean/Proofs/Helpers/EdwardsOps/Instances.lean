/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
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
specs are the configurations' `*_spec_point` theorems, stated first as separate theorems (their
proofs use privately imported modules), then bundled. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

section
open Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
    renaming add → nielsAdd, add_spec_point → nielsAdd_spec
open «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
    renaming sub → nielsSub, sub_spec_point → nielsSub_spec
open Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
open Curve25519Dalek.window.«NafLookupTable5ProjectiveNielsPointx86_64-tables».Insts
open Curve25519Dalek.«Shared0ProjectiveNielsPointx86_64-tables».Insts
set_option linter.style.longLine false
open Curve25519Dalek.window.«LookupTableProjectiveNielsPointx86_64-tables».Insts.«CoreConvertFromSharedAEdwardsPointx86_64-tables»
    renaming «from» → ltFromFn, from_spec → ltFromFn_spec
set_option linter.style.longLine true
open «CoreOpsArithAddSharedAAffineNielsPointx86_64-tablesCompletedPointx86_64-tables»
    renaming add → affineAdd, add_spec_point → affineAdd_spec
open «CoreOpsArithSubSharedAAffineNielsPointx86_64-tablesCompletedPointx86_64-tables»
    renaming sub → affineSub, sub_spec_point → affineSub_spec
open «CoreOpsArithAddEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
    renaming add → edwardsAdd, add_spec_point → edwardsAdd_spec

namespace Curve25519Dalek.EdwardsOps

/-- The `«x86_64-tables»` point operations. -/
@[expose] noncomputable def X86Tables : EdwardsOps where
  E := edwards.EdwardsPoint.«x86_64-tables»
  N := ProjectiveNielsPoint.«x86_64-tables»
  C := CompletedPoint.«x86_64-tables»
  Pr := ProjectivePoint.«x86_64-tables»
  An := AffineNielsPoint.«x86_64-tables»
  inhE := inferInstance
  inhN := inferInstance
  inhA := inferInstance
  reprN := inferInstance
  copyN := ProjectiveNielsPoint.«x86_64-tables».Insts.CoreMarkerCopy
  reprA := inferInstance
  copyA := AffineNielsPoint.«x86_64-tables».Insts.CoreMarkerCopy
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
  identity := edwards.EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity
  add := edwardsAdd
  addAssign := «CoreOpsArithAddAssignEdwardsPointx86_64-tables».add_assign
  mulByPow2 := edwards.«EdwardsPointx86_64-tables».mul_by_pow_2
  addN := nielsAdd
  subN := nielsSub
  asExtended := «CompletedPointx86_64-tables».as_extended
  addA := affineAdd
  subA := affineSub
  asProjectiveNiels := edwards.«EdwardsPointx86_64-tables».as_projective_niels
  pIdentity := ProjectivePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity
  pDouble := «ProjectivePointx86_64-tables».double
  cAsProjective := «CompletedPointx86_64-tables».as_projective
  pAsExtended := «ProjectivePointx86_64-tables».as_extended
  nafTable5 :=
    «CoreConvertFromSharedAEdwardsPointx86_64-tables».from
  ltSelect := window.LookupTable.select
    ProjectiveNielsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity
    ProjectiveNielsPoint.«x86_64-tables».Insts.SubtleConditionallySelectable
    (subtle.ConditionallyNegatable.Blanket
      ProjectiveNielsPoint.«x86_64-tables».Insts.SubtleConditionallySelectable
      «CoreOpsArithNegProjectiveNielsPointx86_64-tables»)
  ltFrom := ltFromFn

theorem X86Tables.identity_spec : X86Tables.IdentitySpec :=
  edwards.EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point

theorem X86Tables.add_spec : X86Tables.AddSpec :=
  edwardsAdd_spec

theorem X86Tables.addAssign_spec : X86Tables.AddAssignSpec :=
  «CoreOpsArithAddAssignEdwardsPointx86_64-tables».add_assign_spec_point

theorem X86Tables.mulByPow2_spec : X86Tables.MulByPow2Spec :=
  edwards.«EdwardsPointx86_64-tables».mul_by_pow_2_spec

theorem X86Tables.addN_spec : X86Tables.AddNSpec :=
  nielsAdd_spec

theorem X86Tables.subN_spec : X86Tables.SubNSpec :=
  nielsSub_spec

theorem X86Tables.addA_spec : X86Tables.AddASpec := affineAdd_spec

theorem X86Tables.subA_spec : X86Tables.SubASpec := affineSub_spec

theorem X86Tables.asExtended_spec : X86Tables.AsExtendedSpec :=
  «CompletedPointx86_64-tables».as_extended_spec_point

theorem X86Tables.asProjectiveNiels_spec : X86Tables.AsProjectiveNielsSpec :=
  edwards.«EdwardsPointx86_64-tables».as_projective_niels_spec_point

theorem X86Tables.pIdentity_spec : X86Tables.PIdentitySpec :=
  ProjectivePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point

theorem X86Tables.pDouble_spec : X86Tables.PDoubleSpec :=
  «ProjectivePointx86_64-tables».double_spec_point

theorem X86Tables.cAsProjective_spec : X86Tables.CAsProjectiveSpec :=
  «CompletedPointx86_64-tables».as_projective_spec_point

theorem X86Tables.pAsExtended_spec : X86Tables.PAsExtendedSpec :=
  «ProjectivePointx86_64-tables».as_extended_spec_point

theorem X86Tables.nafTable5_spec : X86Tables.NafTable5Spec :=
  «CoreConvertFromSharedAEdwardsPointx86_64-tables».from_spec

theorem X86Tables.ltSelect_spec : X86Tables.LtSelectSpec :=
  window.«LookupTableProjectiveNielsPointx86_64-tables».select_spec

theorem X86Tables.ltFrom_spec : X86Tables.LtFromSpec :=
  ltFromFn_spec

end Curve25519Dalek.EdwardsOps

end

section
open Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
    renaming add → nielsAdd, add_spec_point → nielsAdd_spec
open «CoreOpsArithSubSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
    renaming sub → nielsSub, sub_spec_point → nielsSub_spec
open Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
open Curve25519Dalek.window.«NafLookupTable5ProjectiveNielsPointx86_64-no-tables».Insts
open Curve25519Dalek.«Shared0ProjectiveNielsPointx86_64-no-tables».Insts
set_option linter.style.longLine false
open Curve25519Dalek.window.«LookupTableProjectiveNielsPointx86_64-no-tables».Insts.«CoreConvertFromSharedAEdwardsPointx86_64-no-tables»
    renaming «from» → ltFromFn, from_spec → ltFromFn_spec
set_option linter.style.longLine true
open «CoreOpsArithAddSharedAAffineNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
    renaming add → affineAdd, add_spec_point → affineAdd_spec
open «CoreOpsArithSubSharedAAffineNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
    renaming sub → affineSub, sub_spec_point → affineSub_spec
open «CoreOpsArithAddEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
    renaming add → edwardsAdd, add_spec_point → edwardsAdd_spec

namespace Curve25519Dalek.EdwardsOps

/-- The `«x86_64-no-tables»` point operations. -/
@[expose] noncomputable def X86NoTables : EdwardsOps where
  E := edwards.EdwardsPoint.«x86_64-no-tables»
  N := ProjectiveNielsPoint.«x86_64-no-tables»
  C := CompletedPoint.«x86_64-no-tables»
  Pr := ProjectivePoint.«x86_64-no-tables»
  An := AffineNielsPoint.«x86_64-no-tables»
  inhE := inferInstance
  inhN := inferInstance
  inhA := inferInstance
  reprN := inferInstance
  copyN := ProjectiveNielsPoint.«x86_64-no-tables».Insts.CoreMarkerCopy
  reprA := inferInstance
  copyA := AffineNielsPoint.«x86_64-no-tables».Insts.CoreMarkerCopy
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
  identity := edwards.EdwardsPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity
  add := edwardsAdd
  addAssign := «CoreOpsArithAddAssignEdwardsPointx86_64-no-tables».add_assign
  mulByPow2 := edwards.«EdwardsPointx86_64-no-tables».mul_by_pow_2
  addN := nielsAdd
  subN := nielsSub
  asExtended := «CompletedPointx86_64-no-tables».as_extended
  addA := affineAdd
  subA := affineSub
  asProjectiveNiels := edwards.«EdwardsPointx86_64-no-tables».as_projective_niels
  pIdentity := ProjectivePoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity
  pDouble := «ProjectivePointx86_64-no-tables».double
  cAsProjective := «CompletedPointx86_64-no-tables».as_projective
  pAsExtended := «ProjectivePointx86_64-no-tables».as_extended
  nafTable5 :=
    «CoreConvertFromSharedAEdwardsPointx86_64-no-tables».from
  ltSelect := window.LookupTable.select
    ProjectiveNielsPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity
    ProjectiveNielsPoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable
    (subtle.ConditionallyNegatable.Blanket
      ProjectiveNielsPoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable
      «CoreOpsArithNegProjectiveNielsPointx86_64-no-tables»)
  ltFrom := ltFromFn

theorem X86NoTables.identity_spec : X86NoTables.IdentitySpec :=
  edwards.EdwardsPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point

theorem X86NoTables.add_spec : X86NoTables.AddSpec :=
  edwardsAdd_spec

theorem X86NoTables.addAssign_spec : X86NoTables.AddAssignSpec :=
  «CoreOpsArithAddAssignEdwardsPointx86_64-no-tables».add_assign_spec_point

theorem X86NoTables.mulByPow2_spec : X86NoTables.MulByPow2Spec :=
  edwards.«EdwardsPointx86_64-no-tables».mul_by_pow_2_spec

theorem X86NoTables.addN_spec : X86NoTables.AddNSpec :=
  nielsAdd_spec

theorem X86NoTables.subN_spec : X86NoTables.SubNSpec :=
  nielsSub_spec

theorem X86NoTables.addA_spec : X86NoTables.AddASpec := affineAdd_spec

theorem X86NoTables.subA_spec : X86NoTables.SubASpec := affineSub_spec

theorem X86NoTables.asExtended_spec : X86NoTables.AsExtendedSpec :=
  «CompletedPointx86_64-no-tables».as_extended_spec_point

theorem X86NoTables.asProjectiveNiels_spec : X86NoTables.AsProjectiveNielsSpec :=
  edwards.«EdwardsPointx86_64-no-tables».as_projective_niels_spec_point

theorem X86NoTables.pIdentity_spec : X86NoTables.PIdentitySpec :=
  ProjectivePoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point

theorem X86NoTables.pDouble_spec : X86NoTables.PDoubleSpec :=
  «ProjectivePointx86_64-no-tables».double_spec_point

theorem X86NoTables.cAsProjective_spec : X86NoTables.CAsProjectiveSpec :=
  «CompletedPointx86_64-no-tables».as_projective_spec_point

theorem X86NoTables.pAsExtended_spec : X86NoTables.PAsExtendedSpec :=
  «ProjectivePointx86_64-no-tables».as_extended_spec_point

theorem X86NoTables.nafTable5_spec : X86NoTables.NafTable5Spec :=
  «CoreConvertFromSharedAEdwardsPointx86_64-no-tables».from_spec

theorem X86NoTables.ltSelect_spec : X86NoTables.LtSelectSpec :=
  window.«LookupTableProjectiveNielsPointx86_64-no-tables».select_spec

theorem X86NoTables.ltFrom_spec : X86NoTables.LtFromSpec :=
  ltFromFn_spec

end Curve25519Dalek.EdwardsOps

end

section
open Curve25519Dalek.«Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-tablesCompletedPointi686-tables»
    renaming add → nielsAdd, add_spec_point → nielsAdd_spec
open «CoreOpsArithSubSharedAProjectiveNielsPointi686-tablesCompletedPointi686-tables»
    renaming sub → nielsSub, sub_spec_point → nielsSub_spec
open Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts
open Curve25519Dalek.window.«NafLookupTable5ProjectiveNielsPointi686-tables».Insts
open Curve25519Dalek.«Shared0ProjectiveNielsPointi686-tables».Insts
set_option linter.style.longLine false
open Curve25519Dalek.window.«LookupTableProjectiveNielsPointi686-tables».Insts.«CoreConvertFromSharedAEdwardsPointi686-tables»
    renaming «from» → ltFromFn, from_spec → ltFromFn_spec
set_option linter.style.longLine true
open «CoreOpsArithAddSharedAAffineNielsPointi686-tablesCompletedPointi686-tables»
    renaming add → affineAdd, add_spec_point → affineAdd_spec
open «CoreOpsArithSubSharedAAffineNielsPointi686-tablesCompletedPointi686-tables»
    renaming sub → affineSub, sub_spec_point → affineSub_spec
open «CoreOpsArithAddEdwardsPointi686-tablesEdwardsPointi686-tables»
    renaming add → edwardsAdd, add_spec_point → edwardsAdd_spec

namespace Curve25519Dalek.EdwardsOps

/-- The `«i686-tables»` point operations. -/
@[expose] noncomputable def I686Tables : EdwardsOps where
  E := edwards.EdwardsPoint.«i686-tables»
  N := ProjectiveNielsPoint.«i686-tables»
  C := CompletedPoint.«i686-tables»
  Pr := ProjectivePoint.«i686-tables»
  An := AffineNielsPoint.«i686-tables»
  inhE := inferInstance
  inhN := inferInstance
  inhA := inferInstance
  reprN := inferInstance
  copyN := ProjectiveNielsPoint.«i686-tables».Insts.CoreMarkerCopy
  reprA := inferInstance
  copyA := AffineNielsPoint.«i686-tables».Insts.CoreMarkerCopy
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
  identity := edwards.EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity
  add := edwardsAdd
  addAssign := «CoreOpsArithAddAssignEdwardsPointi686-tables».add_assign
  mulByPow2 := edwards.«EdwardsPointi686-tables».mul_by_pow_2
  addN := nielsAdd
  subN := nielsSub
  asExtended := «CompletedPointi686-tables».as_extended
  addA := affineAdd
  subA := affineSub
  asProjectiveNiels := edwards.«EdwardsPointi686-tables».as_projective_niels
  pIdentity := ProjectivePoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity
  pDouble := «ProjectivePointi686-tables».double
  cAsProjective := «CompletedPointi686-tables».as_projective
  pAsExtended := «ProjectivePointi686-tables».as_extended
  nafTable5 :=
    «CoreConvertFromSharedAEdwardsPointi686-tables».from
  ltSelect := window.LookupTable.select
    ProjectiveNielsPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity
    ProjectiveNielsPoint.«i686-tables».Insts.SubtleConditionallySelectable
    (subtle.ConditionallyNegatable.Blanket
      ProjectiveNielsPoint.«i686-tables».Insts.SubtleConditionallySelectable
      «CoreOpsArithNegProjectiveNielsPointi686-tables»)
  ltFrom := ltFromFn

theorem I686Tables.identity_spec : I686Tables.IdentitySpec :=
  edwards.EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point

theorem I686Tables.add_spec : I686Tables.AddSpec :=
  edwardsAdd_spec

theorem I686Tables.addAssign_spec : I686Tables.AddAssignSpec :=
  «CoreOpsArithAddAssignEdwardsPointi686-tables».add_assign_spec_point

theorem I686Tables.mulByPow2_spec : I686Tables.MulByPow2Spec :=
  edwards.«EdwardsPointi686-tables».mul_by_pow_2_spec

theorem I686Tables.addN_spec : I686Tables.AddNSpec :=
  nielsAdd_spec

theorem I686Tables.subN_spec : I686Tables.SubNSpec :=
  nielsSub_spec

theorem I686Tables.addA_spec : I686Tables.AddASpec := affineAdd_spec

theorem I686Tables.subA_spec : I686Tables.SubASpec := affineSub_spec

theorem I686Tables.asExtended_spec : I686Tables.AsExtendedSpec :=
  «CompletedPointi686-tables».as_extended_spec_point

theorem I686Tables.asProjectiveNiels_spec : I686Tables.AsProjectiveNielsSpec :=
  edwards.«EdwardsPointi686-tables».as_projective_niels_spec_point

theorem I686Tables.pIdentity_spec : I686Tables.PIdentitySpec :=
  ProjectivePoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point

theorem I686Tables.pDouble_spec : I686Tables.PDoubleSpec :=
  «ProjectivePointi686-tables».double_spec_point

theorem I686Tables.cAsProjective_spec : I686Tables.CAsProjectiveSpec :=
  «CompletedPointi686-tables».as_projective_spec_point

theorem I686Tables.pAsExtended_spec : I686Tables.PAsExtendedSpec :=
  «ProjectivePointi686-tables».as_extended_spec_point

theorem I686Tables.nafTable5_spec : I686Tables.NafTable5Spec :=
  «CoreConvertFromSharedAEdwardsPointi686-tables».from_spec

theorem I686Tables.ltSelect_spec : I686Tables.LtSelectSpec :=
  window.«LookupTableProjectiveNielsPointi686-tables».select_spec

theorem I686Tables.ltFrom_spec : I686Tables.LtFromSpec :=
  ltFromFn_spec

end Curve25519Dalek.EdwardsOps

end

section
open Curve25519Dalek.«Shared0EdwardsPointi686-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»
    renaming add → nielsAdd, add_spec_point → nielsAdd_spec
open «CoreOpsArithSubSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»
    renaming sub → nielsSub, sub_spec_point → nielsSub_spec
open Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts
open Curve25519Dalek.window.«NafLookupTable5ProjectiveNielsPointi686-no-tables».Insts
open Curve25519Dalek.«Shared0ProjectiveNielsPointi686-no-tables».Insts
set_option linter.style.longLine false
open Curve25519Dalek.window.«LookupTableProjectiveNielsPointi686-no-tables».Insts.«CoreConvertFromSharedAEdwardsPointi686-no-tables»
    renaming «from» → ltFromFn, from_spec → ltFromFn_spec
set_option linter.style.longLine true
open «CoreOpsArithAddSharedAAffineNielsPointi686-no-tablesCompletedPointi686-no-tables»
    renaming add → affineAdd, add_spec_point → affineAdd_spec
open «CoreOpsArithSubSharedAAffineNielsPointi686-no-tablesCompletedPointi686-no-tables»
    renaming sub → affineSub, sub_spec_point → affineSub_spec
open «CoreOpsArithAddEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
    renaming add → edwardsAdd, add_spec_point → edwardsAdd_spec

namespace Curve25519Dalek.EdwardsOps

/-- The `«i686-no-tables»` point operations. -/
@[expose] noncomputable def I686NoTables : EdwardsOps where
  E := edwards.EdwardsPoint.«i686-no-tables»
  N := ProjectiveNielsPoint.«i686-no-tables»
  C := CompletedPoint.«i686-no-tables»
  Pr := ProjectivePoint.«i686-no-tables»
  An := AffineNielsPoint.«i686-no-tables»
  inhE := inferInstance
  inhN := inferInstance
  inhA := inferInstance
  reprN := inferInstance
  copyN := ProjectiveNielsPoint.«i686-no-tables».Insts.CoreMarkerCopy
  reprA := inferInstance
  copyA := AffineNielsPoint.«i686-no-tables».Insts.CoreMarkerCopy
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
  identity := edwards.EdwardsPoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity
  add := edwardsAdd
  addAssign := «CoreOpsArithAddAssignEdwardsPointi686-no-tables».add_assign
  mulByPow2 := edwards.«EdwardsPointi686-no-tables».mul_by_pow_2
  addN := nielsAdd
  subN := nielsSub
  asExtended := «CompletedPointi686-no-tables».as_extended
  addA := affineAdd
  subA := affineSub
  asProjectiveNiels := edwards.«EdwardsPointi686-no-tables».as_projective_niels
  pIdentity := ProjectivePoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity
  pDouble := «ProjectivePointi686-no-tables».double
  cAsProjective := «CompletedPointi686-no-tables».as_projective
  pAsExtended := «ProjectivePointi686-no-tables».as_extended
  nafTable5 :=
    «CoreConvertFromSharedAEdwardsPointi686-no-tables».from
  ltSelect := window.LookupTable.select
    ProjectiveNielsPoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity
    ProjectiveNielsPoint.«i686-no-tables».Insts.SubtleConditionallySelectable
    (subtle.ConditionallyNegatable.Blanket
      ProjectiveNielsPoint.«i686-no-tables».Insts.SubtleConditionallySelectable
      «CoreOpsArithNegProjectiveNielsPointi686-no-tables»)
  ltFrom := ltFromFn

theorem I686NoTables.identity_spec : I686NoTables.IdentitySpec :=
  edwards.EdwardsPoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point

theorem I686NoTables.add_spec : I686NoTables.AddSpec :=
  edwardsAdd_spec

theorem I686NoTables.addAssign_spec : I686NoTables.AddAssignSpec :=
  «CoreOpsArithAddAssignEdwardsPointi686-no-tables».add_assign_spec_point

theorem I686NoTables.mulByPow2_spec : I686NoTables.MulByPow2Spec :=
  edwards.«EdwardsPointi686-no-tables».mul_by_pow_2_spec

theorem I686NoTables.addN_spec : I686NoTables.AddNSpec :=
  nielsAdd_spec

theorem I686NoTables.subN_spec : I686NoTables.SubNSpec :=
  nielsSub_spec

theorem I686NoTables.addA_spec : I686NoTables.AddASpec := affineAdd_spec

theorem I686NoTables.subA_spec : I686NoTables.SubASpec := affineSub_spec

theorem I686NoTables.asExtended_spec : I686NoTables.AsExtendedSpec :=
  «CompletedPointi686-no-tables».as_extended_spec_point

theorem I686NoTables.asProjectiveNiels_spec : I686NoTables.AsProjectiveNielsSpec :=
  edwards.«EdwardsPointi686-no-tables».as_projective_niels_spec_point

theorem I686NoTables.pIdentity_spec : I686NoTables.PIdentitySpec :=
  ProjectivePoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point

theorem I686NoTables.pDouble_spec : I686NoTables.PDoubleSpec :=
  «ProjectivePointi686-no-tables».double_spec_point

theorem I686NoTables.cAsProjective_spec : I686NoTables.CAsProjectiveSpec :=
  «CompletedPointi686-no-tables».as_projective_spec_point

theorem I686NoTables.pAsExtended_spec : I686NoTables.PAsExtendedSpec :=
  «ProjectivePointi686-no-tables».as_extended_spec_point

theorem I686NoTables.nafTable5_spec : I686NoTables.NafTable5Spec :=
  «CoreConvertFromSharedAEdwardsPointi686-no-tables».from_spec

theorem I686NoTables.ltSelect_spec : I686NoTables.LtSelectSpec :=
  window.«LookupTableProjectiveNielsPointi686-no-tables».select_spec

theorem I686NoTables.ltFrom_spec : I686NoTables.LtFromSpec :=
  ltFromFn_spec

end Curve25519Dalek.EdwardsOps

end
