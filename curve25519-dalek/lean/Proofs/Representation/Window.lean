/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Representation.CurveModels
public import ForHumans.Specs.Representation
public section

/-! # The projective Niels points as table entries

The `PointRepr` instances of the four `ProjectiveNielsPoint` structures, the entries of the
tables that `EdwardsPoint::mul` and the multiscalar multiplications build on the fly. The class,
the table predicates and the instances for `AffineNielsPoint` are in
`ForHumans/Specs/Representation/` (`Window.lean`, `CurveModels.lean`). -/

open Aeneas Aeneas.Std

namespace Curve25519Dalek

namespace backend.serial.curve_models

noncomputable instance ProjectiveNielsPoint.«x86_64-tables».instPointRepr :
    PointRepr ProjectiveNielsPoint.«x86_64-tables» where
  OnCurve := ProjectiveNielsPoint.«x86_64-tables».OnCurve
  toPoint := ProjectiveNielsPoint.«x86_64-tables».toPoint
  LimbsLt := ProjectiveNielsPoint.«x86_64-tables».LimbsLt

noncomputable instance ProjectiveNielsPoint.«i686-tables».instPointRepr :
    PointRepr ProjectiveNielsPoint.«i686-tables» where
  OnCurve := ProjectiveNielsPoint.«i686-tables».OnCurve
  toPoint := ProjectiveNielsPoint.«i686-tables».toPoint
  LimbsLt := ProjectiveNielsPoint.«i686-tables».LimbsLt

noncomputable instance ProjectiveNielsPoint.«x86_64-no-tables».instPointRepr :
    PointRepr ProjectiveNielsPoint.«x86_64-no-tables» where
  OnCurve := ProjectiveNielsPoint.«x86_64-no-tables».OnCurve
  toPoint := ProjectiveNielsPoint.«x86_64-no-tables».toPoint
  LimbsLt := ProjectiveNielsPoint.«x86_64-no-tables».LimbsLt

noncomputable instance ProjectiveNielsPoint.«i686-no-tables».instPointRepr :
    PointRepr ProjectiveNielsPoint.«i686-no-tables» where
  OnCurve := ProjectiveNielsPoint.«i686-no-tables».OnCurve
  toPoint := ProjectiveNielsPoint.«i686-no-tables».toPoint
  LimbsLt := ProjectiveNielsPoint.«i686-no-tables».LimbsLt

end backend.serial.curve_models

end Curve25519Dalek
