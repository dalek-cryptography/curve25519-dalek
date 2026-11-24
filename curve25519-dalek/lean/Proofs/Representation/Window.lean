module
public import Proofs.Representation.CurveModels
public import ForHumans.Specs.Representation
public section

open Aeneas Aeneas.Std

namespace Curve25519Dalek

namespace backend.serial.curve_models

noncomputable instance ProjectiveNielsPoint.«64bit-tables».instPointRepr :
    PointRepr ProjectiveNielsPoint.«64bit-tables» where
  OnCurve := ProjectiveNielsPoint.«64bit-tables».OnCurve
  toPoint := ProjectiveNielsPoint.«64bit-tables».toPoint
  LimbsLt := ProjectiveNielsPoint.«64bit-tables».LimbsLt

noncomputable instance ProjectiveNielsPoint.«32bit-tables».instPointRepr :
    PointRepr ProjectiveNielsPoint.«32bit-tables» where
  OnCurve := ProjectiveNielsPoint.«32bit-tables».OnCurve
  toPoint := ProjectiveNielsPoint.«32bit-tables».toPoint
  LimbsLt := ProjectiveNielsPoint.«32bit-tables».LimbsLt

noncomputable instance ProjectiveNielsPoint.«64bit-notables».instPointRepr :
    PointRepr ProjectiveNielsPoint.«64bit-notables» where
  OnCurve := ProjectiveNielsPoint.«64bit-notables».OnCurve
  toPoint := ProjectiveNielsPoint.«64bit-notables».toPoint
  LimbsLt := ProjectiveNielsPoint.«64bit-notables».LimbsLt

noncomputable instance ProjectiveNielsPoint.«32bit-notables».instPointRepr :
    PointRepr ProjectiveNielsPoint.«32bit-notables» where
  OnCurve := ProjectiveNielsPoint.«32bit-notables».OnCurve
  toPoint := ProjectiveNielsPoint.«32bit-notables».toPoint
  LimbsLt := ProjectiveNielsPoint.«32bit-notables».LimbsLt

end backend.serial.curve_models

end Curve25519Dalek
