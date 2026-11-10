/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Models.TwistedEdwards.Coords.Defs
public section

/-! # Twisted Edwards models: mixed additions with Niels points

The four mixed additions of curve25519-dalek's `curve_models.rs`, as exposed formulas, exactly as
the code computes them: `Extended.addProjectiveNiels`, `Extended.subProjectiveNiels`,
`Extended.addAffineNiels`, `Extended.subAffineNiels` (`Add`/`Sub` of `EdwardsPoint` with a Niels
point), all into completed coordinates. These are the `a = -1` formulas of
Hisil–Wong–Carter–Dawson 2008; they are defined for every model and correct when `a = -1`
(`Curve25519.Models.TwistedEdwards.Formulas.Lemmas`).

The other formulas the code uses (projective doubling, the complete extended addition, doubling
and scalar multiplication, the zero test) are those of
`EllipticCurve.TwistedEdwards.Formulas.Defs`. -/

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F}

namespace Extended

/-- Mixed addition of an extended point and a projective Niels point for `a = -1`
(`&EdwardsPoint + &ProjectiveNielsPoint`): `PP = (Y₁ + X₁) (Y₂ + X₂)`,
`MM = (Y₁ - X₁) (Y₂ - X₂)`, `TT2d = T₁ T2d₂`, `ZZ2 = 2 Z₁ Z₂`; the result is
`(PP - MM, PP + MM, ZZ2 + TT2d, ZZ2 - TT2d)`. -/
@[expose] def addProjectiveNiels (P : E.Extended) (Q : E.ProjectiveNiels) : E.Completed :=
  let Y_plus_X := P.Y + P.X
  let Y_minus_X := P.Y - P.X
  let PP := Y_plus_X * Q.YPlusX
  let MM := Y_minus_X * Q.YMinusX
  let TT2d := P.T * Q.T2d
  let ZZ := P.Z * Q.Z
  let ZZ2 := ZZ + ZZ
  ⟨PP - MM, PP + MM, ZZ2 + TT2d, ZZ2 - TT2d⟩

/-- Mixed subtraction of a projective Niels point from an extended point for `a = -1`
(`&EdwardsPoint - &ProjectiveNielsPoint`): `PM = (Y₁ + X₁) (Y₂ - X₂)`,
`MP = (Y₁ - X₁) (Y₂ + X₂)`, `TT2d = T₁ T2d₂`, `ZZ2 = 2 Z₁ Z₂`; the result is
`(PM - MP, PM + MP, ZZ2 - TT2d, ZZ2 + TT2d)`. -/
@[expose] def subProjectiveNiels (P : E.Extended) (Q : E.ProjectiveNiels) : E.Completed :=
  let Y_plus_X := P.Y + P.X
  let Y_minus_X := P.Y - P.X
  let PM := Y_plus_X * Q.YMinusX
  let MP := Y_minus_X * Q.YPlusX
  let TT2d := P.T * Q.T2d
  let ZZ := P.Z * Q.Z
  let ZZ2 := ZZ + ZZ
  ⟨PM - MP, PM + MP, ZZ2 - TT2d, ZZ2 + TT2d⟩

/-- Mixed addition of an extended point and an affine Niels point for `a = -1`
(`&EdwardsPoint + &AffineNielsPoint`): `PP = (Y₁ + X₁) (y₂ + x₂)`,
`MM = (Y₁ - X₁) (y₂ - x₂)`, `Txy2d = T₁ xy2d₂`, `Z2 = 2 Z₁`; the result is
`(PP - MM, PP + MM, Z2 + Txy2d, Z2 - Txy2d)`. -/
@[expose] def addAffineNiels (P : E.Extended) (Q : E.AffineNiels) : E.Completed :=
  let Y_plus_X := P.Y + P.X
  let Y_minus_X := P.Y - P.X
  let PP := Y_plus_X * Q.yPlusX
  let MM := Y_minus_X * Q.yMinusX
  let Txy2d := P.T * Q.xy2d
  let Z2 := P.Z + P.Z
  ⟨PP - MM, PP + MM, Z2 + Txy2d, Z2 - Txy2d⟩

/-- Mixed subtraction of an affine Niels point from an extended point for `a = -1`
(`&EdwardsPoint - &AffineNielsPoint`): `PM = (Y₁ + X₁) (y₂ - x₂)`,
`MP = (Y₁ - X₁) (y₂ + x₂)`, `Txy2d = T₁ xy2d₂`, `Z2 = 2 Z₁`; the result is
`(PM - MP, PM + MP, Z2 - Txy2d, Z2 + Txy2d)`. -/
@[expose] def subAffineNiels (P : E.Extended) (Q : E.AffineNiels) : E.Completed :=
  let Y_plus_X := P.Y + P.X
  let Y_minus_X := P.Y - P.X
  let PM := Y_plus_X * Q.yMinusX
  let MP := Y_minus_X * Q.yPlusX
  let Txy2d := P.T * Q.xy2d
  let Z2 := P.Z + P.Z
  ⟨PM - MP, PM + MP, Z2 - Txy2d, Z2 + Txy2d⟩

end Extended

end TwistedEdwardsModel
