module
public import ForHumans.Specs.Field
public import EllipticCurve.TwistedEdwards.Group
public import Mathlib.Algebra.Module.Torsion.Basic
public section

namespace TwistedEdwardsModel

variable {p : ℕ} [Fact p.Prime] (E : TwistedEdwardsModel (ZMod p)) (bits : ℕ)

/-- RFC 8032 §5.1.2: the encoding of `(x, y)` is `y.val` with the sign of `x` (`1` iff `x.val`
is odd) in bit `bits`. -/
@[expose] def encode (P : E.Point) : ℕ :=
  P.y.val + 2 ^ bits * (if P.x.IsNeg then 1 else 0)

end TwistedEdwardsModel

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] (E : TwistedEdwardsModel F) [E.IsComplete]

/-- Two points are related iff they differ by 4-torsion: the equality test of Decaf/Ristretto
representatives. -/
@[expose] def Rel (P Q : E.Point) : Prop :=
  P - Q ∈ AddSubgroup.torsionBy E.Point 4

end TwistedEdwardsModel

namespace TwistedEdwardsModel

variable {F : Type u} [Field F]

/-- Affine Niels coordinates `(y + x, y - x, 2 d x y)` of an affine point (curve25519-dalek's
`AffineNielsPoint`). -/
@[ext] structure AffineNiels (E : TwistedEdwardsModel F) where
  /-- `y + x`. -/
  yPlusX : F
  /-- `y - x`. -/
  yMinusX : F
  /-- `2 d x y`. -/
  xy2d : F
  deriving DecidableEq

variable {E : TwistedEdwardsModel F}

namespace AffineNiels

/-- The `x`-coordinate `((y + x) - (y - x)) / 2` recovered from the Niels form. -/
@[expose] def x (P : E.AffineNiels) : F :=
  (P.yPlusX - P.yMinusX) / 2

/-- The `y`-coordinate `((y + x) + (y - x)) / 2` recovered from the Niels form. -/
@[expose] def y (P : E.AffineNiels) : F :=
  (P.yPlusX + P.yMinusX) / 2

/-- `(y + x, y - x, xy2d)` represents a point of `E`: `(x, y)` satisfies the equation (`x`, `y`
recovered from the Niels form) and `xy2d = 2 d x y`. -/
@[expose] def OnCurve (P : E.AffineNiels) : Prop :=
  E.Equation P.x P.y ∧ P.xy2d = 2 * E.d * P.x * P.y

open scoped Classical in
/-- The point represented by `(y + x, y - x, xy2d)`: `(x, y)` when `OnCurve`, and `(0, 1)`
otherwise. Hidden; characterised by `toPoint_x`, `toPoint_y`, `toPoint_of_not_onCurve`. -/
noncomputable def toPoint (P : E.AffineNiels) : E.Point :=
  if h : P.OnCurve then ⟨P.x, P.y, h.1⟩ else ⟨0, 1, E.equation_zero_one⟩

end AffineNiels

end TwistedEdwardsModel
