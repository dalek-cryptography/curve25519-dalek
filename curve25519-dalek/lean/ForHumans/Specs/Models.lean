/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ForHumans.Specs.Field
public import EllipticCurve.TwistedEdwards.Group
public import Mathlib.Algebra.Module.Torsion.Basic
public section

/-! # Twisted Edwards models: encoding and the Ristretto relation

Two definitions over any twisted Edwards model `E` (from the `EllipticCurve` library) that the
library does not have yet: the RFC 8032 encoding of a point as a number, and the relation whose
classes are the elements of the Decaf/Ristretto quotient. -/

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
