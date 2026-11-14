/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.TwistedEdwards.Group
public import Mathlib.Algebra.Module.Torsion.Basic
public section

/-! # The Decaf/Ristretto relation on a complete twisted Edwards model: definition

The equality test of Decaf/Ristretto representatives (Hamburg, *Decaf: eliminating cofactors
through point compression*; RFC 9496), independent of any encoding: for a complete twisted
Edwards model `E`, two points are related (`E.Rel`) iff they differ by an element of the
4-torsion, Mathlib's `AddSubgroup.torsionBy E.Point 4 = {P | 4 • P = 0}`.

`Rel` is exposed (specifications unfold it). The characterising lemmas are in
`Curve25519.Models.TwistedEdwards.Decaf.Lemmas`. -/

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] (E : TwistedEdwardsModel F) [E.IsComplete]

/-- Two points are related iff they differ by 4-torsion: the equality test of Decaf/Ristretto
representatives. -/
@[expose] def Rel (P Q : E.Point) : Prop :=
  P - Q ∈ AddSubgroup.torsionBy E.Point 4

end TwistedEdwardsModel
