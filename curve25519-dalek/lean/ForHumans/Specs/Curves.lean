/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ForHumans.Specs.Constants
public import Proofs.Curve25519.Prime
public import Mathlib.Algebra.Field.ZMod
public import EllipticCurve
public section

/-! # edwards25519 and curve25519

The twisted Edwards model `-x² + y² = 1 + d x² y²` (RFC 8032 §5.1) and the Montgomery model
`v² = u³ + A u² + u` (RFC 7748 §4.1) over `ZMod p`. Their points, with their group law, are those
of the `EllipticCurve` library: an Edwards point is an `(x, y)` on the curve, and the group law
is the one transported from Mathlib's Weierstrass curves. -/

namespace curve25519

/-- The twisted Edwards model `-x² + y² = 1 + d x² y²` of curve25519 (edwards25519). -/
noncomputable def edwards : TwistedEdwardsModel (ZMod p) := ⟨a, d⟩

/-- The Montgomery model `v² = u³ + A u² + u` of curve25519. -/
def montgomery : MontgomeryModel (ZMod p) := ⟨(A : ZMod p), 1⟩

end curve25519
