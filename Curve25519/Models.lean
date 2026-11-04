/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Models.Field.Sign
public import Curve25519.Models.TwistedEdwards.Coords.Defs
public import Curve25519.Models.TwistedEdwards.Coords.Lemmas
public import Curve25519.Models.TwistedEdwards.Formulas.Defs
public import Curve25519.Models.TwistedEdwards.Formulas.Lemmas
public import Curve25519.Models.TwistedEdwards.Encoding.Defs
public import Curve25519.Models.TwistedEdwards.Encoding.Lemmas
public import Curve25519.Models.TwistedEdwards.Decaf.Defs
public import Curve25519.Models.TwistedEdwards.Decaf.Lemmas

/-! # Niels coordinates, encodings and the Decaf relation on elliptic-curve models

What the implementation needs on top of the models of the `EllipticCurve` library (which provides
the projective, extended and completed coordinates, their formulas, and the Montgomery ladder),
stated for any field (or any `ZMod p`) rather than for curve25519, under the library's namespaces
(`TwistedEdwardsModel`, `ZMod`). What belongs in the library itself is staged separately in
`Curve25519.ToEllipticCurve`; what is here is specific to the implementation or to the
cryptographic encodings:

* `Field.Sign`: the sign `ZMod.IsNeg` (odd canonical representative) and `ZMod.abs`;
* `TwistedEdwards.Coords`: the Niels coordinates (`toPoint`, `OnCurve`);
* `TwistedEdwards.Formulas`: the mixed additions with Niels points;
* `TwistedEdwards.Encoding`: the RFC 8032 encoding of points (`encode`, `decode`);
* `TwistedEdwards.Decaf`: the relation `Rel` of Decaf/Ristretto (difference in the 4-torsion),
  in coordinates. -/
