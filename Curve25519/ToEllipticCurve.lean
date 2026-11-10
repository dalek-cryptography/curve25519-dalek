/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.ToEllipticCurve.Montgomery.XOnly
public import Curve25519.ToEllipticCurve.TwistedEdwards.Defs
public import Curve25519.ToEllipticCurve.TwistedEdwards.Even
public import Curve25519.ToEllipticCurve.TwistedEdwards.Formulas.Lemmas
public import Curve25519.ToEllipticCurve.TwistedEdwards.Lemmas

/-! # Material staged for the `EllipticCurve` library

Definitions and results about elliptic-curve models that depend on nothing specific to
curve25519 or to the implementation, written in the library's namespaces and conventions, ready
to be proposed upstream. Once the library provides a feature, its module here is deleted and the
importers switch to the library.

* `Montgomery.XOnly`: the doubling formula on `u`-coordinates (`dblU`), x-only multiplication by
  `2 ^ n` as its iterate;
* `TwistedEdwards.Defs`, `TwistedEdwards.Lemmas`: the equation solved for `x²` (`xSq`), the
  points with a given `y`, the bound `|E| ≤ 2 |F|`, the translation by `(0, -1)`;
* `TwistedEdwards.Even`: the 2-descent detects evenness when the even points have index `2`;
* `TwistedEdwards.Formulas.Lemmas`: scalar multiplication in extended coordinates against the group
  law, for kernel certificates. -/
