/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Models.Field.Sign
public import Curve25519.ToEllipticCurve.TwistedEdwards.Defs
public section

/-! # Point encoding of a twisted Edwards model over `ZMod p`: definitions

The RFC 8032 (§5.1.2, §5.1.3) point encoding, generic in the model `E` over `ZMod p` and in the
width `bits` of the `y`-coordinate (`255` for edwards25519, `455` for edwards448): a point
`(x, y)` is encoded as the natural number `y.val + 2 ^ bits * sign(x)` (`encode`), where
`sign(x)` is `1` iff `x` is negative (`ZMod.IsNeg`: `x.val` odd); the encoding is the
little-endian byte string of this number.

Decoding (`decode`) is the strict RFC 8032 procedure: split `n` into `y := n % 2 ^ bits` and
the sign bit `s := n / 2 ^ bits`; reject (`none`) if `n` has more than `bits + 1` bits or
`y ≥ p` (non-canonical `y`); recover `x` from `x² = (y² - 1) / (d y² - a)` (`xSq`): reject if
there is no square root, or if the only root is `x = 0` while `s = 1`; otherwise return the
root whose sign is `s`. The hidden body phrases this as "the `x` with `(x, y)` on the model and
sign `s`", which is unique (`decode_eq_some_iff` in
`Curve25519.Models.TwistedEdwards.Encoding.Lemmas`); the characterisation by the rejection reasons
is `decode_eq_none_iff`. The strict decoder accepts exactly the encodings:
`decode n = some P ↔ encode P = n` (`decode_eq_some_iff_encode_eq`).

`encode` is an exposed formula and `decode` is hidden; `xSq` is that of
`Curve25519.ToEllipticCurve.TwistedEdwards.Defs`. The hypothesis `p < 2 ^ bits`
(so that `y.val` fits in `bits` bits) is taken as `[Fact (p < 2 ^ bits)]` only where it is
needed. -/

namespace TwistedEdwardsModel

variable {p : ℕ} [Fact p.Prime] (E : TwistedEdwardsModel (ZMod p)) (bits : ℕ)

/-- RFC 8032 §5.1.2: the encoding of `(x, y)` is `y.val` with the sign of `x` (`1` iff `x.val`
is odd) in bit `bits`. -/
@[expose] def encode (P : E.Point) : ℕ :=
  P.y.val + 2 ^ bits * (if P.x.IsNeg then 1 else 0)

open scoped Classical in
/-- RFC 8032 §5.1.3, strict: `y := n % 2 ^ bits`, sign `s := n / 2 ^ bits`; `none` if
`n ≥ 2 ^ (bits + 1)` or `y ≥ p`, or if no `x` with `(x, y)` on the model has sign `s` (no
square root of `xSq y`, or `x = 0` with `s = 1`); otherwise the point `(x, y)` with that `x`. -/
noncomputable def decode (n : ℕ) : Option E.Point :=
  if n < 2 ^ (bits + 1) ∧ n % 2 ^ bits < p then
    if h : ∃ x : ZMod p, E.Equation x ((n % 2 ^ bits : ℕ) : ZMod p) ∧
        (x.IsNeg ↔ n / 2 ^ bits = 1) then
      some ⟨Classical.choose h, ((n % 2 ^ bits : ℕ) : ZMod p), (Classical.choose_spec h).1⟩
    else none
  else none

end TwistedEdwardsModel
