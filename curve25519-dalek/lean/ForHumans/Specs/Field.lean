module
public import Proofs.Curve25519.Squares -- shake: keep
public section

namespace ZMod

variable {p : ℕ}

/-- `x` is *negative* (RFC 8032 §5.1.2, RFC 9496 §4.1): its canonical representative
`x.val ∈ [0, p)` is odd. -/
@[expose] def IsNeg (x : ZMod p) : Prop :=
  x.val % 2 = 1

instance instDecidableIsNeg (x : ZMod p) : Decidable x.IsNeg :=
  inferInstanceAs (Decidable (x.val % 2 = 1))

/-- `|x|` (RFC 9496's `CT_ABS`): `-x` if `x` is negative, `x` otherwise. -/
@[expose] def abs (x : ZMod p) : ZMod p :=
  if x.IsNeg then -x else x

end ZMod

namespace curve25519

open scoped Classical in
/-- RFC 9496 §4.2 `SQRT_RATIO_M1(u, v)`: `(true, r)` with `v r² = u` when `u / v` is a square,
`(false, r)` with `v r² = √-1 · u` otherwise, `r` non-negative in both cases; `(u = 0, 0)` when `v =
0`. Exposed; see `sqrtRatioM1_spec`. -/
@[expose] noncomputable def sqrtRatioM1 (u v : ZMod p) : Bool × ZMod p :=
  if v = 0 then (decide (u = 0), 0)
  else if h : IsSquare (u / v) then (true, (Classical.choose h).abs)
  else (false, (Classical.choose (isSquare_sqrtM1_mul_of_not_isSquare h)).abs)

end curve25519
