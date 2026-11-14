/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Ristretto.Encoding.Defs
import all Curve25519.Basic
public section

/-! # Certificates for the ristretto255 encoding of the basepoint (not audited)

Kernel computations (`decide +kernel`) of RFC 9496 §4.3.2 on the coordinates of the Edwards
basepoint: the inverse square root `invsqrt` of `(1 + y)(1 - y)(x y)²` is exhibited as a
numeral (`sqrtRatioM1` is not computable: it is characterised by `sqrtRatioM1_one_eq_of_mul_sq_eq`),
and the rest of the encoding (`encodeRepOf`) is evaluated by the kernel. `Curve25519.Basic` is
imported with `import all` so that the kernel can unfold `p`, `sqrtM1` and `invsqrtAMinusD`.
The result is stated for any point with the basepoint's coordinates and instantiated by
`Curve25519.Ristretto.Encoding` (`encodeRepNat_basepoint`, RFC 9496 §A.1); `encodeRepNat_of_coords`
also serves the test vectors. -/

namespace curve25519.Proofs

/-- The inverse square root of `(1 + y)(1 - y)(x y)²` at the basepoint, as a numeral. -/
private theorem basepoint_invsqrt :
    (1 + (46316835694926478169428394003475163141307993866256225615783033603165251855960 :
        ZMod p)) *
      (1 - (46316835694926478169428394003475163141307993866256225615783033603165251855960 :
        ZMod p)) *
      ((15112221349535400772501151409588531511454012693041857206046113283949847762202 : ZMod p) *
        46316835694926478169428394003475163141307993866256225615783033603165251855960) ^ 2 *
      (52572753176437111631691385822184065804252865134316606714987751091199353072154 : ZMod p)
        ^ 2 = 1 := by
  decide +kernel

private theorem basepoint_invsqrt_not_isNeg :
    ¬ (52572753176437111631691385822184065804252865134316606714987751091199353072154 :
      ZMod p).IsNeg := by
  decide +kernel

/-- RFC 9496 §4.3.2 after `SQRT_RATIO_M1`, on the coordinates `(x, y)` with the inverse square
root `r` of `(1 + y)(1 - y)(x y)²` given: what the kernel evaluates. Exposed, for the kernel. -/
@[expose] noncomputable def encodeRepOf (x y r : ZMod p) : ℕ :=
  let t := x * y
  let u1 := (1 + y) * (1 - y)
  let u2 := x * y
  let den1 := r * u1
  let den2 := r * u2
  let zInv := den1 * den2 * t
  let ix := x * sqrtM1
  let iy := y * sqrtM1
  let enchanted := den1 * invsqrtAMinusD
  let rotate := (t * zInv).IsNeg
  let x' := if rotate then iy else x
  let y' := if rotate then ix else y
  let denInv := if rotate then enchanted else den2
  let y'' := if (x' * zInv).IsNeg then -y' else y'
  (denInv * (1 - y'')).abs.val

/-- `encodeRepNat` of a point with given coordinates, from the inverse square root `r` of
`(1 + y)(1 - y)(x y)²` as a numeral and a kernel evaluation of the rest (`encodeRepOf`). -/
theorem encodeRepNat_of_coords {x y r : ZMod p} {n : ℕ} (P : edwards.Point) (hx : P.x = x)
    (hy : P.y = y) (hr : (1 + y) * (1 - y) * (x * y) ^ 2 * r ^ 2 = 1) (hneg : ¬ r.IsNeg)
    (hc : encodeRepOf x y r = n) : Ristretto.encodeRepNat P = n := by
  rw [Ristretto.encodeRepNat_eq]
  dsimp only
  rw [hx, hy, sqrtRatioM1_one_eq_of_mul_sq_eq hr hneg]
  exact hc

/-- **RFC 9496 §A.1**: the encoding of the basepoint is `e2f2ae0a 6abc4e71 a884a961 c500515f
58e30b6a a582dd8d b6a65945 e08d2d76` (little-endian). -/
theorem encodeRepNat_of_basepoint_coords (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    Ristretto.encodeRepNat P =
      53453403443306840533278073560698739391446669128918427283046925944918568268514 :=
  encodeRepNat_of_coords P hx hy basepoint_invsqrt basepoint_invsqrt_not_isNeg (by decide +kernel)

end curve25519.Proofs
