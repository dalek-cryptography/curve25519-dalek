module
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
public section

namespace curve25519

/-- The field prime `p = 2^255 - 19`. -/
def p : ℕ := 2 ^ 255 - 19

/-- The order of the prime-order subgroup, `L = 2^252 + 27742317777372353535851937790883648493`. -/
def L : ℕ := 2 ^ 252 + 27742317777372353535851937790883648493

/-- The Edwards coefficient `a = -1`. -/
noncomputable def a : ZMod p := -1

/-- The Edwards coefficient `d = -121665 / 121666`. -/
noncomputable def d : ZMod p := -121665 * (121666 : ZMod p)⁻¹

/-- The Montgomery coefficient `A = 486662`. -/
def A : ℕ := 486662

/-- The square root of `-1` used by RFC 8032 (§5.1.3), `2^((p-1)/4) mod p`, as a natural number
below `p`. -/
def sqrtM1 : ℕ := 19681161376707505956807079304988542015446066515923890162744021073123829784752

/-- A square root of `-(A + 2) = -486664` modulo `p`, as a natural number below `p`: the scaling
`v ↦ sqrtNegAAddTwo · v` identifies the Montgomery model `(A, 1)` with the Montgomery model
`(A, 4 / (a - d))` of the Edwards model (`sqrtNegAAddTwo_sq`, `four_eq_sqrtNegAAddTwo_sq_mul`).
Of the two roots, the odd one: RFC 7748 §4.1 does not name the root, but its base points fix it,
since the map `v = √(-486664) · u / x` must send the Edwards base point to `(9, V(P))`
(`curve25519.v_montgomeryBasepoint`). -/
def sqrtNegAAddTwo : ℕ :=
  51042569399160536130206135233146329284152202253034631822681833788666877215207

/-- RFC 9496 §4.1 `SQRT_AD_MINUS_ONE`: a square root of `a d - 1 = -d - 1` modulo `p`, as a
natural number below `p` (`sqrtAdMinusOne_sq`). The RFC's value is odd, i.e. negative in the
sense of `ZMod.IsNeg` (`sqrtAdMinusOne_mod_two`). -/
def sqrtAdMinusOne : ℕ :=
  25063068953384623474111414158702152701244531502492656460079210482610430750235

/-- RFC 9496 §4.1 `INVSQRT_A_MINUS_D`: the inverse of a square root of `a - d = -1 - d` modulo
`p`, as a natural number below `p` (`invsqrtAMinusD_sq_mul`); even (`invsqrtAMinusD_mod_two`). -/
def invsqrtAMinusD : ℕ :=
  54469307008909316920995813868745141605393597292927456921205312896311721017578

/-- RFC 9496 §4.1 `ONE_MINUS_D_SQ = 1 - d²` modulo `p`, as a natural number below `p`
(`oneMinusDSq_eq`). -/
def oneMinusDSq : ℕ :=
  1159843021668779879193775521855586647937357759715417654439879720876111806838

/-- RFC 9496 §4.1 `D_MINUS_ONE_SQ = (d - 1)²` modulo `p`, as a natural number below `p`
(`dMinusOneSq_eq`). -/
def dMinusOneSq : ℕ :=
  40440834346308536858101042469323190826248399146238708352240133220865137265952

end curve25519
