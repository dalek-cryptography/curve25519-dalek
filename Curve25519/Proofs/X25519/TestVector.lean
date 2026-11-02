/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
import all Curve25519.Basic
public section

/-! # The RFC 7748 test vectors for X25519 (not audited)

Kernel evaluations (`decide +kernel`) of the 255-step Montgomery ladder on the test vectors of
RFC 7748 §5.2 and §6.1, as little-endian numbers: a regression test of `x25519`. The ladder is
run in projective form (`XZ.ladderXZ`, no field inversion) and its result `(U : W)` is checked
against the expected coordinate `e` as `U = e W ∧ W ≠ 0`, since the kernel cannot evaluate the
inverse in `ZMod p`; `Curve25519.Basic` is imported with `import all` so that the kernel can
unfold `p`. -/

namespace curve25519.Proofs

open MontgomeryModel

/-- `x25519 k u = e` from a kernel check of the projective ladder result. -/
private theorem x25519_eq_of_ladderXZ {k u e : ℕ}
    (h : (XZ.ladderXZ 121665 255 (clamp k) (decodeU u)).U =
        (e : ZMod p) * (XZ.ladderXZ 121665 255 (clamp k) (decodeU u)).W ∧
      (XZ.ladderXZ 121665 255 (clamp k) (decodeU u)).W ≠ 0) (he : e < p) :
    x25519 k u = e := by
  unfold x25519 MontgomeryModel.ladder XZ.ladder
  rw [montgomery_a24_eq, XZ.toU, h.1, mul_div_assoc, div_self h.2, mul_one]
  exact ZMod.val_natCast_of_lt he

/-- RFC 7748 §5.2, first vector: scalar `a546e36b…`, `u` `e6db6867…`, output `c3da5537…`. -/
theorem x25519_vector₁ :
    x25519 88925887110773138616681052956207043583107764937498542285260013040410376226469
        34426434033919594451155107781188821651316167215306631574996226621102155684838 =
      37325765543539916631701301279660700968428932651319597985674090122993663859395 :=
  x25519_eq_of_ladderXZ (by decide +kernel) (by rw [p_eq_numeral]; decide)

/-- RFC 7748 §5.2, second vector: scalar `4b66e9d4…`, `u` `e5210f12…`, output `95cbde94…`. -/
theorem x25519_vector₂ :
    x25519 6208869506345768410841466502331656783811117849709423753404619313487976949323
        66779901969842027605876251890954603246052331132842480964984187926304357556709 =
      39566196721700740701373067725336211924689549479508623342842086701180565506965 :=
  x25519_eq_of_ladderXZ (by decide +kernel) (by rw [p_eq_numeral]; decide)

/-- RFC 7748 §6.1: Alice's public key `X25519(a, 9)` for `a = 77076d0a…` is `8520f009…`. -/
theorem x25519_alice_public :
    x25519 19076158533740022697853188432810029468508100820210985396154491514718125885303 9 =
      48084050389777770101701157326923977117307187144965043058462938058489685090437 :=
  x25519_eq_of_ladderXZ (by decide +kernel) (by rw [p_eq_numeral]; decide)

/-- RFC 7748 §5.2, the iterated test after one iteration: `X25519(9, 9)` is `422c8e7a…`. -/
theorem x25519_one_iteration :
    x25519 9 9 =
      54815864700279561125610391355931320566748822376190344121911385527384361806914 :=
  x25519_eq_of_ladderXZ (by decide +kernel) (by rw [p_eq_numeral]; decide)

/-- RFC 7748 §6.1: Bob's public key `X25519(b, 9)` for `b = 5dab087e…` is `de9edb7d…`. -/
theorem x25519_bob_public :
    x25519 106690238676031959364154629127743819238817784511314751294525304279539011595101 9 =
      35809631094079244041211258971985475468665640815735853089228998203411133079262 :=
  x25519_eq_of_ladderXZ (by decide +kernel) (by rw [p_eq_numeral]; decide)

/-- RFC 7748 §6.1: the shared secret `X25519(a, X25519(b, 9))` is `4a5d9d5b…` (Alice's side;
RFC 7748 gives the same value for Bob's side `X25519(b, X25519(a, 9))`, not checked here). -/
theorem x25519_shared_secret :
    x25519 19076158533740022697853188432810029468508100820210985396154491514718125885303
        35809631094079244041211258971985475468665640815735853089228998203411133079262 =
      29893438142586401087946310744922998080771935139441267052026283852717044358474 :=
  x25519_eq_of_ladderXZ (by decide +kernel) (by rw [p_eq_numeral]; decide)

end curve25519.Proofs
