/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
import all Curve25519.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ReduceModChar
public section

/-! # The 2-descent certificate of the 8-torsion (not audited)

Euler's criterion for `1 - y²` at the point of order `8`, `y = 55188…417927`:
`(1 - y²)^((p-1)/2) = -1`, so `1 - y²` is not a square (`not_isSquare_one_sub_torsion8_y_sq` in
`Curve25519.Ristretto.Even`): the point of order `8` is not even. The computation rewrites `p` to
its numeral, so this module imports `Curve25519.Basic` only (with `import all`): with the field
structure of `ZMod p` in scope (`Fact p.Prime`) the rewrite would not typecheck. -/

namespace curve25519.Proofs

theorem one_sub_torsion8_y_sq_pow_p_div_two :
    (1 - ((55188659117513257062467267217118295137698188065244968500265048394206261417927 : ℕ) :
      ZMod p) ^ 2) ^ (p / 2) = -1 := by
  rw [p_eq_numeral]
  norm_num
  reduce_mod_char

end curve25519.Proofs
