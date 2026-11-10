/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
import Mathlib.Tactic.ReduceModChar
public section

/-! # Certificates for the low-order `u`-coordinates (not audited)

Numeral facts in `ZMod p` used by `Curve25519.X25519.LowOrder`, with `A = 486662`,
`u₈ = 3256…3504` (the `u`-coordinate of a point of order `8`), `u₈' = 3938…5823` and
`r = 4880…9637`:

* Euler's criterion `x^((p-1)/2) = -1` for the non-squares `A² - 4`, `2 - A`, `u₈² + A u₈ + 1`,
  `u₈'² + A u₈' + 1` and `(2 - 2 r)² - 4`;
* `r² = A + 2`, `u₈ + u₈' = 2 + 2 r` and `u₈ u₈' = 1`;
* `(u² - 1)² = 4 u (u² + A u + 1)` at `u = u₈, u₈'` (`u(2 Q) = 1`).

The powers are evaluated by `norm_num` and `reduce_mod_char` after `p` is rewritten to its
numeral (`p_eq_numeral`). -/

namespace curve25519.Proofs

theorem a_sq_sub_four_pow : ((486662 : ZMod p) ^ 2 - 4) ^ (p / 2) = -1 := by
  rw [p_eq_numeral]
  norm_num
  reduce_mod_char

theorem two_sub_a_pow : ((2 : ZMod p) - 486662) ^ (p / 2) = -1 := by
  rw [p_eq_numeral]
  norm_num
  reduce_mod_char

theorem u8_sq_add_pow (u : ZMod p)
    (hu : u = 325606250916557431795983626356110631294008115727848805560023387167927233504) :
    (u ^ 2 + 486662 * u + 1) ^ (p / 2) = -1 := by
  rw [hu, p_eq_numeral]
  norm_num
  reduce_mod_char

theorem u8'_sq_add_pow (u : ZMod p)
    (hu : u = 39382357235489614581723060781553021112529911719440698176882885853963445705823) :
    (u ^ 2 + 486662 * u + 1) ^ (p / 2) = -1 := by
  rw [hu, p_eq_numeral]
  norm_num
  reduce_mod_char

theorem two_sub_two_r_sq_sub_four_pow (r : ZMod p)
    (hr : r = 48802004052532134862652268456126542835229456083994414501085850622543968879637) :
    ((2 - 2 * r) ^ 2 - 4) ^ (p / 2) = -1 := by
  rw [hr, p_eq_numeral]
  norm_num
  reduce_mod_char

theorem r_sq (r : ZMod p)
    (hr : r = 48802004052532134862652268456126542835229456083994414501085850622543968879637) :
    r ^ 2 = 486662 + 2 := by
  rw [hr, p_eq_numeral]
  norm_num
  reduce_mod_char

theorem u8_add_u8' (u u' r : ZMod p)
    (hu : u = 325606250916557431795983626356110631294008115727848805560023387167927233504)
    (hu' : u' = 39382357235489614581723060781553021112529911719440698176882885853963445705823)
    (hr : r = 48802004052532134862652268456126542835229456083994414501085850622543968879637) :
    u + u' = 2 + 2 * r := by
  rw [hu, hu', hr, p_eq_numeral]
  norm_num
  reduce_mod_char

theorem u8_mul_u8' (u u' : ZMod p)
    (hu : u = 325606250916557431795983626356110631294008115727848805560023387167927233504)
    (hu' : u' = 39382357235489614581723060781553021112529911719440698176882885853963445705823) :
    u * u' = 1 := by
  rw [hu, hu', p_eq_numeral]
  norm_num
  reduce_mod_char

theorem u8_dbl (u : ZMod p)
    (hu : u = 325606250916557431795983626356110631294008115727848805560023387167927233504) :
    (u ^ 2 - 1) ^ 2 = 4 * u * (u ^ 2 + 486662 * u + 1) := by
  rw [hu, p_eq_numeral]
  norm_num
  reduce_mod_char

theorem u8'_dbl (u : ZMod p)
    (hu : u = 39382357235489614581723060781553021112529911719440698176882885853963445705823) :
    (u ^ 2 - 1) ^ 2 = 4 * u * (u ^ 2 + 486662 * u + 1) := by
  rw [hu, p_eq_numeral]
  norm_num
  reduce_mod_char

end curve25519.Proofs
