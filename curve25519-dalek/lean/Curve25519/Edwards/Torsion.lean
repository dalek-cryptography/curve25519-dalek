/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basic
import Curve25519.Proofs.Edwards.Certs
import Curve25519.ToEllipticCurve.TwistedEdwards.Lemmas
import Mathlib.Tactic.Abel
public section

/-! # The 8-torsion

The point `torsion8` of order `8`: the point `T` with `2 • T = (-√-1, 0)` and `x` non-negative
(`eq_torsion8_iff`; `√-1` is RFC 8032's `sqrtM1`). It is dalek's `EIGHT_TORSION[1]`, and the
eight torsion points are its multiples `i • T`, `i < 8`, in the order of dalek's `EIGHT_TORSION`
array: `2 • T` and `6 • T` are `(∓√-1, 0)`, `4 • T = (0, -1)`, and `3 • T`, `5 • T`, `7 • T` are
`(x, -y)`, `(-x, -y)`, `(-x, y)` for `T = (x, y)`. The definition is hidden; the coordinates are
`torsion8_x_eq`, `torsion8_y_eq`, `two_nsmul_torsion8_x_eq`, ….

Only `T` being on the model and the coordinates of `2 • T` and `4 • T` are kernel certificates
(`Curve25519.Proofs.Edwards.Certs`, not audited). The rest follows from the group law:
`4 • T = (0, -1)` has order `2`, so `8 • T = 0` and `4 • T ≠ 0`; adding `(0, -1)` negates both
coordinates, so `5 • T = (-x, -y)`; and `3 • T`, `6 • T`, `7 • T` are the negations of `5 • T`,
`2 • T`, `T`. -/

namespace curve25519

/-- Dalek's `EIGHT_TORSION[1]` is on the model. -/
theorem torsion8_equation : edwards.Equation
    14399317868200118260347934320527232580618823971194345261214217575416788799818
    55188659117513257062467267217118295137698188065244968500265048394206261417927 :=
  Proofs.torsion8_equation

/-- The point of order `8` with `2 • T = (-√-1, 0)` and `x` non-negative (`eq_torsion8_iff`):
dalek's `EIGHT_TORSION[1]`. -/
noncomputable def torsion8 : edwards.Point :=
  ⟨14399317868200118260347934320527232580618823971194345261214217575416788799818,
    55188659117513257062467267217118295137698188065244968500265048394206261417927,
    torsion8_equation⟩

theorem torsion8_def : torsion8 =
    ⟨14399317868200118260347934320527232580618823971194345261214217575416788799818,
      55188659117513257062467267217118295137698188065244968500265048394206261417927,
      torsion8_equation⟩ := by
  unfold torsion8
  rfl

theorem torsion8_x_eq : torsion8.x =
    14399317868200118260347934320527232580618823971194345261214217575416788799818 := by
  rw [torsion8_def]

theorem torsion8_y_eq : torsion8.y =
    55188659117513257062467267217118295137698188065244968500265048394206261417927 := by
  rw [torsion8_def]

/-! ### The multiples `2 • T` and `4 • T` -/

theorem two_nsmul_torsion8_x_eq : (2 • torsion8).x =
    38214883241950591754978413199355411911188925816896391856984770930832735035197 :=
  (Proofs.two_nsmul_torsion8_x_y torsion8 torsion8_x_eq torsion8_y_eq).1

/-- `2 • torsion8 = (-√-1, 0)`. -/
theorem two_nsmul_torsion8_x : (2 • torsion8).x = -sqrtM1 := by
  rw [two_nsmul_torsion8_x_eq, neg_sqrtM1_eq]

theorem two_nsmul_torsion8_y_eq : (2 • torsion8).y = 0 :=
  (Proofs.two_nsmul_torsion8_x_y torsion8 torsion8_x_eq torsion8_y_eq).2

theorem four_nsmul_torsion8_x_eq : (4 • torsion8).x = 0 :=
  (Proofs.four_nsmul_torsion8_x_y torsion8 torsion8_x_eq torsion8_y_eq).1

theorem four_nsmul_torsion8_y_eq : (4 • torsion8).y =
    57896044618658097711785492504343953926634992332820282019728792003956564819948 :=
  (Proofs.four_nsmul_torsion8_x_y torsion8 torsion8_x_eq torsion8_y_eq).2

/-- `4 • torsion8 = (0, -1)`, the point of order `2`. -/
theorem four_nsmul_torsion8_y : (4 • torsion8).y = -1 := by
  rw [four_nsmul_torsion8_y_eq, neg_one_eq_numeral]

theorem four_nsmul_torsion8_ne_zero : 4 • torsion8 ≠ 0 := by
  intro h
  have hy := congrArg TwistedEdwardsModel.Point.y h
  rw [four_nsmul_torsion8_y, TwistedEdwardsModel.zero_y] at hy
  exact ZMod.neg_one_ne_one hy

/-- `8 • torsion8 = 2 • (0, -1) = 0`. -/
theorem eight_nsmul_torsion8 : 8 • torsion8 = 0 := by
  rw [show (8 : ℕ) = 2 * 4 from rfl, ← smul_smul, TwistedEdwardsModel.two_nsmul_eq_zero_iff]
  exact four_nsmul_torsion8_x_eq

/-- `torsion8` has order `8`. -/
theorem addOrderOf_torsion8 : addOrderOf torsion8 = 8 :=
  addOrderOf_eq_prime_pow (p := 2) (n := 2) four_nsmul_torsion8_ne_zero eight_nsmul_torsion8

/-! ### The characterisation -/

/-- `x(torsion8)` is non-negative (even). -/
theorem not_isNeg_torsion8_x : ¬ torsion8.x.IsNeg := by
  rw [torsion8_x_eq, ZMod.not_isNeg_iff, ZMod.val_ofNat_of_lt (by rw [p_eq_numeral]; decide)]

/-- **`torsion8` in words**: it is the point `T` with `2 • T = (-√-1, 0)` and `x` non-negative.
(Such a `T` has order `8`; the other point with this double is `5 • T = (-x, -y)`.) -/
theorem eq_torsion8_iff (T : edwards.Point) :
    T = torsion8 ↔ (2 • T).x = -sqrtM1 ∧ (2 • T).y = 0 ∧ ¬ T.x.IsNeg := by
  constructor
  · rintro rfl
    exact ⟨two_nsmul_torsion8_x, two_nsmul_torsion8_y_eq, not_isNeg_torsion8_x⟩
  · rintro ⟨hx, hy, hneg⟩
    -- `D = T - torsion8` has `2 • D = 0`, so `D` is `(0, 1)` or `(0, -1)`
    have h2 : 2 • T = 2 • torsion8 := TwistedEdwardsModel.Point.ext
      (by rw [hx, two_nsmul_torsion8_x]) (by rw [hy, two_nsmul_torsion8_y_eq])
    have hD : 2 • (T - torsion8) = 0 := by rw [smul_sub, h2, sub_self]
    have hDx := (TwistedEdwardsModel.two_nsmul_eq_zero_iff _).mp hD
    have hT : T = (T - torsion8) + torsion8 := by abel
    rcases TwistedEdwardsModel.y_eq_one_or_eq_neg_one_of_x_eq_zero (T - torsion8).equation hDx
      with hDy | hDy
    · have h0 : T - torsion8 = 0 := TwistedEdwardsModel.Point.ext
        (by rw [hDx, TwistedEdwardsModel.zero_x]) (by rw [hDy, TwistedEdwardsModel.zero_y])
      rw [hT, h0, zero_add]
    · -- `T = (-x, -y)` would have `x` negative
      exfalso
      have hTx : T.x = -torsion8.x := by
        rw [hT]
        exact TwistedEdwardsModel.add_x_of_x_eq_zero_of_y_eq_neg_one torsion8 hDx hDy
      have hx0 : torsion8.x ≠ 0 := fun h0 => by
        have h20 := (TwistedEdwardsModel.two_nsmul_eq_zero_iff torsion8).mpr h0
        have := two_nsmul_torsion8_y_eq
        rw [h20, TwistedEdwardsModel.zero_y] at this
        exact one_ne_zero this
      rw [hTx] at hneg
      exact hneg (ZMod.isNeg_neg_of_not_isNeg hx0 not_isNeg_torsion8_x)

/-! ### The other multiples, from the group law -/

/-- `5 • T = (0, -1) + T = (-x, -y)`. -/
private theorem five_nsmul_torsion8_x : (5 • torsion8).x = -torsion8.x := by
  rw [succ_nsmul, TwistedEdwardsModel.add_x_of_x_eq_zero_of_y_eq_neg_one _ four_nsmul_torsion8_x_eq
    four_nsmul_torsion8_y]

private theorem five_nsmul_torsion8_y : (5 • torsion8).y = -torsion8.y := by
  rw [succ_nsmul, TwistedEdwardsModel.add_y_of_x_eq_zero_of_y_eq_neg_one _ four_nsmul_torsion8_x_eq
    four_nsmul_torsion8_y]

/-- `i • T = -((8 - i) • T)`, as `8 • T = 0`. -/
private theorem nsmul_torsion8_eq_neg {i j : ℕ} (h : i + j = 8) :
    i • torsion8 = -(j • torsion8) :=
  eq_neg_of_add_eq_zero_left (by rw [← add_nsmul, h, eight_nsmul_torsion8])

/-- `-x` for `T = (x, y)`, as a numeral. -/
private theorem neg_torsion8_x_eq : -torsion8.x =
    43496726750457979451437558183816721346016168361625936758514574428539776020131 := by
  rw [torsion8_x_eq]
  exact_mod_cast neg_natCast_eq_of_add_eq
    (x := 14399317868200118260347934320527232580618823971194345261214217575416788799818)
    (y := 43496726750457979451437558183816721346016168361625936758514574428539776020131)
    (by rw [p_eq_numeral])

/-- `-y` for `T = (x, y)`, as a numeral. -/
private theorem neg_torsion8_y_eq : -torsion8.y =
    2707385501144840649318225287225658788936804267575313519463743609750303402022 := by
  rw [torsion8_y_eq]
  exact_mod_cast neg_natCast_eq_of_add_eq
    (x := 55188659117513257062467267217118295137698188065244968500265048394206261417927)
    (y := 2707385501144840649318225287225658788936804267575313519463743609750303402022)
    (by rw [p_eq_numeral])

theorem three_nsmul_torsion8_x_eq : (3 • torsion8).x =
    14399317868200118260347934320527232580618823971194345261214217575416788799818 := by
  rw [nsmul_torsion8_eq_neg (j := 5) rfl, TwistedEdwardsModel.neg_x, five_nsmul_torsion8_x,
    neg_neg, torsion8_x_eq]

theorem three_nsmul_torsion8_y_eq : (3 • torsion8).y =
    2707385501144840649318225287225658788936804267575313519463743609750303402022 := by
  rw [nsmul_torsion8_eq_neg (j := 5) rfl, TwistedEdwardsModel.neg_y, five_nsmul_torsion8_y,
    neg_torsion8_y_eq]

theorem five_nsmul_torsion8_x_eq : (5 • torsion8).x =
    43496726750457979451437558183816721346016168361625936758514574428539776020131 := by
  rw [five_nsmul_torsion8_x, neg_torsion8_x_eq]

theorem five_nsmul_torsion8_y_eq : (5 • torsion8).y =
    2707385501144840649318225287225658788936804267575313519463743609750303402022 := by
  rw [five_nsmul_torsion8_y, neg_torsion8_y_eq]

theorem six_nsmul_torsion8_x_eq : (6 • torsion8).x =
    19681161376707505956807079304988542015446066515923890162744021073123829784752 := by
  rw [nsmul_torsion8_eq_neg (j := 2) rfl, TwistedEdwardsModel.neg_x, two_nsmul_torsion8_x_eq,
    ← neg_sqrtM1_eq, neg_neg, sqrtM1_eq_numeral]

/-- `6 • torsion8 = (√-1, 0)`. -/
theorem six_nsmul_torsion8_x : (6 • torsion8).x = sqrtM1 := by
  rw [six_nsmul_torsion8_x_eq, sqrtM1_eq_numeral]

theorem six_nsmul_torsion8_y_eq : (6 • torsion8).y = 0 := by
  rw [nsmul_torsion8_eq_neg (j := 2) rfl, TwistedEdwardsModel.neg_y, two_nsmul_torsion8_y_eq]

theorem seven_nsmul_torsion8_x_eq : (7 • torsion8).x =
    43496726750457979451437558183816721346016168361625936758514574428539776020131 := by
  rw [nsmul_torsion8_eq_neg (j := 1) rfl, one_nsmul, TwistedEdwardsModel.neg_x, neg_torsion8_x_eq]

theorem seven_nsmul_torsion8_y_eq : (7 • torsion8).y =
    55188659117513257062467267217118295137698188065244968500265048394206261417927 := by
  rw [nsmul_torsion8_eq_neg (j := 1) rfl, one_nsmul, TwistedEdwardsModel.neg_y, torsion8_y_eq]

/-! ### The eight torsion points `i • T`, `i < 8` -/

/-- `8 • (i • torsion8) = 0`. -/
theorem eight_nsmul_nsmul_torsion8 (i : ℕ) : 8 • i • torsion8 = 0 := by
  rw [smul_comm, eight_nsmul_torsion8, smul_zero]

/-- The eight points `i • torsion8`, `i < 8`, are distinct. -/
theorem nsmul_torsion8_injective : Function.Injective fun i : Fin 8 => (i : ℕ) • torsion8 := by
  intro i j h
  simp only at h
  rw [nsmul_eq_nsmul_iff_modEq, addOrderOf_torsion8] at h
  exact Fin.ext (h.eq_of_lt_of_lt i.isLt j.isLt)

end curve25519
