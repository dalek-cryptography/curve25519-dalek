/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basic
import all Curve25519.Basic
import Curve25519.ToEllipticCurve.TwistedEdwards.Formulas.Lemmas
public section

/-! # Certificates for the basepoint and the 8-torsion (not audited)

Kernel computations (`decide +kernel`) in extended coordinates: the curve equation at the
basepoint and at the torsion point, numeral facts about the basepoint's coordinates,
`L • basepoint = 0` (the 253-step double-and-add chain), and the coordinates of `2 • torsion8`
and `4 • torsion8`. Scalar multiples are related to the group law by
`Point.nsmul_eq_iff_projEq` and `Point.nsmul_eq_zero_iff_isZero`
(`Curve25519.ToEllipticCurve.TwistedEdwards.Formulas.Lemmas`). The model is first rewritten to
its numeral form (`edwards_eq`), so that the kernel never meets the field inversion in `d`;
`Curve25519.Basic` is imported with `import all` so that the kernel can unfold `p` and `L`. The
results are stated for any point with the given numeral coordinates and used by
`Curve25519.Edwards.Basepoint`, `Curve25519.Edwards.Torsion` and `Curve25519.Montgomery`;
`edwards_eq` and `nsmul_x_y_of_coords` also by the Ristretto test vectors, and `edwards_eq` by
the dalek table certificates. -/

namespace curve25519.Proofs

open TwistedEdwardsModel

/-- `edwards` with its coefficients as numerals, for the kernel. -/
theorem edwards_eq :
    edwards = ⟨-1, ((37095705934669439343138083508754565189542113879843219016388785533085940283555 :
      ℕ) : ZMod p)⟩ := by
  rw [edwards_def, a_def, d_eq_natCast]

/-! ### From kernel computations to group facts -/

/-- A point with the given coordinates is `(x : y : 1 : x y)` in extended coordinates. -/
private theorem toExtended_of_coords {x y : ZMod p} {P : edwards.Point} (hx : P.x = x)
    (hy : P.y = y) : P.toExtended = ⟨x, y, 1, x * y⟩ := by
  rw [← hx, ← hy]
  rfl

/-- `n • P = 0` for a point with given coordinates, from the zero test on the numeral
extended point. -/
private theorem nsmul_eq_zero_of_coords {x y : ZMod p} {n : ℕ} (P : edwards.Point)
    (hx : P.x = x) (hy : P.y = y)
    (hc : (Extended.nsmul n (⟨x, y, 1, x * y⟩ : edwards.Extended)).IsZero) : n • P = 0 :=
  (Point.nsmul_eq_zero_iff_isZero n P).mpr (by rwa [toExtended_of_coords hx hy])

/-- The coordinates of `n • P` for a point with given coordinates, from projective equality of
the numeral extended points. -/
theorem nsmul_x_y_of_coords {x y x' y' : ZMod p} {n : ℕ} (P : edwards.Point)
    (hx : P.x = x) (hy : P.y = y) (h' : edwards.Equation x' y')
    (hc : (Extended.nsmul n (⟨x, y, 1, x * y⟩ : edwards.Extended)).ProjEq ⟨x', y', 1, x' * y'⟩) :
    (n • P).x = x' ∧ (n • P).y = y' := by
  rw [(Point.nsmul_eq_iff_projEq n P ⟨x', y', h'⟩).mpr (by rwa [toExtended_of_coords hx hy])]
  exact ⟨rfl, rfl⟩

/-! ### The basepoint -/

/-- The basepoint `(x, 4/5)` of RFC 8032 is on the model. -/
theorem basepoint_equation : edwards.Equation
    15112221349535400772501151409588531511454012693041857206046113283949847762202
    46316835694926478169428394003475163141307993866256225615783033603165251855960 := by
  rw [edwards_eq]
  decide +kernel

theorem basepoint_x_val_mod_two :
    (15112221349535400772501151409588531511454012693041857206046113283949847762202 :
      ZMod p).val % 2 = 0 := by
  decide +kernel

theorem basepoint_y_mul_five :
    (46316835694926478169428394003475163141307993866256225615783033603165251855960 : ZMod p)
      * 5 = 4 := by
  decide +kernel

/-- `(1 - y) x ≠ 0` at the basepoint: the denominator of the Montgomery `v`-coordinate. -/
theorem basepoint_den_ne_zero :
    (1 - (46316835694926478169428394003475163141307993866256225615783033603165251855960 : ZMod p)) *
      15112221349535400772501151409588531511454012693041857206046113283949847762202 ≠ 0 := by
  decide +kernel

/-- RFC 7748 §4.1: `V(P) · (1 - y) x = sqrtNegAAddTwo · (1 + y)` at the basepoint, i.e. the
Montgomery base point has `v = V(P)`. -/
theorem basepoint_v_mul_den :
    (14781619447589544791020593568409986887264606134616475288964881837755586237401 : ZMod p) *
      ((1 - 46316835694926478169428394003475163141307993866256225615783033603165251855960) *
        15112221349535400772501151409588531511454012693041857206046113283949847762202) =
      (sqrtNegAAddTwo : ZMod p) *
        (1 + 46316835694926478169428394003475163141307993866256225615783033603165251855960) := by
  decide +kernel

/-- `L • basepoint = 0`: the 253-step double-and-add chain in extended coordinates. -/
theorem L_nsmul_eq_zero (P : edwards.Point)
    (hx : P.x = 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (hy : P.y = 46316835694926478169428394003475163141307993866256225615783033603165251855960) :
    L • P = 0 :=
  nsmul_eq_zero_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)

/-! ### The torsion point -/

/-- Dalek's `EIGHT_TORSION[1]` is on the model. -/
theorem torsion8_equation : edwards.Equation
    14399317868200118260347934320527232580618823971194345261214217575416788799818
    55188659117513257062467267217118295137698188065244968500265048394206261417927 := by
  rw [edwards_eq]
  decide +kernel

/-! The multiples `2 • T = (-sqrtM1, 0)` and `4 • T = (0, -1)` of the torsion point `T`, with
their coordinates as numerals; the other multiples follow from the group law
(`Curve25519.Edwards.Torsion`). -/

theorem two_nsmul_torsion8_x_y (P : edwards.Point)
    (hx : P.x = 14399317868200118260347934320527232580618823971194345261214217575416788799818)
    (hy : P.y = 55188659117513257062467267217118295137698188065244968500265048394206261417927) :
    (2 • P).x = 38214883241950591754978413199355411911188925816896391856984770930832735035197 ∧
      (2 • P).y = 0 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

theorem four_nsmul_torsion8_x_y (P : edwards.Point)
    (hx : P.x = 14399317868200118260347934320527232580618823971194345261214217575416788799818)
    (hy : P.y = 55188659117513257062467267217118295137698188065244968500265048394206261417927) :
    (4 • P).x = 0 ∧
      (4 • P).y = 57896044618658097711785492504343953926634992332820282019728792003956564819948 :=
  nsmul_x_y_of_coords P hx hy (by rw [edwards_eq]; decide +kernel)
    (by rw [edwards_eq]; decide +kernel)

end curve25519.Proofs
