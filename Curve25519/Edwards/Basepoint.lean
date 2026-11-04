/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basic
import Curve25519.Proofs.Edwards.Certs
import Mathlib.Tactic.LinearCombination
public section

/-! # The basepoint

The basepoint `B` of edwards25519 (RFC 8032 §5.1): the point with `y = 4/5` and even `x`. It
generates the prime-order subgroup: `L • B = 0` and `addOrderOf B = L`. The definition is
hidden; the coordinates are `basepoint_x_eq`, `basepoint_y_eq`, `basepoint_y`. The certificates
are in `Curve25519.Proofs.Edwards.Certs` (not audited). -/

namespace curve25519

/-- The basepoint `(x, 4/5)` of RFC 8032 is on the model. -/
theorem basepoint_equation : edwards.Equation
    15112221349535400772501151409588531511454012693041857206046113283949847762202
    46316835694926478169428394003475163141307993866256225615783033603165251855960 :=
  Proofs.basepoint_equation

/-- The basepoint of edwards25519: `y = 4/5`, `x` even (RFC 8032 §5.1). -/
noncomputable def basepoint : edwards.Point :=
  ⟨15112221349535400772501151409588531511454012693041857206046113283949847762202,
    46316835694926478169428394003475163141307993866256225615783033603165251855960,
    basepoint_equation⟩

theorem basepoint_def : basepoint =
    ⟨15112221349535400772501151409588531511454012693041857206046113283949847762202,
      46316835694926478169428394003475163141307993866256225615783033603165251855960,
      basepoint_equation⟩ := by
  unfold basepoint
  rfl

/-- The `x`-coordinate of the basepoint. -/
theorem basepoint_x_eq : basepoint.x =
    15112221349535400772501151409588531511454012693041857206046113283949847762202 := by
  rw [basepoint_def]

/-- The `y`-coordinate of the basepoint. -/
theorem basepoint_y_eq : basepoint.y =
    46316835694926478169428394003475163141307993866256225615783033603165251855960 := by
  rw [basepoint_def]

/-- The basepoint has `y = 4/5`. -/
theorem basepoint_y : basepoint.y = 4 / 5 := by
  rw [basepoint_y_eq, eq_div_iff (NeZero.ne (5 : ZMod p))]
  exact Proofs.basepoint_y_mul_five

/-- The basepoint has even `x` (RFC 8032: the "positive" square root). -/
theorem basepoint_x_val_even : basepoint.x.val % 2 = 0 := by
  rw [basepoint_x_eq]
  exact Proofs.basepoint_x_val_mod_two

/-- The basepoint is not `0 = (0, 1)`: its `y` is `4/5 ≠ 1`. -/
theorem basepoint_ne_zero : basepoint ≠ 0 := by
  intro h
  have hy := congrArg TwistedEdwardsModel.Point.y h
  rw [basepoint_y, TwistedEdwardsModel.zero_y, div_eq_one_iff_eq (NeZero.ne (5 : ZMod p))] at hy
  exact one_ne_zero (by linear_combination -hy : (1 : ZMod p) = 0)

/-- `L • basepoint = 0`. -/
theorem L_nsmul_basepoint : L • basepoint = 0 :=
  Proofs.L_nsmul_eq_zero basepoint basepoint_x_eq basepoint_y_eq

/-- The basepoint has prime order `L`. -/
theorem addOrderOf_basepoint : addOrderOf basepoint = L :=
  addOrderOf_eq_prime L_nsmul_basepoint basepoint_ne_zero

end curve25519
