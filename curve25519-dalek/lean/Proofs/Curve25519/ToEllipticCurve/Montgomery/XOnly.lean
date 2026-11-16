/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.Montgomery.Ladder.Lemmas
public import EllipticCurve.Montgomery.XOnly.Lemmas
import EllipticCurve.Montgomery.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public section

/-! # The doubling formula of x-only arithmetic (staged for `EllipticCurve`)

The `u`-coordinate of `2 • Q` is a rational function of `u(Q)`:
`u(2 Q) = (u² - 1)² / (4 u (u² + A u + 1))` (`u_two_nsmul`), with `x / 0 = 0` covering the point at
infinity and the points of order `2`, both sent to `u = 0`. For a finite field and a non-square
`c`, x-only doubling `M.xMul c 2` is this function (`xMul_two`), and `M.xMul c (2 ^ n)` is its
`n`-th iterate (`xMul_two_pow`).

Staged here for upstreaming to the `EllipticCurve` library: these depend only on the model. -/

universe u

namespace MontgomeryModel

variable {F : Type u} [Field F] {M : MontgomeryModel F}

/-- The doubling map on `u`-coordinates, `u ↦ (u² - 1)² / (4 u (u² + A u + 1))`. -/
@[expose] def dblU (M : MontgomeryModel F) (u : F) : F :=
  (u ^ 2 - 1) ^ 2 / (4 * u * (u ^ 2 + M.A * u + 1))

/-- `dblU` depends on the model only through `A`, so it is the same on a twist. -/
theorem dblU_twist (c : F) : (M.twist c).dblU = M.dblU := by
  unfold dblU
  rw [twist_A]

variable [M.IsNonsingular]

/-- **Doubling on `u`-coordinates**: `u(2 • Q) = (u² - 1)² / (4 u (u² + A u + 1))`. -/
theorem u_two_nsmul (Q : M.Point) : (2 • Q).u = M.dblU Q.u := by
  rcases Point.cases Q with rfl | ⟨u, v, hQ, rfl⟩
  · rw [smul_zero, u_zero, dblU, mul_zero, zero_mul, div_zero]
  · have hrep : (XZ.mk u 1).Represents (Point.some u v hQ) :=
      (XZ.represents_some_iff hQ).mpr ⟨one_ne_zero, (mul_one u).symm⟩
    rw [← XZ.toU_xDbl hrep, u_some, XZ.toU, dblU]
    have ha24 := four_mul_a24 M
    congr 1
    · simp only [xDbl, XZ.dbl]
      ring
    · simp only [xDbl, XZ.dbl]
      linear_combination (4 * u ^ 2) * ha24

variable [Finite F] {c : F}

/-- x-only doubling is `dblU`. -/
theorem xMul_two (hc : ¬ IsSquare c) (u : F) : M.xMul c 2 u = M.dblU u := by
  have := M.isNonsingular_twist (ne_zero_of_not_isSquare hc)
  rcases exists_point_u_or_twist (M := M) hc u with ⟨Q, rfl⟩ | ⟨Q, rfl⟩
  · rw [xMul_eq_u_nsmul, u_two_nsmul]
  · rw [xMul_eq_u_nsmul_twist hc, u_two_nsmul, dblU_twist]

/-- x-only multiplication by `2 ^ n` is the `n`-th iterate of `dblU`. -/
theorem xMul_two_pow (hc : ¬ IsSquare c) (n : ℕ) (u : F) :
    M.xMul c (2 ^ n) u = M.dblU^[n] u := by
  induction n with
  | zero => rw [pow_zero, xMul_one hc, Function.iterate_zero_apply]
  | succ n ih => rw [pow_succ', xMul_mul hc, ih, xMul_two hc, Function.iterate_succ_apply']

end MontgomeryModel
