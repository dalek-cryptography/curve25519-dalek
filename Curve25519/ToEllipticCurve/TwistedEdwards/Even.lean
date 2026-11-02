/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.TwistedEdwards.Even
public import Mathlib.GroupTheory.Index
import EllipticCurve.Mathlib.Algebra.Group.Even
public section

/-! # The 2-descent on a complete twisted Edwards model (staged for `EllipticCurve`)

Completions of the generic half of the 2-descent of `EllipticCurve.TwistedEdwards.Even`
(`E.descent`, the points with `(a - d)(1 - y²)` a square, contains the even points):

* when `a - d` is a nonzero square, membership in `E.descent` is `1 - y²` being a square
  (`mem_descent_iff_of_sub_eq_sq`);
* when the even points have index `2` and some point is not in `E.descent`, the descent subgroup
  is exactly the subgroup of even points (`descent_eq_even_of_index_eq_two`): the descent map
  then detects evenness.

Staged here for upstreaming to the `EllipticCurve` library: these depend only on the model. -/

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F} [E.IsComplete]

/-- When `a - d = c²` with `c ≠ 0`, a point is in `E.descent` iff `1 - y²` is a square. -/
theorem mem_descent_iff_of_sub_eq_sq {c : F} (hc : c ≠ 0) (h : E.a - E.d = c ^ 2) (P : E.Point) :
    P ∈ E.descent ↔ IsSquare (1 - P.y ^ 2) := by
  rw [mem_descent, h, isSquare_sq_mul_iff hc]

/-- **The 2-descent**: if the even points have index `2` and some point is not in `E.descent`,
then `E.descent` is the subgroup of even points. -/
theorem descent_eq_even_of_index_eq_two (h2 : (AddSubgroup.even E.Point).index = 2)
    {P : E.Point} (hP : P ∉ E.descent) : E.descent = AddSubgroup.even E.Point := by
  have hmul := AddSubgroup.relIndex_mul_index (even_le_descent (E := E))
  rw [h2] at hmul
  have hne : E.descent.index ≠ 1 := fun h1 =>
    hP ((AddSubgroup.index_eq_one.mp h1).symm ▸ AddSubgroup.mem_top P)
  have hrel : (AddSubgroup.even E.Point).relIndex E.descent = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro_left _ hmul) with h | h
    · exact absurd h hne
    · rw [h] at hmul
      omega
  exact le_antisymm (AddSubgroup.relIndex_eq_one.mp hrel) even_le_descent

end TwistedEdwardsModel
