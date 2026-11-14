/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Field.ZMod
public section

/-! # The sign convention on `ZMod p`

RFC 8032 (§5.1.2) and RFC 9496 (§4.1) call an element `x` of `ZMod p` *negative* when its
canonical representative `x.val ∈ [0, p)` is odd: `ZMod.IsNeg x`. For odd `p`, exactly one of
`x` and `-x` is negative when `x ≠ 0` (`isNeg_neg_iff`), so for prime `p` two elements with the
same square and the same sign are equal (`eq_of_sq_eq_of_isNeg_iff`). The absolute value
`ZMod.abs x = if x.IsNeg then -x else x` is RFC 9496's `CT_ABS` / `|x|`.

Both definitions are exposed: `IsNeg` is a `Prop` that specifications unfold, and `abs` is a
formula the kernel evaluates. The parity lemmas take the oddness of `p` as an instance
`[Fact (p % 2 = 1)]`, as Mathlib does (for a complete twisted Edwards model over `ZMod p` it
follows from `2 ≠ 0`: `mod_two_eq_one_of_two_ne_zero`,
`TwistedEdwardsModel.mod_two_eq_one_of_isComplete`). -/

namespace ZMod

variable {p : ℕ}

/-- `x` is *negative* (RFC 8032 §5.1.2, RFC 9496 §4.1): its canonical representative
`x.val ∈ [0, p)` is odd. -/
@[expose] def IsNeg (x : ZMod p) : Prop :=
  x.val % 2 = 1

instance instDecidableIsNeg (x : ZMod p) : Decidable x.IsNeg :=
  inferInstanceAs (Decidable (x.val % 2 = 1))

/-- `|x|` (RFC 9496's `CT_ABS`): `-x` if `x` is negative, `x` otherwise. -/
@[expose] def abs (x : ZMod p) : ZMod p :=
  if x.IsNeg then -x else x

/-! ### Parity -/

theorem isNeg_iff {x : ZMod p} : x.IsNeg ↔ x.val % 2 = 1 :=
  Iff.rfl

theorem not_isNeg_iff {x : ZMod p} : ¬ x.IsNeg ↔ x.val % 2 = 0 := by
  rw [isNeg_iff]
  omega

theorem not_isNeg_zero : ¬ (0 : ZMod p).IsNeg := by
  rw [isNeg_iff, val_zero]
  decide

theorem ne_zero_of_isNeg {x : ZMod p} (h : x.IsNeg) : x ≠ 0 :=
  fun h0 => not_isNeg_zero (h0 ▸ h)

/-- `p` is odd when `2 ≠ 0` in the field `ZMod p`. -/
theorem mod_two_eq_one_of_two_ne_zero [Fact p.Prime] (h : (2 : ZMod p) ≠ 0) : p % 2 = 1 :=
  (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr
    (by rintro rfl; exact h (by exact_mod_cast ZMod.natCast_self 2))

section Odd

variable [Fact (p % 2 = 1)]

/-- For odd `p`, exactly one of `x` and `-x` is negative when `x ≠ 0`. -/
theorem isNeg_neg_iff {x : ZMod p} (hx : x ≠ 0) : (-x).IsNeg ↔ ¬ x.IsNeg := by
  have hp : p % 2 = 1 := Fact.out
  have : NeZero p := ⟨by omega⟩
  rw [isNeg_iff, isNeg_iff, neg_val, ite_eq_right hx]
  have h1 := val_lt x
  have h2 : x.val ≠ 0 := fun h0 => hx ((val_eq_zero x).mp h0)
  omega

theorem isNeg_neg_of_not_isNeg {x : ZMod p} (hx : x ≠ 0) (h : ¬ x.IsNeg) : (-x).IsNeg :=
  (isNeg_neg_iff hx).mpr h

theorem not_isNeg_neg_of_isNeg {x : ZMod p} (h : x.IsNeg) : ¬ (-x).IsNeg :=
  fun h' => (isNeg_neg_iff (ne_zero_of_isNeg h)).mp h' h

theorem isNeg_or_isNeg_neg {x : ZMod p} (hx : x ≠ 0) : x.IsNeg ∨ (-x).IsNeg := by
  rw [isNeg_neg_iff hx]
  exact em _

/-- An element that is not negative and whose negation is not negative is `0` (`p` odd). -/
theorem eq_zero_of_not_isNeg_of_not_isNeg_neg {x : ZMod p} (h : ¬ x.IsNeg) (h' : ¬ (-x).IsNeg) :
    x = 0 := by
  by_contra hx
  exact (isNeg_or_isNeg_neg hx).elim h h'

end Odd

/-! ### The absolute value -/

theorem abs_of_isNeg {x : ZMod p} (h : x.IsNeg) : x.abs = -x :=
  ite_eq_left h

theorem abs_of_not_isNeg {x : ZMod p} (h : ¬ x.IsNeg) : x.abs = x :=
  ite_eq_right h

theorem abs_zero : (0 : ZMod p).abs = 0 :=
  abs_of_not_isNeg not_isNeg_zero

theorem abs_eq_or_abs_eq_neg (x : ZMod p) : x.abs = x ∨ x.abs = -x := by
  by_cases h : x.IsNeg
  · exact Or.inr (abs_of_isNeg h)
  · exact Or.inl (abs_of_not_isNeg h)

theorem abs_sq (x : ZMod p) : x.abs ^ 2 = x ^ 2 := by
  rcases abs_eq_or_abs_eq_neg x with h | h <;> rw [h]
  exact neg_sq x

section Odd

variable [Fact (p % 2 = 1)]

/-- `|x|` is never negative (`p` odd). -/
theorem not_isNeg_abs (x : ZMod p) : ¬ x.abs.IsNeg := by
  by_cases h : x.IsNeg
  · rw [abs_of_isNeg h]
    exact not_isNeg_neg_of_isNeg h
  · rwa [abs_of_not_isNeg h]

theorem abs_neg (x : ZMod p) : (-x).abs = x.abs := by
  by_cases hx : x = 0
  · rw [hx, neg_zero]
  · by_cases h : x.IsNeg
    · rw [abs_of_isNeg h, abs_of_not_isNeg (not_isNeg_neg_of_isNeg h)]
    · rw [abs_of_not_isNeg h, abs_of_isNeg (isNeg_neg_of_not_isNeg hx h), neg_neg]

/-- `|x| = |y|` iff `y = x` or `y = -x` (`p` odd). -/
theorem abs_eq_abs_iff {x y : ZMod p} : x.abs = y.abs ↔ x = y ∨ x = -y := by
  constructor
  · intro h
    rcases abs_eq_or_abs_eq_neg x with hx | hx <;> rcases abs_eq_or_abs_eq_neg y with hy | hy <;>
      rw [hx, hy] at h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (neg_eq_iff_eq_neg.mp h)
    · exact Or.inl (neg_inj.mp h)
  · rintro (rfl | rfl)
    · rfl
    · exact abs_neg y

end Odd

/-! ### Square roots -/

section Field

variable [Fact p.Prime]

variable [Fact (p % 2 = 1)]

/-- Two elements with the same square have the same absolute value (`p` odd). -/
theorem abs_eq_abs_of_sq_eq {x y : ZMod p} (h : x ^ 2 = y ^ 2) : x.abs = y.abs :=
  (abs_eq_abs_iff).mpr (sq_eq_sq_iff_eq_or_eq_neg.mp h)

/-- Two elements with the same square and the same sign are equal (`p` odd). -/
theorem eq_of_sq_eq_of_isNeg_iff {x y : ZMod p} (h : x ^ 2 = y ^ 2)
    (hs : x.IsNeg ↔ y.IsNeg) : x = y := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with hxy | hxy
  · exact hxy
  · by_cases hy : y = 0
    · rw [hxy, hy, neg_zero]
    · rw [hxy, isNeg_neg_iff hy] at hs
      exact absurd hs not_iff_self

end Field

end ZMod
