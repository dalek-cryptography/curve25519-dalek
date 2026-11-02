/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basic
import Curve25519.Proofs.Ristretto.Algebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public section

/-! # The field identities behind the ristretto255 map (not audited)

The algebra of RFC 9496 §4.3.4 `MAP`, stated with explicit hypotheses in place of the square
root: for `r`, `v = (-1 - r d)(r + d)`, `u = (r + 1)(1 - d²)`, and `(s, c)` the output of the
`SQRT_RATIO_M1` branch (`s² v = u`, `c = -1` when `u / v` is a square; `s² v = r u`, `c = r`
when it is not; `s = 0`, `c = r` when `v = 0`), the denominator `N K` with
`N = c (r - 1)(d - 1)² - v`, `K = SQRT_AD_MINUS_ONE` is nonzero, `1 + s² ≠ 0`, and
`(2 s v / (N K), (1 - s²) / (1 + s²))` is on `edwards` (`map_equation_of_branch`). Instantiated by
`Curve25519.Ristretto.Map`. -/

namespace curve25519.Proofs

open TwistedEdwardsModel

/-- The polynomial identity behind the curve equation of `MAP`: with `S = s²`, `S D = e u`
(`e = 1`, `c = -1` or `e = r`, `c = r`) and `D = (-1 - r dd)(r + dd)`, the equation
`-x² + y² = 1 + dd x² y²` at `x = 2 s D / (N K)`, `y = (1 - S) / (1 + S)`, multiplied out, with
`K² = -(1 + dd)`. -/
private theorem map_equation_identity {F : Type*} [Field F] (dd r e c S D : F)
    (hD : D = (-1 - r * dd) * (r + dd)) (hDne : D ≠ 0) (hc : (e = 1 ∧ c = -1) ∨ (e = r ∧ c = r))
    (hS : S * D = e * ((r + 1) * (1 - dd ^ 2))) :
    -(4 * S * D ^ 2) * (1 + S) ^ 2 +
        (1 - S) ^ 2 * (c * (r - 1) * (dd - 1) ^ 2 - D) ^ 2 * (-(1 + dd)) =
      (c * (r - 1) * (dd - 1) ^ 2 - D) ^ 2 * (-(1 + dd)) * (1 + S) ^ 2 +
        dd * (4 * S * D ^ 2) * (1 - S) ^ 2 := by
  have hS' : S = e * ((r + 1) * (1 - dd ^ 2)) / D := by
    rw [eq_div_iff hDne]
    exact hS
  subst hS'
  field_simp
  subst hD
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ring

/-- The curve equation from the multiplied-out identity. -/
private theorem map_equation_of_identity (s D N : ZMod p) (hN : N ≠ 0) (hs : 1 + s ^ 2 ≠ 0)
    (E : -(4 * s ^ 2 * D ^ 2) * (1 + s ^ 2) ^ 2 + (1 - s ^ 2) ^ 2 * N ^ 2 =
      N ^ 2 * (1 + s ^ 2) ^ 2 + d * (4 * s ^ 2 * D ^ 2) * (1 - s ^ 2) ^ 2) :
    edwards.Equation (2 * s * D / N) ((1 - s ^ 2) / (1 + s ^ 2)) := by
  unfold Equation
  rw [edwards_a_eq_neg_one, edwards_d]
  field_simp
  linear_combination E

/-- **The core of `MAP`**, abstracted over the branch data. -/
theorem map_equation_of_branch (r s c e D : ZMod p) (hD : D = (-1 - r * d) * (r + d))
    (hns : (r + 1) * (1 - d ^ 2) ≠ 0)
    (hcase : (D ≠ 0 ∧ ((e = 1 ∧ c = -1) ∨ (e = r ∧ c = r)) ∧
        s ^ 2 * D = e * ((r + 1) * (1 - d ^ 2))) ∨ (D = 0 ∧ s = 0 ∧ c = r)) :
    (c * (r - 1) * (d - 1) ^ 2 - D) * sqrtAdMinusOne ≠ 0 ∧ 1 + s ^ 2 ≠ 0 ∧
      edwards.Equation (2 * s * D / ((c * (r - 1) * (d - 1) ^ 2 - D) * sqrtAdMinusOne))
        ((1 - s ^ 2) / (1 + s ^ 2)) := by
  set Nt := c * (r - 1) * (d - 1) ^ 2 - D with hNt
  have hK2 : (sqrtAdMinusOne : ZMod p) ^ 2 = -(1 + d) := by
    rw [sqrtAdMinusOne_sq, a_def]
    ring
  have E0 : -(4 * s ^ 2 * D ^ 2) * (1 + s ^ 2) ^ 2 + (1 - s ^ 2) ^ 2 * Nt ^ 2 * (-(1 + d)) =
      Nt ^ 2 * (-(1 + d)) * (1 + s ^ 2) ^ 2 + d * (4 * s ^ 2 * D ^ 2) * (1 - s ^ 2) ^ 2 := by
    rcases hcase with ⟨hDne, hc, hS⟩ | ⟨hD0, hs0, -⟩
    · exact map_equation_identity d r e c (s ^ 2) D hD hDne hc hS
    · rw [hD0, hs0]
      ring
  have hNt_ne : Nt ≠ 0 := by
    intro hN
    rw [hN] at E0
    rcases hcase with ⟨hDne, hc, hS⟩ | ⟨hD0, hs0, hc⟩
    · have hfac : (4 * s ^ 2 * D ^ 2) * ((1 + s ^ 2) ^ 2 + d * (1 - s ^ 2) ^ 2) = 0 := by
        linear_combination -E0
      rcases mul_eq_zero.mp hfac with h0 | h0
      · have hs2 : s ^ 2 = 0 := by
          rcases mul_eq_zero.mp h0 with h1 | h1
          · rcases mul_eq_zero.mp h1 with h2 | h2
            · exact absurd h2 four_ne_zero
            · exact h2
          · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h1) hDne
        rw [hs2, zero_mul] at hS
        have he : e = 0 := by
          rcases mul_eq_zero.mp hS.symm with h | h
          · exact h
          · exact absurd h hns
        rcases hc with ⟨he1, -⟩ | ⟨her, hcr⟩
        · rw [he1] at he
          exact one_ne_zero he
        · have hr : r = 0 := her ▸ he
          rw [hNt, hcr, hD, hr] at hN
          apply d_ne_zero
          linear_combination hN
      · have hsub : (1 : ZMod p) - s ^ 2 ≠ 0 := by
          intro h1
          have h2 : (1 + s ^ 2) ^ 2 = 0 := by linear_combination h0 - d * (1 - s ^ 2) * h1
          have h3 : (1 : ZMod p) + s ^ 2 = 2 := by linear_combination -h1
          rw [h3] at h2
          exact two_ne_zero (pow_eq_zero_iff two_ne_zero |>.mp h2)
        apply not_isSquare_neg_d
        refine ⟨(1 + s ^ 2) / (1 - s ^ 2), ?_⟩
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hsub hsub)]
        linear_combination -h0
    · rw [hNt, hc, hD0] at hN
      have hr0 : r ≠ 0 := by
        intro h
        rw [h, hD0] at hD
        apply d_ne_zero
        linear_combination hD
      have hr1 : r - 1 ≠ 0 := by
        intro h
        have h' : r = 1 := by linear_combination h
        rw [h', hD0] at hD
        have h2 : (1 + d) ^ 2 = 0 := by linear_combination hD
        exact one_add_d_ne_zero (pow_eq_zero_iff two_ne_zero |>.mp h2)
      have h3 : r * (r - 1) * (d - 1) ^ 2 = 0 := by linear_combination hN
      rcases mul_eq_zero.mp h3 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact hr0 h
        · exact hr1 h
      · exact d_sub_one_ne_zero (pow_eq_zero_iff two_ne_zero |>.mp h)
  have hNK : Nt * sqrtAdMinusOne ≠ 0 := mul_ne_zero hNt_ne sqrtAdMinusOne_ne_zero
  have E : -(4 * s ^ 2 * D ^ 2) * (1 + s ^ 2) ^ 2 + (1 - s ^ 2) ^ 2 * (Nt * sqrtAdMinusOne) ^ 2 =
      (Nt * sqrtAdMinusOne) ^ 2 * (1 + s ^ 2) ^ 2 + d * (4 * s ^ 2 * D ^ 2) * (1 - s ^ 2) ^ 2 := by
    rw [mul_pow, hK2]
    linear_combination E0
  have hs1 : 1 + s ^ 2 ≠ 0 := by
    intro h1
    have hS : s ^ 2 = -1 := by linear_combination h1
    rw [hS] at E
    have hsq : (Nt * sqrtAdMinusOne) ^ 2 = d * (2 * s * D) ^ 2 := by
      have h4 : (4 : ZMod p) * ((Nt * sqrtAdMinusOne) ^ 2 - d * (4 * (-1) * D ^ 2)) = 0 := by
        linear_combination E
      have h5 := (mul_eq_zero.mp h4).resolve_left four_ne_zero
      rw [show (2 * s * D) ^ 2 = 4 * s ^ 2 * D ^ 2 by ring, hS]
      linear_combination h5
    have hsD : 2 * s * D ≠ 0 := by
      intro h0
      rw [h0] at hsq
      have hz : (Nt * sqrtAdMinusOne) ^ 2 = 0 := by rw [hsq]; ring
      exact hNK (pow_eq_zero_iff two_ne_zero |>.mp hz)
    apply not_isSquare_d
    refine ⟨Nt * sqrtAdMinusOne / (2 * s * D), ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hsD hsD), ← sq, ← sq, hsq]
  exact ⟨hNK, hs1, map_equation_of_identity s D _ hNK hs1 E⟩

end curve25519.Proofs
