module
public import ForHumans.Specs.Curves
import all ForHumans.Specs.Curves
public import Proofs.Curve25519.Basic
public import Proofs.Curve25519.Prime
public import Proofs.Curve25519.Squares
public import EllipticCurve
public import Proofs.Curve25519.Models
public import Mathlib.Algebra.Field.ZMod
public section

/-! # The models of curve25519

The twisted Edwards model `edwards = (a, d)` (edwards25519, RFC 8032 §5.1), the Montgomery
model `montgomery = (A, 1)` (curve25519, RFC 7748 §4.1), and the curve `curve` they both realise.
`edwards` is complete (`-1` is a square and `d` is not, `Proofs.Curve25519.Squares`), `montgomery`
is nonsingular, and the two models give the same curve (`toCurve_edwards`, `toCurve_montgomery`):
the Montgomery model `(A, 4 / (a - d))` of `edwards` is the rescaling of `montgomery` by
`sqrtNegAAddTwo`, a square root of `4 / (a - d) = -(A + 2)`.

The definitions are hidden; importers use `edwards_def`, `edwards_a`, `edwards_d`,
`montgomery_def`, `montgomery_A`, `montgomery_B`, `curve_def` and the lemmas below.

This module re-exports the `EllipticCurve` library and `Proofs.Curve25519.Models` (coordinates,
encodings, the Decaf relation), so that every importer of the models sees their API. -/

namespace curve25519

/-! ### The twisted Edwards model -/

theorem edwards_def : edwards = ⟨a, d⟩ := by
  unfold edwards
  rfl

theorem edwards_a : edwards.a = a := by
  rw [edwards_def]

theorem edwards_d : edwards.d = d := by
  rw [edwards_def]

theorem edwards_a_eq_neg_one : edwards.a = -1 := by
  rw [edwards_a, a_def]

/-- `edwards` is complete: the affine points form the whole group and the addition formula has
no exceptional case. -/
instance instIsCompleteEdwards : edwards.IsComplete where
  two_ne_zero := two_ne_zero
  isSquare_a := edwards_a ▸ isSquare_a
  a_ne_zero := by
    rw [edwards_a_eq_neg_one]
    exact neg_ne_zero.mpr one_ne_zero
  not_isSquare_d := edwards_d ▸ not_isSquare_d

/-! ### The Montgomery model -/

theorem montgomery_def : montgomery = ⟨(A : ZMod p), 1⟩ := by
  unfold montgomery
  rfl

theorem montgomery_A : montgomery.A = (A : ZMod p) := by
  rw [montgomery_def]

theorem montgomery_A_eq : montgomery.A = 486662 := by
  rw [montgomery_A, A_def]
  rfl

theorem montgomery_B : montgomery.B = 1 := by
  rw [montgomery_def]

/-- `montgomery` is nonsingular: `A² ≠ 4`. -/
instance instIsNonsingularMontgomery : montgomery.IsNonsingular where
  two_ne_zero := two_ne_zero
  B_ne_zero := by
    rw [montgomery_B]
    exact one_ne_zero
  A_sq_ne_four := by
    rw [montgomery_A]
    exact A_sq_ne_four

/-! ### The curve -/

/-- The curve realised by `edwards` and by `montgomery`: curve25519 itself. -/
noncomputable def curve : Curve (ZMod p) := edwards.toCurve

theorem curve_def : curve = edwards.toCurve := by
  unfold curve
  rfl

theorem toCurve_edwards : edwards.toCurve = curve := by
  rw [curve_def]

/-- The Montgomery model of `edwards` has the coefficient `A` of `montgomery`. -/
theorem edwards_toMontgomery_A : edwards.toMontgomery.A = montgomery.A := by
  rw [TwistedEdwardsModel.toMontgomery_A, montgomery_A, edwards_a, edwards_d,
    div_eq_iff a_sub_d_ne_zero]
  exact two_mul_a_add_d

/-- The Montgomery model of `edwards` has `B = 4 / (a - d) = sqrtNegAAddTwo²`: it is the
rescaling of `montgomery` (`B = 1`) by `sqrtNegAAddTwo`. -/
theorem edwards_toMontgomery_B : edwards.toMontgomery.B = (sqrtNegAAddTwo : ZMod p) ^ 2 := by
  rw [TwistedEdwardsModel.toMontgomery_B, edwards_a, edwards_d, div_eq_iff a_sub_d_ne_zero]
  exact four_eq_sqrtNegAAddTwo_sq_mul

/-- `montgomery` realises the same curve as `edwards`. -/
theorem toCurve_montgomery : montgomery.toCurve = curve := by
  rw [← toCurve_edwards, ← TwistedEdwardsModel.toCurve_toMontgomery]
  exact (MontgomeryModel.toCurve_eq_of_B_eq_mul_sq montgomery edwards.toMontgomery
    edwards_toMontgomery_A sqrtNegAAddTwo_ne_zero
    (by rw [edwards_toMontgomery_B, montgomery_B, one_mul])).symm

end curve25519

namespace curve25519

open MontgomeryModel TwistedEdwardsModel

/-- `montgomery = (A, 1)` is the rescaling of the Montgomery model `(A, sqrtNegAAddTwo²)` of
`edwards` by `sqrtNegAAddTwo`. -/
theorem montgomery_B_mul_sqrtNegAAddTwo_sq :
    montgomery.B * (sqrtNegAAddTwo : ZMod p) ^ 2 = edwards.toMontgomery.B := by
  rw [montgomery_B, edwards_toMontgomery_B, one_mul]

end curve25519
