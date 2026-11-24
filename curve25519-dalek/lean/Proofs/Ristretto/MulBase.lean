module
public import Curve25519Dalek.Funs
public import Proofs.Curve25519.Edwards.Basepoint
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
import Proofs.Curve25519.Ristretto.Even
import Proofs.Constants.RistrettoBasepoint
import Proofs.Ristretto.BasepointTable
import Proofs.Ristretto.Mul
public section

/-! # `RistrettoPoint::mul_base`

With tables, `scalar * RISTRETTO_BASEPOINT_TABLE`; without, `scalar * RISTRETTO_BASEPOINT_POINT`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.ristretto

namespace «RistrettoPoint64bit-tables»

/-- `RistrettoPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`);
an even point (a ristretto255 representative); limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = scalar.asNat • basepoint ∧
        r.LimbsLt 52 ⦄ := by
  unfold mul_base
  step with constants.«64bit-tables».RISTRETTO_BASEPOINT_TABLE_spec as ⟨t, ht, htp, htb⟩
  step as ⟨r, h1, h2, h3⟩
  rw [htp] at h2
  exact ⟨h1, by rw [h2]; exact even_basepoint.nsmul_right _, h2, h3⟩

end «RistrettoPoint64bit-tables»

namespace «RistrettoPoint32bit-tables»

/-- `RistrettoPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`);
an even point (a ristretto255 representative); limbs `< 2^26`. -/
@[step]
theorem mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = scalar.asNat • basepoint ∧
        r.LimbsLt 26 ⦄ := by
  unfold mul_base
  step with constants.«32bit-tables».RISTRETTO_BASEPOINT_TABLE_spec as ⟨t, ht, htp, htb⟩
  step as ⟨r, h1, h2, h3⟩
  rw [htp] at h2
  exact ⟨h1, by rw [h2]; exact even_basepoint.nsmul_right _, h2, h3⟩

end «RistrettoPoint32bit-tables»

namespace «RistrettoPoint64bit-notables»

/-- `RistrettoPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`);
an even point (a ristretto255 representative); limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = scalar.asNat • basepoint ∧
        r.LimbsLt 52 ⦄ := by
  unfold mul_base
  step with constants.«64bit-notables».RISTRETTO_BASEPOINT_POINT_spec as ⟨p, hp_on, _, hp, hpb⟩
  step as ⟨r, h1, h2, h3⟩
  refine (fun h => ⟨h1, by rw [h]; exact even_basepoint.nsmul_right _, h, h3⟩) ?_
  rw [h2, hp]

end «RistrettoPoint64bit-notables»

namespace «RistrettoPoint32bit-notables»

/-- `RistrettoPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`);
an even point (a ristretto255 representative); limbs `< 2^26`. -/
@[step]
theorem mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = scalar.asNat • basepoint ∧
        r.LimbsLt 26 ⦄ := by
  unfold mul_base
  step with constants.«32bit-notables».RISTRETTO_BASEPOINT_POINT_spec as ⟨p, hp_on, _, hp, hpb⟩
  step as ⟨r, h1, h2, h3⟩
  refine (fun h => ⟨h1, by rw [h]; exact even_basepoint.nsmul_right _, h, h3⟩) ?_
  rw [h2, hp]

end «RistrettoPoint32bit-notables»

end Curve25519Dalek.ristretto
