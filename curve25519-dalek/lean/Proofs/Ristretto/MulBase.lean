/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Edwards.Basepoint
public import Defs.Edwards
public import Defs.Scalar
import Curve25519.Ristretto.Even
import Proofs.Constants.RistrettoBasepoint
import Proofs.Ristretto.BasepointTable
import Proofs.Ristretto.Mul
public section

/-! # `RistrettoPoint::mul_base`

With tables, `scalar * RISTRETTO_BASEPOINT_TABLE`; without, `scalar * RISTRETTO_BASEPOINT_POINT`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.ristretto

namespace «RistrettoPointx86_64-tables»

/-- `RistrettoPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`);
an even point (a ristretto255 representative); limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = scalar.asNat • basepoint ∧
        r.LimbsLt 52 ⦄ := by
  unfold mul_base
  step with constants.«x86_64-tables».RISTRETTO_BASEPOINT_TABLE_spec as ⟨t, ht, htb⟩
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact even_basepoint.nsmul_right _, h2, h3⟩

end «RistrettoPointx86_64-tables»

namespace «RistrettoPointi686-tables»

/-- `RistrettoPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`);
an even point (a ristretto255 representative); limbs `< 2^26`. -/
@[step]
theorem mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = scalar.asNat • basepoint ∧
        r.LimbsLt 26 ⦄ := by
  unfold mul_base
  step with constants.«i686-tables».RISTRETTO_BASEPOINT_TABLE_spec as ⟨t, ht, htb⟩
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact even_basepoint.nsmul_right _, h2, h3⟩

end «RistrettoPointi686-tables»

namespace «RistrettoPointx86_64-no-tables»

/-- `RistrettoPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`);
an even point (a ristretto255 representative); limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = scalar.asNat • basepoint ∧
        r.LimbsLt 52 ⦄ := by
  unfold mul_base
  step with constants.«x86_64-no-tables».RISTRETTO_BASEPOINT_POINT_spec as ⟨p, hp_on, _, hp, hpb⟩
  step as ⟨r, h1, h2, h3⟩
  refine (fun h => ⟨h1, by rw [h]; exact even_basepoint.nsmul_right _, h, h3⟩) ?_
  rw [h2, hp]

end «RistrettoPointx86_64-no-tables»

namespace «RistrettoPointi686-no-tables»

/-- `RistrettoPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`);
an even point (a ristretto255 representative); limbs `< 2^26`. -/
@[step]
theorem mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = scalar.asNat • basepoint ∧
        r.LimbsLt 26 ⦄ := by
  unfold mul_base
  step with constants.«i686-no-tables».RISTRETTO_BASEPOINT_POINT_spec as ⟨p, hp_on, _, hp, hpb⟩
  step as ⟨r, h1, h2, h3⟩
  refine (fun h => ⟨h1, by rw [h]; exact even_basepoint.nsmul_right _, h, h3⟩) ?_
  rw [h2, hp]

end «RistrettoPointi686-no-tables»

end Curve25519Dalek.ristretto
