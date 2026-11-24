module
public import Proofs.Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
import Proofs.Backend.Serial.U64.Constants.Ed25519BasepointPoint
import Proofs.Backend.Serial.U64.Constants.Ed25519BasepointTable
import Proofs.Edwards.BasepointTableMul
import Proofs.Edwards.Mul
import Proofs.Backend.Serial.U32.Constants.Ed25519BasepointPoint
import Proofs.Backend.Serial.U32.Constants.Ed25519BasepointTable
public section

/-! # `EdwardsPoint::mul_base`

In the `64bit-notables` configuration `mul_base` is `scalar * ED25519_BASEPOINT_POINT`. The
`64bit-tables` configuration multiplies with the precomputed `ED25519_BASEPOINT_TABLE` instead
(certified in `Proofs/Backend/Serial/U64/Constants/Ed25519BasepointTable.lean`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards

namespace «EdwardsPoint64bit-tables»

/-- `EdwardsPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`);
limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base
  step*

end «EdwardsPoint64bit-tables»

namespace «EdwardsPoint32bit-tables»

/-- `EdwardsPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`);
limbs `< 2^26`. -/
@[step]
theorem mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base
  step*

end «EdwardsPoint32bit-tables»

namespace «EdwardsPoint64bit-notables»

/-- `EdwardsPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`);
limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base
  step with backend.serial.u64.constants.«64bit-notables».ED25519_BASEPOINT_POINT_spec
    as ⟨ep, hepon, hep, hepb⟩
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hep ▸ hr, hrb⟩

end «EdwardsPoint64bit-notables»

namespace «EdwardsPoint32bit-notables»

/-- `EdwardsPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`);
limbs `< 2^26`. -/
@[step]
theorem mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base
  step with backend.serial.u32.constants.«32bit-notables».ED25519_BASEPOINT_POINT_spec
    as ⟨ep, hepon, hep, hepb⟩
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hep ▸ hr, hrb⟩

end «EdwardsPoint32bit-notables»

end Curve25519Dalek.edwards
