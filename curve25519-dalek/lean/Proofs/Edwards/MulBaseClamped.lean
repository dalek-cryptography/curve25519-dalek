/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Curve25519.Edwards.Basepoint
public import Proofs.Curve25519.X25519
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Edwards.MulBase
import Proofs.Scalar.ClampInteger
public import Proofs.Helpers.ByteValues
public section

/-! # `EdwardsPoint::mul_base_clamped` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards

namespace «EdwardsPoint64bit-tables»

/-- `EdwardsPoint::mul_base_clamped`: `clamp bytes • B`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^52`. -/
@[step]
theorem mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • basepoint ∧ r.LimbsLt 52 ⦄ := by
  simp only [Aeneas.Std.Array.decodeScalar25519_toVector]
  unfold mul_base_clamped
  step as ⟨a, ha⟩
  have hca : ({ bytes := a } : scalar.Scalar).asNat = clamp (bytes.asNat 8) := by
    have := clamp_add_mod_eight (bytes.asNat 8)
    rw [scalar.Scalar.asNat_def]
    change a.asNat 8 = _
    omega
  step with mul_base_spec _ (hca ▸ clamp_lt _) as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hca ▸ hr, hrb⟩

end «EdwardsPoint64bit-tables»

namespace «EdwardsPoint32bit-tables»

/-- `EdwardsPoint::mul_base_clamped`: `clamp bytes • B`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^26`. -/
@[step]
theorem mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • basepoint ∧ r.LimbsLt 26 ⦄ := by
  simp only [Aeneas.Std.Array.decodeScalar25519_toVector]
  unfold mul_base_clamped
  step as ⟨a, ha⟩
  have hca : ({ bytes := a } : scalar.Scalar).asNat = clamp (bytes.asNat 8) := by
    have := clamp_add_mod_eight (bytes.asNat 8)
    rw [scalar.Scalar.asNat_def]
    change a.asNat 8 = _
    omega
  step with mul_base_spec _ (hca ▸ clamp_lt _) as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hca ▸ hr, hrb⟩

end «EdwardsPoint32bit-tables»

namespace «EdwardsPoint64bit-notables»

/-- `EdwardsPoint::mul_base_clamped`: `clamp bytes • B`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^52`. -/
@[step]
theorem mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • basepoint ∧ r.LimbsLt 52 ⦄ := by
  simp only [Aeneas.Std.Array.decodeScalar25519_toVector]
  unfold mul_base_clamped
  step as ⟨a, ha⟩
  have hca : ({ bytes := a } : scalar.Scalar).asNat = clamp (bytes.asNat 8) := by
    have := clamp_add_mod_eight (bytes.asNat 8)
    rw [scalar.Scalar.asNat_def]
    change a.asNat 8 = _
    omega
  step with mul_base_spec _ (hca ▸ clamp_lt _) as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hca ▸ hr, hrb⟩

end «EdwardsPoint64bit-notables»

namespace «EdwardsPoint32bit-notables»

/-- `EdwardsPoint::mul_base_clamped`: `clamp bytes • B`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^26`. -/
@[step]
theorem mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • basepoint ∧ r.LimbsLt 26 ⦄ := by
  simp only [Aeneas.Std.Array.decodeScalar25519_toVector]
  unfold mul_base_clamped
  step as ⟨a, ha⟩
  have hca : ({ bytes := a } : scalar.Scalar).asNat = clamp (bytes.asNat 8) := by
    have := clamp_add_mod_eight (bytes.asNat 8)
    rw [scalar.Scalar.asNat_def]
    change a.asNat 8 = _
    omega
  step with mul_base_spec _ (hca ▸ clamp_lt _) as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hca ▸ hr, hrb⟩

end «EdwardsPoint32bit-notables»

end Curve25519Dalek.edwards
