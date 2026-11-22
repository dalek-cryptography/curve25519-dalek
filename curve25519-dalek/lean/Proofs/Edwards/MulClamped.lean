/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Curve25519.X25519
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Edwards.Mul
import Proofs.Scalar.ClampInteger
public import Proofs.Helpers.ByteValues
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards

namespace «EdwardsPoint64bit-tables»

/-- `EdwardsPoint::mul_clamped`: `clamp bytes • self`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^52`. -/
@[step]
theorem mul_clamped_spec (self : EdwardsPoint.«64bit-tables») (bytes : Array U8 32#usize)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) :
    mul_clamped self bytes ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  simp only [Aeneas.Std.Array.decodeScalar25519_toVector]
  unfold mul_clamped
  step as ⟨a, ha⟩
  have hca : ({ bytes := a } : scalar.Scalar).asNat = clamp (bytes.asNat 8) := by
    have := clamp_add_mod_eight (bytes.asNat 8)
    rw [scalar.Scalar.asNat_def]
    change a.asNat 8 = _
    omega
  have hlt : ({ bytes := a } : scalar.Scalar).asNat < 2 ^ 255 := hca ▸ clamp_lt _
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hca ▸ hr, hrb⟩

end «EdwardsPoint64bit-tables»

namespace «EdwardsPoint32bit-tables»

/-- `EdwardsPoint::mul_clamped`: `clamp bytes • self`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^26`. -/
@[step]
theorem mul_clamped_spec (self : EdwardsPoint.«32bit-tables») (bytes : Array U8 32#usize)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) :
    mul_clamped self bytes ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  simp only [Aeneas.Std.Array.decodeScalar25519_toVector]
  unfold mul_clamped
  step as ⟨a, ha⟩
  have hca : ({ bytes := a } : scalar.Scalar).asNat = clamp (bytes.asNat 8) := by
    have := clamp_add_mod_eight (bytes.asNat 8)
    rw [scalar.Scalar.asNat_def]
    change a.asNat 8 = _
    omega
  have hlt : ({ bytes := a } : scalar.Scalar).asNat < 2 ^ 255 := hca ▸ clamp_lt _
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hca ▸ hr, hrb⟩

end «EdwardsPoint32bit-tables»

namespace «EdwardsPoint64bit-notables»

/-- `EdwardsPoint::mul_clamped`: `clamp bytes • self`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^52`. -/
@[step]
theorem mul_clamped_spec (self : EdwardsPoint.«64bit-notables») (bytes : Array U8 32#usize)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) :
    mul_clamped self bytes ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  simp only [Aeneas.Std.Array.decodeScalar25519_toVector]
  unfold mul_clamped
  step as ⟨a, ha⟩
  have hca : ({ bytes := a } : scalar.Scalar).asNat = clamp (bytes.asNat 8) := by
    have := clamp_add_mod_eight (bytes.asNat 8)
    rw [scalar.Scalar.asNat_def]
    change a.asNat 8 = _
    omega
  have hlt : ({ bytes := a } : scalar.Scalar).asNat < 2 ^ 255 := hca ▸ clamp_lt _
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hca ▸ hr, hrb⟩

end «EdwardsPoint64bit-notables»

namespace «EdwardsPoint32bit-notables»

/-- `EdwardsPoint::mul_clamped`: `clamp bytes • self`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^26`. -/
@[step]
theorem mul_clamped_spec (self : EdwardsPoint.«32bit-notables») (bytes : Array U8 32#usize)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) :
    mul_clamped self bytes ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  simp only [Aeneas.Std.Array.decodeScalar25519_toVector]
  unfold mul_clamped
  step as ⟨a, ha⟩
  have hca : ({ bytes := a } : scalar.Scalar).asNat = clamp (bytes.asNat 8) := by
    have := clamp_add_mod_eight (bytes.asNat 8)
    rw [scalar.Scalar.asNat_def]
    change a.asNat 8 = _
    omega
  have hlt : ({ bytes := a } : scalar.Scalar).asNat < 2 ^ 255 := hca ▸ clamp_lt _
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hca ▸ hr, hrb⟩

end «EdwardsPoint32bit-notables»

end Curve25519Dalek.edwards
