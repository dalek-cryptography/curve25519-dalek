/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Edwards.Mul
import Proofs.Scalar.ClampInteger
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

/-- `EdwardsPoint::mul_clamped`: `clamp bytes • P`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^52`. -/
@[step]
theorem mul_clamped_spec (self : EdwardsPoint.«x86_64-tables») (bytes : Array U8 32#usize)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) :
    mul_clamped self bytes ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = clamp (bytes.asNat 8) • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
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

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

/-- `EdwardsPoint::mul_clamped`: `clamp bytes • P`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^26`. -/
@[step]
theorem mul_clamped_spec (self : EdwardsPoint.«i686-tables») (bytes : Array U8 32#usize)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) :
    mul_clamped self bytes ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = clamp (bytes.asNat 8) • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
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

end «EdwardsPointi686-tables»

namespace «EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::mul_clamped`: `clamp bytes • P`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^52`. -/
@[step]
theorem mul_clamped_spec (self : EdwardsPoint.«x86_64-no-tables») (bytes : Array U8 32#usize)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) :
    mul_clamped self bytes ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = clamp (bytes.asNat 8) • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
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

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

/-- `EdwardsPoint::mul_clamped`: `clamp bytes • P`, with RFC 7748's clamping of the
little-endian value of `bytes`; limbs `< 2^26`. -/
@[step]
theorem mul_clamped_spec (self : EdwardsPoint.«i686-no-tables») (bytes : Array U8 32#usize)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) :
    mul_clamped self bytes ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = clamp (bytes.asNat 8) • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
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

end «EdwardsPointi686-no-tables»

end Curve25519Dalek.edwards
