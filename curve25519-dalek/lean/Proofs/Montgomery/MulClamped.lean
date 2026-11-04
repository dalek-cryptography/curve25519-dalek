/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Montgomery
import Proofs.Montgomery.Mul
import Proofs.Scalar.ClampInteger
public section

/-! # `MontgomeryPoint::mul_clamped`

RFC 7748 `X25519(k, u)` byte for byte: the clamped scalar is below `2^255`, so the ladder over
`255` bits sees all of it. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.montgomery.MontgomeryPoint

/-- `MontgomeryPoint::mul_clamped`: RFC 7748 `X25519(bytes, self)`. -/
@[step]
theorem mul_clamped_spec (self : MontgomeryPoint) (bytes : Array U8 32#usize) :
    mul_clamped self bytes ⦃ (r : MontgomeryPoint) =>
      r.asNat = x25519 (bytes.asNat 8) self.asNat ⦄ := by
  unfold mul_clamped
  step as ⟨a, ha⟩
  step with scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint.mul_spec
    { bytes := a } self as ⟨r, hr⟩
  have hca : ({ bytes := a } : scalar.Scalar).asNat = clamp (bytes.asNat 8) := by
    have := clamp_add_mod_eight (bytes.asNat 8)
    rw [scalar.Scalar.asNat_def]
    change a.asNat 8 = _
    omega
  rw [hr, hca, Nat.mod_eq_of_lt (clamp_lt _), x25519, MontgomeryPoint.u_def]

end Curve25519Dalek.montgomery.MontgomeryPoint
