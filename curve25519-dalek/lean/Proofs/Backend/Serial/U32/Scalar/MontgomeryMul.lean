/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar29
import Proofs.Backend.Serial.U32.Scalar.MontgomeryReduce
import Proofs.Backend.Serial.U32.Scalar.MulInternal
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29)

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

@[step]
theorem montgomery_mul_spec (a b : Scalar29) (ha : a.LimbsLt 29)
    (hb : b.LimbsLt 29) (hab : a.asNat * b.asNat < montgomeryRadix * L) :
    montgomery_mul a b ⦃ (r : Scalar29) =>
      r.asNat * montgomeryRadix % L = a.asNat * b.asNat % L ∧ r.asNat < L ∧
      r.LimbsLt 29 ⦄ := by
  unfold montgomery_mul
  step with mul_internal_spec a b ha hb as ⟨ab, hab_eq, hab_lt⟩
  step with montgomery_reduce_spec ab (fun i hi => (hab_lt i hi).trans (by decide))
    (hab_eq ▸ hab) as ⟨r, hr, hrL, hr_lt⟩
  exact ⟨hab_eq ▸ hr, hrL, hr_lt⟩

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29
