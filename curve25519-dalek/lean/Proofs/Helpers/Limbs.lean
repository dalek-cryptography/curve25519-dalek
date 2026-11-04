/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.FieldElement51
public import Defs.Scalar52
import Proofs.Helpers.AsNat
public section

/-! # Lemmas shared by the proofs of the u64 backend

The values of a `FieldElement51` (radix `2^51`) and of a `Scalar52` (radix `2^52`), unfolded into
their five limbs. -/

open Aeneas Aeneas.Std

namespace Curve25519Dalek.backend.serial.u64

/-- The value of a `FieldElement51` from its five limbs. -/
theorem field.FieldElement51.asNat_eq (a : field.FieldElement51) :
    a.asNat = a[0]!.val + 2 ^ 51 * a[1]!.val + 2 ^ 102 * a[2]!.val + 2 ^ 153 * a[3]!.val
      + 2 ^ 204 * a[4]!.val := by
  simp only [field.FieldElement51.asNat_def, Array.asNat_five]

/-- The value of a `Scalar52` from its five limbs. -/
theorem scalar.Scalar52.asNat_eq (a : scalar.Scalar52) :
    a.asNat = a[0]!.val + 2 ^ 52 * a[1]!.val + 2 ^ 104 * a[2]!.val + 2 ^ 156 * a[3]!.val
      + 2 ^ 208 * a[4]!.val := by
  simp only [scalar.Scalar52.asNat_def, Array.asNat_five]

end Curve25519Dalek.backend.serial.u64
