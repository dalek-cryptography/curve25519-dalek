/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar
import Proofs.Scalar.Zero
public import Proofs.Helpers.ByteValues
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.HalfWidthScalar

theorem ZERO_spec :
    ZERO.asNat < 2 ^ 128 ∧ ZERO.asNat = 0 := by
  have h : ZERO.asNat = 0 := by simp [HalfWidthScalar.asNat_def, ZERO, Scalar.ZERO_spec]
  exact ⟨by rw [h]; norm_num, h⟩

end Curve25519Dalek.scalar.HalfWidthScalar
