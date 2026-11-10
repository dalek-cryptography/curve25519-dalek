/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar
import Proofs.Scalar.Zero
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreDefaultDefault

@[step]
theorem default_spec :
    default ⦃ (r : Scalar) =>
      r.asNat = 0 ⦄ := by
  unfold default
  simp [ZERO_spec]

end Curve25519Dalek.scalar.Scalar.Insts.CoreDefaultDefault
