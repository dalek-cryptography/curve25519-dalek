/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar
import Proofs.Scalar.Default
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreDefaultDefault

@[step]
theorem default_spec :
    default ⦃ (r : HalfWidthScalar) =>
      r.asNat = 0 ⦄ := by
  unfold default
  step as ⟨s, hs⟩
  rw [scalar.HalfWidthScalar.asNat_def]
  exact hs

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreDefaultDefault
