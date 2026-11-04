/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar
import Proofs.Scalar.Eq
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreCmpPartialEqHalfWidthScalar

@[step]
theorem eq_spec (self other : HalfWidthScalar) :
    eq self other ⦃ (b : Bool) =>
      (b = true ↔ self = other) ⦄ := by
  unfold eq
  step*

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreCmpPartialEqHalfWidthScalar
