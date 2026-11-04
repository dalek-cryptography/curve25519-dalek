/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
import Proofs.Scalar.Add
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar)

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddAssignSharedAScalar

@[step]
theorem add_assign_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    add_assign self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄ := by
  unfold add_assign
  step*

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddAssignSharedAScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddAssignScalar

/-- `AddAssign<Scalar> for Scalar` (from `define_add_assign_variants!`): forwards to the
`&Scalar` version. -/
@[step]
theorem add_assign_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    add_assign self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄ := by
  unfold add_assign
  step*

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddAssignScalar
