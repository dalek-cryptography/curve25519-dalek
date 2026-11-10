/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
import Proofs.Scalar.Sub
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar)

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubAssignSharedAScalar

@[step]
theorem sub_assign_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    sub_assign self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄ := by
  unfold sub_assign
  step*

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubAssignSharedAScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubAssignScalar

/-- `SubAssign<Scalar> for Scalar` (from `define_sub_assign_variants!`): forwards to the
`&Scalar` version. -/
@[step]
theorem sub_assign_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    sub_assign self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄ := by
  unfold sub_assign
  step*

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubAssignScalar
