/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
import Proofs.Edwards.BasepointTableClone
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.ristretto

/-- `Clone for RistrettoBasepointTable`: the table itself. -/
@[step]
theorem RistrettoBasepointTable.«64bit-tables».Insts.CoreCloneClone.clone_spec
    (self : RistrettoBasepointTable.«64bit-tables») :
    RistrettoBasepointTable.«64bit-tables».Insts.CoreCloneClone.clone self ⦃ r => r = self ⦄ := by
  unfold RistrettoBasepointTable.«64bit-tables».Insts.CoreCloneClone.clone
  step with edwards.EdwardsBasepointTable.«64bit-tables».Insts.CoreCloneClone.clone_spec
    as ⟨ebt, h⟩
  exact h

/-- `Clone for RistrettoBasepointTable`: the table itself. -/
@[step]
theorem RistrettoBasepointTable.«32bit-tables».Insts.CoreCloneClone.clone_spec
    (self : RistrettoBasepointTable.«32bit-tables») :
    RistrettoBasepointTable.«32bit-tables».Insts.CoreCloneClone.clone self ⦃ r => r = self ⦄ := by
  unfold RistrettoBasepointTable.«32bit-tables».Insts.CoreCloneClone.clone
  step with edwards.EdwardsBasepointTable.«32bit-tables».Insts.CoreCloneClone.clone_spec
    as ⟨ebt, h⟩
  exact h

end Curve25519Dalek.ristretto
