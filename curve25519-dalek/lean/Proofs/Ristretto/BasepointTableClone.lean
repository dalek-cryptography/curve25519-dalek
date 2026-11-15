/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
import Proofs.Edwards.BasepointTableClone
public section

/-! # `Clone for RistrettoBasepointTable`

`#[derive(Clone)]` on the wrapper: the clone of the inner `EdwardsBasepointTable`, which is the
table itself. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.ristretto

/-- `Clone for RistrettoBasepointTable`: the table itself. -/
@[step]
theorem RistrettoBasepointTable.«x86_64-tables».Insts.CoreCloneClone.clone_spec
    (self : RistrettoBasepointTable.«x86_64-tables») :
    RistrettoBasepointTable.«x86_64-tables».Insts.CoreCloneClone.clone self ⦃ r => r = self ⦄ := by
  unfold RistrettoBasepointTable.«x86_64-tables».Insts.CoreCloneClone.clone
  step with edwards.EdwardsBasepointTable.«x86_64-tables».Insts.CoreCloneClone.clone_spec
    as ⟨ebt, h⟩
  exact h

/-- `Clone for RistrettoBasepointTable`: the table itself. -/
@[step]
theorem RistrettoBasepointTable.«i686-tables».Insts.CoreCloneClone.clone_spec
    (self : RistrettoBasepointTable.«i686-tables») :
    RistrettoBasepointTable.«i686-tables».Insts.CoreCloneClone.clone self ⦃ r => r = self ⦄ := by
  unfold RistrettoBasepointTable.«i686-tables».Insts.CoreCloneClone.clone
  step with edwards.EdwardsBasepointTable.«i686-tables».Insts.CoreCloneClone.clone_spec
    as ⟨ebt, h⟩
  exact h

end Curve25519Dalek.ristretto
