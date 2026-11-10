/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Basic
public import Defs.Scalar52
import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64

@[step]
theorem index_mut_spec (self : Scalar52) (index : Usize) (hindex : index.val < 5) :
    index_mut self index ⦃ (r : U64) (back : U64 → Scalar52) =>
      r = self[index.val]! ∧ ∀ x, back x = self.set index x ⦄ := by
  unfold index_mut
  step*
  subst_vars
  exact ⟨by simp_lists, fun _ => rfl⟩

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64
