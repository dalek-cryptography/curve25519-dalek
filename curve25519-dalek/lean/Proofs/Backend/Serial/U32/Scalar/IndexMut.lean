/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar29
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29)

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29.Insts.CoreOpsIndexIndexMutUsizeU32

@[step]
theorem index_mut_spec (self : Scalar29) (index : Usize) (hindex : index.val < 9) :
    index_mut self index ⦃ (r : U32) (back : U32 → Scalar29) =>
      r = self[index.val]! ∧ ∀ x, back x = self.set index x ⦄ := by
  unfold index_mut
  step*
  subst_vars
  exact ⟨by simp_lists, fun _ => rfl⟩

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29.Insts.CoreOpsIndexIndexMutUsizeU32
