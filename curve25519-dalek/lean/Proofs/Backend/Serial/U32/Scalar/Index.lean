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

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29.Insts.CoreOpsIndexIndexUsizeU32

@[step]
theorem index_spec (self : Scalar29) (index : Usize) (hindex : index.val < 9) :
    CoreOpsIndexIndexUsizeU32.index self index ⦃ (r : U32) =>
      r = self[index.val]! ⦄ := by
  unfold CoreOpsIndexIndexUsizeU32.index
  step*
  simp_lists [*]

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29.Insts.CoreOpsIndexIndexUsizeU32
