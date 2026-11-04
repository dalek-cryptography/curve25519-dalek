/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar52
import Mathlib.Tactic.ReduceModChar
import Proofs.Helpers.Bytes
import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU8

@[step]
theorem from_spec (x : U8) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.val ⦄ := by
  unfold «from»
  step*
  simp [Scalar.asNat_def, Array.asNat_def, Nat.ofDigits, *]

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU8

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU16

@[step]
theorem from_spec (x : U16) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.val ⦄ := by
  unfold «from»
  step*
  rw [Scalar.asNat_def, ← UScalar.bv_toNat]
  apply Array.asNat_setSlice!_toLEBytes _ x.bv (by simp)
  simp_all

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU16

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU32

@[step]
theorem from_spec (x : U32) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.val ⦄ := by
  unfold «from»
  step*
  rw [Scalar.asNat_def, ← UScalar.bv_toNat]
  apply Array.asNat_setSlice!_toLEBytes _ x.bv (by simp)
  simp_all

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU32

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU64

@[step]
theorem from_spec (x : U64) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.val ⦄ := by
  unfold «from»
  step*
  rw [Scalar.asNat_def, ← UScalar.bv_toNat]
  apply Array.asNat_setSlice!_toLEBytes _ x.bv (by simp)
  simp_all

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU64

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU128

@[step]
theorem from_spec (x : U128) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.val ⦄ := by
  unfold «from»
  step*
  rw [Scalar.asNat_def, ← UScalar.bv_toNat]
  apply Array.asNat_setSlice!_toLEBytes _ x.bv (by simp)
  simp_all

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU128
