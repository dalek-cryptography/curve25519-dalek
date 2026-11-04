/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar
import Mathlib.Tactic.ReduceModChar
import Proofs.Helpers.Bytes
import Proofs.Scalar.HalfWidthFromBytes
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU8

@[step]
theorem from_spec (x : U8) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄ := by
  have key (a : Array U8 16#usize)
      (h : a.val = (List.replicate 16 0#u8).setSlice! 0 (x.bv.toLEBytes.map UScalar.mk)) :
      a.asNat 8 = x.val := by
    rw [← UScalar.bv_toNat]
    exact Array.asNat_setSlice!_toLEBytes a x.bv (by simp) h
  unfold «from»
  step*
  simp_all

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU8

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU16

@[step]
theorem from_spec (x : U16) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄ := by
  have key (a : Array U8 16#usize)
      (h : a.val = (List.replicate 16 0#u8).setSlice! 0 (x.bv.toLEBytes.map UScalar.mk)) :
      a.asNat 8 = x.val := by
    rw [← UScalar.bv_toNat]
    exact Array.asNat_setSlice!_toLEBytes a x.bv (by simp) h
  unfold «from»
  step*
  simp_all

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU16

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU32

@[step]
theorem from_spec (x : U32) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄ := by
  have key (a : Array U8 16#usize)
      (h : a.val = (List.replicate 16 0#u8).setSlice! 0 (x.bv.toLEBytes.map UScalar.mk)) :
      a.asNat 8 = x.val := by
    rw [← UScalar.bv_toNat]
    exact Array.asNat_setSlice!_toLEBytes a x.bv (by simp) h
  unfold «from»
  step*
  simp_all

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU32

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU64

@[step]
theorem from_spec (x : U64) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄ := by
  have key (a : Array U8 16#usize)
      (h : a.val = (List.replicate 16 0#u8).setSlice! 0 (x.bv.toLEBytes.map UScalar.mk)) :
      a.asNat 8 = x.val := by
    rw [← UScalar.bv_toNat]
    exact Array.asNat_setSlice!_toLEBytes a x.bv (by simp) h
  unfold «from»
  step*
  simp_all

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU64

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU128

@[step]
theorem from_spec (x : U128) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄ := by
  have key (a : Array U8 16#usize)
      (h : a.val = (List.replicate 16 0#u8).setSlice! 0 (x.bv.toLEBytes.map UScalar.mk)) :
      a.asNat 8 = x.val := by
    rw [← UScalar.bv_toNat]
    exact Array.asNat_setSlice!_toLEBytes a x.bv (by simp) h
  unfold «from»
  step*
  simp_all

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU128
