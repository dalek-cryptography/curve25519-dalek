/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Zhang-Liao, Alessandro D'Angelo,
  Hoang Le Truong, Markus Ferdinand Dablander
-/
module
public import Curve25519Dalek.Funs
import Zeroize.Lemmas
@[expose] public section
open Aeneas Aeneas.Std Result Aeneas.Std.WP

/-! # `zeroize` for the trait instances generated in `Curve25519Dalek/Funs.lean` (no axioms) -/

namespace Curve25519Dalek

/-! ## Blanket impl for primitive types -/

@[step] theorem U8.Insts.ZeroizeDefaultIsZeroes.zeroize_spec (x : Std.U8) :
    _root_.zeroize.Zeroize.Blanket.zeroize U8.Insts.ZeroizeDefaultIsZeroes x
      ⦃ r => r = 0#u8 ⦄ := by
  rw [_root_.zeroize.Zeroize.Blanket.zeroize_eq]; exact (spec_ok _).mpr rfl

@[step] theorem U32.Insts.ZeroizeDefaultIsZeroes.zeroize_spec (x : Std.U32) :
    _root_.zeroize.Zeroize.Blanket.zeroize U32.Insts.ZeroizeDefaultIsZeroes x
      ⦃ r => r = 0#u32 ⦄ := by
  rw [_root_.zeroize.Zeroize.Blanket.zeroize_eq]; exact (spec_ok _).mpr rfl

@[step] theorem U64.Insts.ZeroizeDefaultIsZeroes.zeroize_spec (x : Std.U64) :
    _root_.zeroize.Zeroize.Blanket.zeroize U64.Insts.ZeroizeDefaultIsZeroes x
      ⦃ r => r = 0#u64 ⦄ := by
  rw [_root_.zeroize.Zeroize.Blanket.zeroize_eq]; exact (spec_ok _).mpr rfl

@[step] theorem I8.Insts.ZeroizeDefaultIsZeroes.zeroize_spec (x : Std.I8) :
    _root_.zeroize.Zeroize.Blanket.zeroize I8.Insts.ZeroizeDefaultIsZeroes x
      ⦃ r => r = 0#i8 ⦄ := by
  rw [_root_.zeroize.Zeroize.Blanket.zeroize_eq]; exact (spec_ok _).mpr rfl

@[step] theorem Bool.Insts.ZeroizeDefaultIsZeroes.zeroize_spec (x : Bool) :
    _root_.zeroize.Zeroize.Blanket.zeroize Bool.Insts.ZeroizeDefaultIsZeroes x
      ⦃ r => r = false ⦄ := by
  rw [_root_.zeroize.Zeroize.Blanket.zeroize_eq]; exact (spec_ok _).mpr rfl

/-! ## Arrays of primitive types -/

@[step] theorem Array.Insts.ZeroizeZeroize.zeroize_U8_spec {N : Std.Usize} (a : Array Std.U8 N) :
    _root_.Array.Insts.ZeroizeZeroize.zeroize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a
      ⦃ r => r = Array.repeat N 0#u8 ⦄ :=
  _root_.Array.Insts.ZeroizeZeroize.zeroize_const_spec _ _
    U8.Insts.ZeroizeDefaultIsZeroes.zeroize_spec a

@[step] theorem Array.Insts.ZeroizeZeroize.zeroize_U32_spec {N : Std.Usize} (a : Array Std.U32 N) :
    _root_.Array.Insts.ZeroizeZeroize.zeroize
      (zeroize.Zeroize.Blanket U32.Insts.ZeroizeDefaultIsZeroes) a
      ⦃ r => r = Array.repeat N 0#u32 ⦄ :=
  _root_.Array.Insts.ZeroizeZeroize.zeroize_const_spec _ _
    U32.Insts.ZeroizeDefaultIsZeroes.zeroize_spec a

@[step] theorem Array.Insts.ZeroizeZeroize.zeroize_U64_spec {N : Std.Usize} (a : Array Std.U64 N) :
    _root_.Array.Insts.ZeroizeZeroize.zeroize
      (zeroize.Zeroize.Blanket U64.Insts.ZeroizeDefaultIsZeroes) a
      ⦃ r => r = Array.repeat N 0#u64 ⦄ :=
  _root_.Array.Insts.ZeroizeZeroize.zeroize_const_spec _ _
    U64.Insts.ZeroizeDefaultIsZeroes.zeroize_spec a

/-! ## Backend field elements and scalars -/

@[step] theorem backend.serial.u64.field.FieldElement51.Insts.ZeroizeZeroize.zeroize_spec
    (x : backend.serial.u64.field.FieldElement51) :
    backend.serial.u64.field.FieldElement51.Insts.ZeroizeZeroize.zeroize x ⦃ r =>
      r = Array.repeat 5#usize 0#u64 ⦄ := by
  unfold backend.serial.u64.field.FieldElement51.Insts.ZeroizeZeroize.zeroize; step*

@[step] theorem backend.serial.u32.field.FieldElement2625.Insts.ZeroizeZeroize.zeroize_spec
    (x : backend.serial.u32.field.FieldElement2625) :
    backend.serial.u32.field.FieldElement2625.Insts.ZeroizeZeroize.zeroize x ⦃ r =>
      r = Array.repeat 10#usize 0#u32 ⦄ := by
  unfold backend.serial.u32.field.FieldElement2625.Insts.ZeroizeZeroize.zeroize; step*

@[step] theorem backend.serial.u64.scalar.Scalar52.Insts.ZeroizeZeroize.zeroize_spec
    (x : backend.serial.u64.scalar.Scalar52) :
    backend.serial.u64.scalar.Scalar52.Insts.ZeroizeZeroize.zeroize x ⦃ r =>
      r = Array.repeat 5#usize 0#u64 ⦄ := by
  unfold backend.serial.u64.scalar.Scalar52.Insts.ZeroizeZeroize.zeroize; step*

@[step] theorem backend.serial.u32.scalar.Scalar29.Insts.ZeroizeZeroize.zeroize_spec
    (x : backend.serial.u32.scalar.Scalar29) :
    backend.serial.u32.scalar.Scalar29.Insts.ZeroizeZeroize.zeroize x ⦃ r =>
      r = Array.repeat 9#usize 0#u32 ⦄ := by
  unfold backend.serial.u32.scalar.Scalar29.Insts.ZeroizeZeroize.zeroize; step*

/-! ## Byte-array types -/

@[step] theorem montgomery.MontgomeryPoint.Insts.ZeroizeZeroize.zeroize_spec
    (p : montgomery.MontgomeryPoint) :
    montgomery.MontgomeryPoint.Insts.ZeroizeZeroize.zeroize p ⦃ r =>
      r = Array.repeat 32#usize 0#u8 ⦄ := by
  unfold montgomery.MontgomeryPoint.Insts.ZeroizeZeroize.zeroize; step*

@[step] theorem ristretto.CompressedRistretto.Insts.ZeroizeZeroize.zeroize_spec
    (p : ristretto.CompressedRistretto) :
    ristretto.CompressedRistretto.Insts.ZeroizeZeroize.zeroize p ⦃ r =>
      r = Array.repeat 32#usize 0#u8 ⦄ := by
  unfold ristretto.CompressedRistretto.Insts.ZeroizeZeroize.zeroize; step*

@[step] theorem scalar.Scalar.Insts.ZeroizeZeroize.zeroize_spec (s : scalar.Scalar) :
    scalar.Scalar.Insts.ZeroizeZeroize.zeroize s ⦃ r =>
      r = { bytes := Array.repeat 32#usize 0#u8 } ⦄ := by
  unfold scalar.Scalar.Insts.ZeroizeZeroize.zeroize; step*

end Curve25519Dalek
