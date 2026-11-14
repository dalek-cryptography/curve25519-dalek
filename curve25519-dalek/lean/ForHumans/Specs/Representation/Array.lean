/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
module
public import Mathlib.Data.Nat.Digits.Defs
public import Aeneas.Std.Array.Array
public section

/-! # The value of an array of digits (audited) -/

open Aeneas.Std

/-- The natural number with the array's elements as little-endian digits in radix `2^bits`:
`a[0] + 2^bits · a[1] + 2^(2 bits) · a[2] + …`. The digits may exceed `2^bits`.
Bytes use `bits = 8`. -/
def Aeneas.Std.Array.asNat {ty : UScalarTy} {n : Usize} (bits : ℕ) (a : Array (UScalar ty) n) : ℕ :=
  Nat.ofDigits (2 ^ bits) (a.val.map (·.val))

/-- The integer with the array's signed elements as little-endian digits in radix `2^bits`:
`a[0] + 2^bits · a[1] + 2^(2 bits) · a[2] + …`. Used for the signed-digit recodings of scalars. -/
def Aeneas.Std.Array.asInt {ty : IScalarTy} {n : Usize} (bits : ℕ) (a : Array (IScalar ty) n) : ℤ :=
  (a.val.map (·.val)).foldr (fun d acc => d + 2 ^ bits * acc) 0

theorem Aeneas.Std.Array.asNat_def {ty : UScalarTy} {n : Usize} (bits : ℕ)
    (a : Array (UScalar ty) n) : a.asNat bits = Nat.ofDigits (2 ^ bits) (a.val.map (·.val)) := by
  unfold Aeneas.Std.Array.asNat
  rfl

theorem Aeneas.Std.Array.asInt_def {ty : IScalarTy} {n : Usize} (bits : ℕ)
    (a : Array (IScalar ty) n) :
    a.asInt bits = (a.val.map (·.val)).foldr (fun d acc => d + 2 ^ bits * acc) 0 := by
  unfold Aeneas.Std.Array.asInt
  rfl
