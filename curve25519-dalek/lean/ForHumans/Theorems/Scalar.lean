/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Curve25519.Basic
public import Curve25519Dalek.Funs
public import Proofs.ToAeneas.Iterator
public import ForHumans.Specs.Representation.Scalar
public import Proofs.External.Subtle
import Proofs
import Proofs.External.Zeroize.Instances
public section

/-! # Specs of `src/scalar.rs`

The public items of `scalar.rs`, in its order.

A `Scalar` is specified by its value `asNat`, the number its 32 bytes encode little-endian, which
need not be reduced modulo the group order `L`. A `HalfWidthScalar` is a `Scalar` whose value is
below `2^128`; the Lean type does not carry the bound: its constructors state it and its consumers
assume it.

Definitions used: `Scalar.asNat`, `HalfWidthScalar.asNat`
(`ForHumans/Specs/Representation/Scalar.lean`), `Array.asNat`
(`ForHumans/Specs/Representation/Array.lean`), `Iterator.Yields` (`Proofs/ToAeneas/Iterator.lean`),
`L` (`Proofs/Curve25519/Basic.lean`), `subtle.Choice.IsValid`, `subtle.CtOption` (`Subtle/`).

Not specified: derived `Clone`/`Copy` impls, and items outside the public API (`reduce`,
`as_radix_16`, …), which are proved in `Proofs/Scalar/`. Not translated: `Debug`, `Hash`,
`from_bits`, `random`, `hash_from_bytes`, `from_hash`, the `group` and `serde` impls. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)

namespace Theorems.scalar.Scalar

/-- `from_bytes_mod_order`: the 256-bit little-endian value reduced modulo `L`. -/
theorem from_bytes_mod_order (bytes : Array U8 32#usize) :
    Scalar.from_bytes_mod_order bytes ⦃ (r : Scalar) => r.asNat = bytes.asNat 8 % L ⦄ :=
  Scalar.from_bytes_mod_order_spec bytes

/-- `from_bytes_mod_order_wide`: the 512-bit little-endian value reduced modulo `L`. -/
theorem from_bytes_mod_order_wide (input : Array U8 64#usize) :
    Scalar.from_bytes_mod_order_wide input ⦃ (r : Scalar) => r.asNat = input.asNat 8 % L ⦄ :=
  Scalar.from_bytes_mod_order_wide_spec input

/-- `from_canonical_bytes`: `Some` exactly for canonical encodings (value below `L`). -/
theorem from_canonical_bytes (bytes : Array U8 32#usize) :
    Scalar.from_canonical_bytes bytes ⦃ (r : subtle.CtOption Scalar) =>
      r.is_some.IsValid ∧ r.value.bytes = bytes ∧
      (bytes.asNat 8 < L → r.is_some = 1#u8) ∧ (L ≤ bytes.asNat 8 → r.is_some = 0#u8) ⦄ :=
  Scalar.from_canonical_bytes_spec bytes

/-- `PartialEq`: equality of the byte encodings. -/
theorem eq (a b : Scalar) :
    Scalar.Insts.CoreCmpPartialEqScalar.eq a b ⦃ (r : Bool) => r = true ↔ a = b ⦄ :=
  Scalar.Insts.CoreCmpPartialEqScalar.eq_spec a b

/-- `ConstantTimeEq`: `1` iff the byte encodings are equal. -/
theorem ct_eq (a b : Scalar) :
    Scalar.Insts.SubtleConstantTimeEq.ct_eq a b ⦃ (r : subtle.Choice) =>
      r.IsValid ∧ (a = b → r = 1#u8) ∧ (a ≠ b → r = 0#u8) ⦄ :=
  Scalar.Insts.SubtleConstantTimeEq.ct_eq_spec a b

/-- `Index<usize>`: byte `index`. -/
theorem index (s : Scalar) (index : Usize) (hindex : index.val < 32) :
    Scalar.Insts.CoreOpsIndexIndexUsizeU8.index s index ⦃ (r : U8) =>
      r = s.bytes[index.val]! ⦄ :=
  Scalar.Insts.CoreOpsIndexIndexUsizeU8.index_spec s index hindex

/-- `Mul` and `MulAssign`: the product modulo `L`. -/
theorem mul (a b : Scalar) :
    ∀ mul ∈ [
        Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar.mul, -- &a * &b
        Scalar.Insts.CoreOpsArithMulSharedBScalarScalar.mul, -- a * &b
        SharedAScalar.Insts.CoreOpsArithMulScalarScalar.mul, -- &a * b
        Scalar.Insts.CoreOpsArithMulScalarScalar.mul, -- a * b
        Scalar.Insts.CoreOpsArithMulAssignSharedAScalar.mul_assign, -- a *= &b
        Scalar.Insts.CoreOpsArithMulAssignScalar.mul_assign], -- a *= b
      mul a b ⦃ (r : Scalar) => r.asNat = a.asNat * b.asNat % L ⦄ := by
  variants [Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar.mul_spec]

/-- `Add` and `AddAssign`: the sum modulo `L`, for reduced inputs. -/
theorem add (a b : Scalar) (ha : a.asNat < L) (hb : b.asNat < L) :
    ∀ add ∈ [
        Shared0Scalar.Insts.CoreOpsArithAddSharedAScalarScalar.add, -- &a + &b
        Scalar.Insts.CoreOpsArithAddSharedBScalarScalar.add, -- a + &b
        SharedAScalar.Insts.CoreOpsArithAddScalarScalar.add, -- &a + b
        Scalar.Insts.CoreOpsArithAddScalarScalar.add, -- a + b
        Scalar.Insts.CoreOpsArithAddAssignSharedAScalar.add_assign, -- a += &b
        Scalar.Insts.CoreOpsArithAddAssignScalar.add_assign], -- a += b
      add a b ⦃ (r : Scalar) => r.asNat = (a.asNat + b.asNat) % L ⦄ := by
  variants [Shared0Scalar.Insts.CoreOpsArithAddSharedAScalarScalar.add_spec]

/-- `Sub` and `SubAssign`: the difference modulo `L`, reduced, for reduced inputs. -/
theorem sub (a b : Scalar) (ha : a.asNat < L) (hb : b.asNat < L) :
    ∀ sub ∈ [
        Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar.sub, -- &a - &b
        Scalar.Insts.CoreOpsArithSubSharedBScalarScalar.sub, -- a - &b
        SharedAScalar.Insts.CoreOpsArithSubScalarScalar.sub, -- &a - b
        Scalar.Insts.CoreOpsArithSubScalarScalar.sub, -- a - b
        Scalar.Insts.CoreOpsArithSubAssignSharedAScalar.sub_assign, -- a -= &b
        Scalar.Insts.CoreOpsArithSubAssignScalar.sub_assign], -- a -= b
      sub a b ⦃ (r : Scalar) => (r.asNat + b.asNat) % L = a.asNat ∧ r.asNat < L ⦄ := by
  variants [Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar.sub_spec]

/-- `Neg`: the negation modulo `L`, reduced. -/
theorem neg (a : Scalar) :
    ∀ neg ∈ [
        Shared0Scalar.Insts.CoreOpsArithNegScalar.neg, -- -&a
        Scalar.Insts.CoreOpsArithNegScalar.neg], -- -a
      neg a ⦃ (r : Scalar) => (r.asNat + a.asNat) % L = 0 ∧ r.asNat < L ⦄ := by
  variants [Shared0Scalar.Insts.CoreOpsArithNegScalar.neg_spec]

/-- `ConditionallySelectable`: `a` if `choice = 0`, `b` if `choice = 1`, for a valid `choice`. -/
theorem conditional_select (a b : Scalar) (choice : subtle.Choice) (hchoice : choice.IsValid) :
    Scalar.Insts.SubtleConditionallySelectable.conditional_select a b choice ⦃ (r : Scalar) =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  Scalar.Insts.SubtleConditionallySelectable.conditional_select_spec a b choice hchoice

/-- `Product`: the product of the items modulo `L`. The items are given by the list `xs` that the
iterator yields, and `ss`, the scalars they borrow as. -/
theorem product {T I : Type} (borrowInst : core.borrow.Borrow T Scalar)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ss : List Scalar) (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂ (fun x s => borrowInst.borrow x ⦃ (s' : Scalar) => s' = s ⦄) xs ss) :
    Scalar.Insts.CoreIterTraitsAccumProduct.product borrowInst iterInst iter ⦃ (r : Scalar) =>
      r.asNat = (ss.map (·.asNat)).prod % L ⦄ :=
  Scalar.Insts.CoreIterTraitsAccumProduct.product_spec borrowInst iterInst iter xs ss hiter hborrow

/-- `Sum`: the sum of the items modulo `L`, for reduced items (given as for `product`). -/
theorem sum {T I : Type} (borrowInst : core.borrow.Borrow T Scalar)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ss : List Scalar) (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂ (fun x s => borrowInst.borrow x ⦃ (s' : Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < L) :
    Scalar.Insts.CoreIterTraitsAccumSum.sum borrowInst iterInst iter ⦃ (r : Scalar) =>
      r.asNat = (ss.map (·.asNat)).sum % L ⦄ :=
  Scalar.Insts.CoreIterTraitsAccumSum.sum_spec borrowInst iterInst iter xs ss hiter hborrow hss

/-- `Default`: the scalar `0`. -/
theorem default : Scalar.Insts.CoreDefaultDefault.default ⦃ (r : Scalar) => r.asNat = 0 ⦄ :=
  Scalar.Insts.CoreDefaultDefault.default_spec

/-- `From<u8>`, `From<u16>`, `From<u32>`, `From<u64>`, `From<u128>`: the value of the integer. -/
theorem «from» :
    (∀ x : U8, Scalar.Insts.CoreConvertFromU8.from x ⦃ (r : Scalar) => r.asNat = x.val ⦄) ∧
    (∀ x : U16, Scalar.Insts.CoreConvertFromU16.from x ⦃ (r : Scalar) => r.asNat = x.val ⦄) ∧
    (∀ x : U32, Scalar.Insts.CoreConvertFromU32.from x ⦃ (r : Scalar) => r.asNat = x.val ⦄) ∧
    (∀ x : U64, Scalar.Insts.CoreConvertFromU64.from x ⦃ (r : Scalar) => r.asNat = x.val ⦄) ∧
    (∀ x : U128, Scalar.Insts.CoreConvertFromU128.from x ⦃ (r : Scalar) => r.asNat = x.val ⦄) :=
  ⟨Scalar.Insts.CoreConvertFromU8.from_spec, Scalar.Insts.CoreConvertFromU16.from_spec,
    Scalar.Insts.CoreConvertFromU32.from_spec, Scalar.Insts.CoreConvertFromU64.from_spec,
    Scalar.Insts.CoreConvertFromU128.from_spec⟩

/-- `Zeroize`: all bytes `0`. -/
theorem zeroize (s : Scalar) :
    Scalar.Insts.ZeroizeZeroize.zeroize s ⦃ (r : Scalar) =>
      r = { bytes := Array.repeat 32#usize 0#u8 } ⦄ :=
  Scalar.Insts.ZeroizeZeroize.zeroize_spec s

/-- `ZERO`: the scalar `0`. -/
theorem ZERO : Scalar.ZERO.asNat = 0 := Scalar.ZERO_spec

/-- `ONE`: the scalar `1`. -/
theorem ONE : Scalar.ONE.asNat = 1 := Scalar.ONE_spec

/-- `to_bytes`: the byte encoding. -/
theorem to_bytes (s : Scalar) : Scalar.to_bytes s ⦃ (r : Array U8 32#usize) => r = s.bytes ⦄ :=
  Scalar.to_bytes_spec s

/-- `as_bytes`: the byte encoding. -/
theorem as_bytes (s : Scalar) : Scalar.as_bytes s ⦃ (r : Array U8 32#usize) => r = s.bytes ⦄ :=
  Scalar.as_bytes_spec s

/-- `invert`: the inverse modulo `L` (reduced), and `0` for `0`. -/
theorem invert (s : Scalar) :
    Scalar.invert s ⦃ (r : Scalar) =>
      (s.asNat % L ≠ 0 → r.asNat * s.asNat % L = 1) ∧
      (s.asNat % L = 0 → r.asNat = 0) ∧ r.asNat < L ⦄ :=
  Scalar.invert_spec s

/-- `invert_batch`: inverts every (nonzero) input; returns the inverse of their product. -/
theorem invert_batch {N : Usize} (inputs : Array Scalar N)
    (hinputs : ∀ i < N.val, inputs[i]!.asNat % L ≠ 0) :
    Scalar.invert_batch inputs ⦃ (ret : Scalar) (r : Array Scalar N) =>
      (∀ i < N.val, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range N.val, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  Scalar.invert_batch_spec inputs hinputs

/-- `invert_batch_alloc`: as `invert_batch`, on a slice. -/
theorem invert_batch_alloc (inputs : Slice Scalar)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    Scalar.invert_batch_alloc inputs ⦃ (ret : Scalar) (r : Slice Scalar) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  Scalar.invert_batch_alloc_spec inputs hinputs

/-- `div_by_2`: `b` with `b + b = s` modulo `L`, reduced. -/
theorem div_by_2 (s : Scalar) (hs : s.asNat < L) :
    Scalar.div_by_2 s ⦃ (r : Scalar) => 2 * r.asNat % L = s.asNat ∧ r.asNat < L ⦄ :=
  Scalar.div_by_2_spec s hs

end Theorems.scalar.Scalar

namespace Theorems.scalar

/-- `clamp_integer`: clears the low 3 bits and bit 255, sets bit 254. -/
theorem clamp_integer (bytes : Array U8 32#usize) :
    scalar.clamp_integer bytes ⦃ (r : Array U8 32#usize) =>
      r.asNat 8 = 2 ^ 254 + 8 * (bytes.asNat 8 % 2 ^ 254 / 8) ⦄ :=
  scalar.clamp_integer_spec bytes

end Theorems.scalar

namespace Theorems.scalar.HalfWidthScalar

/-- `Default` (derived): the scalar `0`. -/
theorem default :
    HalfWidthScalar.Insts.CoreDefaultDefault.default ⦃ (r : HalfWidthScalar) =>
      r.asNat < 2 ^ 128 ∧ r.asNat = 0 ⦄ :=
  HalfWidthScalar.Insts.CoreDefaultDefault.default_spec

/-- `PartialEq` (derived): equality. -/
theorem eq (a b : HalfWidthScalar) :
    HalfWidthScalar.Insts.CoreCmpPartialEqHalfWidthScalar.eq a b ⦃ (r : Bool) =>
      r = true ↔ a = b ⦄ :=
  HalfWidthScalar.Insts.CoreCmpPartialEqHalfWidthScalar.eq_spec a b

/-- `TryFrom<Scalar>`: succeeds iff the value is below `2^128`. -/
theorem try_from (value : Scalar) :
    HalfWidthScalar.Insts.CoreConvertTryFromScalarTuple.try_from value
      ⦃ (r : core.result.Result HalfWidthScalar Unit) =>
        (value.asNat < 2 ^ 128 → r = .Ok value) ∧ (2 ^ 128 ≤ value.asNat → r = .Err ()) ⦄ :=
  HalfWidthScalar.Insts.CoreConvertTryFromScalarTuple.try_from_spec value

/-- `ZERO`: `0`. -/
theorem ZERO : HalfWidthScalar.ZERO.asNat < 2 ^ 128 ∧ HalfWidthScalar.ZERO.asNat = 0 :=
  HalfWidthScalar.ZERO_spec

/-- `ONE`: `1`. -/
theorem ONE : HalfWidthScalar.ONE.asNat < 2 ^ 128 ∧ HalfWidthScalar.ONE.asNat = 1 :=
  HalfWidthScalar.ONE_spec

/-- `from_bytes`: the 128-bit little-endian value. -/
theorem from_bytes (bytes : Array U8 16#usize) :
    HalfWidthScalar.from_bytes bytes ⦃ (r : HalfWidthScalar) =>
      r.asNat < 2 ^ 128 ∧ r.asNat = bytes.asNat 8 ⦄ :=
  HalfWidthScalar.from_bytes_spec bytes

/-- `as_scalar`: the same value. -/
theorem as_scalar (s : HalfWidthScalar) :
    HalfWidthScalar.as_scalar s ⦃ (r : Scalar) => r.asNat = s.asNat ⦄ :=
  HalfWidthScalar.as_scalar_spec s

/-- `to_bytes`: the 128-bit little-endian encoding. -/
theorem to_bytes (s : HalfWidthScalar) (hs : s.asNat < 2 ^ 128) :
    HalfWidthScalar.to_bytes s ⦃ (r : Array U8 16#usize) => r.asNat 8 = s.asNat ⦄ :=
  HalfWidthScalar.to_bytes_spec s hs

/-- `From<HalfWidthScalar> for Scalar`: the same value. -/
theorem into_scalar (x : HalfWidthScalar) :
    Scalar.Insts.CoreConvertFromHalfWidthScalar.from x ⦃ (r : Scalar) => r.asNat = x.asNat ⦄ :=
  Scalar.Insts.CoreConvertFromHalfWidthScalar.from_spec x

/-- `From<u8>`, `From<u16>`, `From<u32>`, `From<u64>`, `From<u128>`: the value of the integer. -/
theorem «from» :
    (∀ x : U8, HalfWidthScalar.Insts.CoreConvertFromU8.from x ⦃ (r : HalfWidthScalar) =>
      r.asNat < 2 ^ 128 ∧ r.asNat = x.val ⦄) ∧
    (∀ x : U16, HalfWidthScalar.Insts.CoreConvertFromU16.from x ⦃ (r : HalfWidthScalar) =>
      r.asNat < 2 ^ 128 ∧ r.asNat = x.val ⦄) ∧
    (∀ x : U32, HalfWidthScalar.Insts.CoreConvertFromU32.from x ⦃ (r : HalfWidthScalar) =>
      r.asNat < 2 ^ 128 ∧ r.asNat = x.val ⦄) ∧
    (∀ x : U64, HalfWidthScalar.Insts.CoreConvertFromU64.from x ⦃ (r : HalfWidthScalar) =>
      r.asNat < 2 ^ 128 ∧ r.asNat = x.val ⦄) ∧
    (∀ x : U128, HalfWidthScalar.Insts.CoreConvertFromU128.from x ⦃ (r : HalfWidthScalar) =>
      r.asNat < 2 ^ 128 ∧ r.asNat = x.val ⦄) :=
  ⟨HalfWidthScalar.Insts.CoreConvertFromU8.from_spec,
    HalfWidthScalar.Insts.CoreConvertFromU16.from_spec,
    HalfWidthScalar.Insts.CoreConvertFromU32.from_spec,
    HalfWidthScalar.Insts.CoreConvertFromU64.from_spec,
    HalfWidthScalar.Insts.CoreConvertFromU128.from_spec⟩

/-- `Zeroize`: all bytes `0`. -/
theorem zeroize (s : HalfWidthScalar) :
    HalfWidthScalar.Insts.ZeroizeZeroize.zeroize s ⦃ (r : HalfWidthScalar) =>
      r = { bytes := Array.repeat 32#usize 0#u8 } ⦄ :=
  HalfWidthScalar.Insts.ZeroizeZeroize.zeroize_spec s

end Theorems.scalar.HalfWidthScalar
