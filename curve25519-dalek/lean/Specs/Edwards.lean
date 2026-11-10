/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519.Edwards.Encoding
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
public import Subtle
import Proofs.Edwards.Add
import Proofs.Edwards.AddAssign
import Proofs.Edwards.AsBytes
import Proofs.Edwards.BasepointTableBasepoint
import Proofs.Edwards.BasepointTableCreate
import Proofs.Edwards.BasepointTableFrom
import Proofs.Edwards.BasepointTableMul
import Proofs.Edwards.BasepointTableMulBase
import Proofs.Edwards.Compress
import Proofs.Edwards.CompressBatch
import Proofs.Edwards.CompressBatchAlloc
import Proofs.Edwards.CompressedCtEq
import Proofs.Edwards.CompressedDefault
import Proofs.Edwards.CompressedEq
import Proofs.Edwards.CompressedIdentity
import Proofs.Edwards.CompressedZeroize
import Proofs.Edwards.ConditionalSelect
import Proofs.Edwards.CtEq
import Proofs.Edwards.Decompress
import Proofs.Edwards.Default
import Proofs.Edwards.Eq
import Proofs.Edwards.FromSlice
import Proofs.Edwards.Identity
import Proofs.Edwards.IsSmallOrder
import Proofs.Edwards.IsTorsionFree
import Proofs.Edwards.Mul
import Proofs.Edwards.MulAssign
import Proofs.Edwards.MulBase
import Proofs.Edwards.MulBaseClamped
import Proofs.Edwards.MulByCofactor
import Proofs.Edwards.MulClamped
import Proofs.Edwards.MultiscalarMul
import Proofs.Edwards.Neg
import Proofs.Edwards.OptionalMultiscalarMul
import Proofs.Edwards.Sub
import Proofs.Edwards.SubAssign
import Proofs.Edwards.Sum
import Proofs.Edwards.ToBytes
import Proofs.Edwards.ToMontgomery
import Proofs.Edwards.ToMontgomeryBatch
import Proofs.Edwards.VartimeDoubleScalarMulBasepoint
import Proofs.Edwards.VartimeTripleScalarMulBasepoint
import Proofs.Edwards.VartimeEdwardsPrecomputationIsEmpty
import Proofs.Edwards.VartimeEdwardsPrecomputationLen
import Proofs.Edwards.VartimeEdwardsPrecomputationNew
import Proofs.Edwards.VartimeEdwardsPrecomputationOptionalMixedMultiscalarMul
import Proofs.Edwards.Zeroize
import Zeroize.Instances
public section

/-! # Specs of `src/edwards.rs`

The public items of `edwards.rs`, in its order, restated with `recall` from `Proofs/Edwards/`,
with the axioms each proof uses; one statement per configuration (`x86_64`/`i686`, with or
without precomputed tables; the basepoint tables exist only with tables).

Points are specified through `toPoint` under the invariants `OnCurve` and `IsBounded`, tables
through `point` under `IsTable` and `IsBounded`, precomputations through `points` under `IsValid`
and `IsBounded`. Scalars act by their unreduced value `asNat`, which must be `< 2^255` (invariant
#1 of `Scalar` in `scalar.rs`). Iterator inputs are given by the lists they yield. The multiscalar
statements are about the patched code
(`translation-patches/edwards-{multiscalar,optional_multiscalar}_mul.patch`), which requires as many
scalars as points; the original panics unless both inputs' `size_hint`s are exact and equal.

Definitions used: `EdwardsPoint.toPoint`, `OnCurve`, `IsBounded`, the
tables' `point`, `IsTable`, `IsBounded` (`Defs/Edwards.lean`), the precomputations' `points`,
`IsValid`, `IsBounded` (`Defs/ScalarMul.lean`), `Scalar.asNat`, `HalfWidthScalar.asNat`
(`Defs/Scalar.lean`), `Array.toVector`
(`ToAeneas/Array.lean`), `Iterator.Yields`, `IntoIterator.Yields` (`ToAeneas/Iterator.lean`),
`curve25519.encode`, `decodeLenient` (`Curve25519/Edwards/Encoding.lean`), `curve25519.basepoint`
(`Curve25519/Edwards/Basepoint.lean`), `decodeScalar25519`, `encodeUCoordinate`
(`Curve25519/X25519.lean`), `curve25519.L` (`Curve25519/Basic.lean`), `edwardsToMontgomery`
(`Curve25519/Montgomery.lean`), `subtle.Choice.IsValid` (`Subtle/`).

Not translated: `Debug`, `Hash`, the `group` and `serde` impls, `random`, hash-to-curve, and the
provided methods of the traits. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts.SubtleConstantTimeEq

/-- `ConstantTimeEq for CompressedEdwardsY`: byte equality (two encodings of one point can
differ). -/
recall ct_eq_spec (self other : CompressedEdwardsY) :
    ct_eq self other ⦃ (r : subtle.Choice) => r.IsValid ∧ (r = 1#u8 ↔ self = other) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec

end Curve25519Dalek.edwards.CompressedEdwardsY.Insts.SubtleConstantTimeEq

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts
namespace CoreCmpPartialEqCompressedEdwardsY

/-- `PartialEq for CompressedEdwardsY`: byte equality (two encodings of one point can differ). -/
recall eq_spec (self other : CompressedEdwardsY) :
    eq self other ⦃ (r : Bool) => r = true ↔ self = other ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec

end CoreCmpPartialEqCompressedEdwardsY
end Curve25519Dalek.edwards.CompressedEdwardsY.Insts

namespace Curve25519Dalek.edwards.CompressedEdwardsY

/-- `CompressedEdwardsY::as_bytes`: the bytes. -/
recall as_bytes_spec (self : CompressedEdwardsY) :
    as_bytes self ⦃ (r : Array U8 32#usize) => r = self ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms as_bytes_spec

/-- `CompressedEdwardsY::to_bytes`: the bytes. -/
recall to_bytes_spec (self : CompressedEdwardsY) :
    to_bytes self ⦃ (r : Array U8 32#usize) => r = self ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_bytes_spec

end Curve25519Dalek.edwards.CompressedEdwardsY

namespace Curve25519Dalek.edwards.CompressedEdwardsY.«x86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `CompressedEdwardsY::decompress`: the lenient decoding `decodeLenient` of the bytes (`y`
reduced modulo `p`, `x = 0` accepted with either sign); the point is on the curve. -/
recall decompress_spec (self : CompressedEdwardsY) :
    decompress.«x86_64-tables» self ⦃ (r : Option (EdwardsPoint.«x86_64-tables»)) =>
      r.map EdwardsPoint.«x86_64-tables».toPoint = decodeLenient self.toVector ∧
      ∀ q, r = some q → q.OnCurve ∧ q.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms decompress_spec

end Curve25519Dalek.edwards.CompressedEdwardsY.«x86_64-tables»

namespace Curve25519Dalek.edwards.CompressedEdwardsY.«i686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `CompressedEdwardsY::decompress`: the lenient decoding `decodeLenient` of the bytes (`y`
reduced modulo `p`, `x = 0` accepted with either sign); the point is on the curve. -/
recall decompress_spec (self : CompressedEdwardsY) :
    decompress.«i686-tables» self ⦃ (r : Option (EdwardsPoint.«i686-tables»)) =>
      r.map EdwardsPoint.«i686-tables».toPoint = decodeLenient self.toVector ∧
      ∀ q, r = some q → q.OnCurve ∧ q.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms decompress_spec

end Curve25519Dalek.edwards.CompressedEdwardsY.«i686-tables»

namespace Curve25519Dalek.edwards.CompressedEdwardsY.«x86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `CompressedEdwardsY::decompress`: the lenient decoding `decodeLenient` of the bytes (`y`
reduced modulo `p`, `x = 0` accepted with either sign); the point is on the curve. -/
recall decompress_spec (self : CompressedEdwardsY) :
    decompress.«x86_64-no-tables» self ⦃ (r : Option (EdwardsPoint.«x86_64-no-tables»)) =>
      r.map EdwardsPoint.«x86_64-no-tables».toPoint = decodeLenient self.toVector ∧
      ∀ q, r = some q → q.OnCurve ∧ q.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms decompress_spec

end Curve25519Dalek.edwards.CompressedEdwardsY.«x86_64-no-tables»

namespace Curve25519Dalek.edwards.CompressedEdwardsY.«i686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `CompressedEdwardsY::decompress`: the lenient decoding `decodeLenient` of the bytes (`y`
reduced modulo `p`, `x = 0` accepted with either sign); the point is on the curve. -/
recall decompress_spec (self : CompressedEdwardsY) :
    decompress.«i686-no-tables» self ⦃ (r : Option (EdwardsPoint.«i686-no-tables»)) =>
      r.map EdwardsPoint.«i686-no-tables».toPoint = decodeLenient self.toVector ∧
      ∀ q, r = some q → q.OnCurve ∧ q.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms decompress_spec

end Curve25519Dalek.edwards.CompressedEdwardsY.«i686-no-tables»

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts
namespace CoreConvertTryFromShared0SliceU8TryFromSliceError

/-- `TryFrom<&[u8]> for CompressedEdwardsY`: as `from_slice`. -/
recall try_from_spec (slice : Slice U8) :
    try_from slice ⦃ (r : core.result.Result CompressedEdwardsY core.array.TryFromSliceError) =>
      match r with
      | .Ok c => slice.length = 32 ∧ ∀ i < 32, c[i]! = slice[i]!
      | .Err _ => slice.length ≠ 32 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms try_from_spec

end CoreConvertTryFromShared0SliceU8TryFromSliceError
end Curve25519Dalek.edwards.CompressedEdwardsY.Insts

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for CompressedEdwardsY` is the encoding of the neutral element. -/
recall identity_spec :
    identity ⦃ (r : CompressedEdwardsY) => r.toVector = encode 0 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms identity_spec

end Curve25519Dalek.edwards.CompressedEdwardsY.Insts.Curve25519_dalekTraitsIdentity

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts.CoreDefaultDefault

/-- `Default for CompressedEdwardsY` is the encoding of the neutral element. -/
recall default_spec :
    default ⦃ (r : CompressedEdwardsY) => r.toVector = encode 0 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec

end Curve25519Dalek.edwards.CompressedEdwardsY.Insts.CoreDefaultDefault

namespace Curve25519Dalek.edwards.CompressedEdwardsY

/-- `CompressedEdwardsY::from_slice`: the bytes of a slice of length `32`, an error otherwise. -/
recall from_slice_spec (bytes : Slice U8) :
    from_slice bytes ⦃ (r : core.result.Result CompressedEdwardsY core.array.TryFromSliceError) =>
      match r with
      | .Ok c => bytes.length = 32 ∧ ∀ i < 32, c[i]! = bytes[i]!
      | .Err _ => bytes.length ≠ 32 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_slice_spec

end Curve25519Dalek.edwards.CompressedEdwardsY

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519_dalekTraitsIdentity

/-- `Identity for EdwardsPoint` represents the neutral element. -/
recall identity_spec :
    identity ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms identity_spec

end Curve25519_dalekTraitsIdentity
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace Curve25519_dalekTraitsIdentity

/-- `Identity for EdwardsPoint` represents the neutral element. -/
recall identity_spec :
    identity ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms identity_spec

end Curve25519_dalekTraitsIdentity
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519_dalekTraitsIdentity

/-- `Identity for EdwardsPoint` represents the neutral element. -/
recall identity_spec :
    identity ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms identity_spec

end Curve25519_dalekTraitsIdentity
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace Curve25519_dalekTraitsIdentity

/-- `Identity for EdwardsPoint` represents the neutral element. -/
recall identity_spec :
    identity ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms identity_spec

end Curve25519_dalekTraitsIdentity
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Default for EdwardsPoint` represents the neutral element. -/
recall default_spec :
    default ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec

end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts.CoreDefaultDefault

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Default for EdwardsPoint` represents the neutral element. -/
recall default_spec :
    default ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec

end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts.CoreDefaultDefault

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Default for EdwardsPoint` represents the neutral element. -/
recall default_spec :
    default ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec

end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts.CoreDefaultDefault

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Default for EdwardsPoint` represents the neutral element. -/
recall default_spec :
    default ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec

end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts.CoreDefaultDefault

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts.ZeroizeZeroize

/-- `Zeroize for CompressedEdwardsY` leaves the encoding of the neutral element. -/
recall zeroize_spec (self : CompressedEdwardsY) :
    zeroize self ⦃ (r : CompressedEdwardsY) => r.toVector = encode 0 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec

end Curve25519Dalek.edwards.CompressedEdwardsY.Insts.ZeroizeZeroize

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts.ZeroizeZeroize

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Zeroize for EdwardsPoint` leaves the neutral element. -/
recall zeroize_spec (self : EdwardsPoint.«x86_64-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec

end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts.ZeroizeZeroize

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts.ZeroizeZeroize

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Zeroize for EdwardsPoint` leaves the neutral element. -/
recall zeroize_spec (self : EdwardsPoint.«i686-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec

end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts.ZeroizeZeroize

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts.ZeroizeZeroize

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Zeroize for EdwardsPoint` leaves the neutral element. -/
recall zeroize_spec (self : EdwardsPoint.«x86_64-no-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec

end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts.ZeroizeZeroize

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts.ZeroizeZeroize

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Zeroize for EdwardsPoint` leaves the neutral element. -/
recall zeroize_spec (self : EdwardsPoint.«i686-no-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec

end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts.ZeroizeZeroize

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_select` for `EdwardsPoint`:
`a` if `choice = 0`, `b` if `choice = 1`. -/
recall conditional_select_spec (a b : EdwardsPoint.«x86_64-tables») (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_select_spec

end SubtleConditionallySelectable
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_select` for `EdwardsPoint`:
`a` if `choice = 0`, `b` if `choice = 1`. -/
recall conditional_select_spec (a b : EdwardsPoint.«i686-tables») (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : EdwardsPoint.«i686-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_select_spec

end SubtleConditionallySelectable
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_select` for `EdwardsPoint`:
`a` if `choice = 0`, `b` if `choice = 1`. -/
recall conditional_select_spec (a b : EdwardsPoint.«x86_64-no-tables») (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_select_spec

end SubtleConditionallySelectable
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_select` for `EdwardsPoint`:
`a` if `choice = 0`, `b` if `choice = 1`. -/
recall conditional_select_spec (a b : EdwardsPoint.«i686-no-tables») (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_select_spec

end SubtleConditionallySelectable
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts.SubtleConstantTimeEq

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ConstantTimeEq for EdwardsPoint` on points: equality of the represented points. -/
recall ct_eq_spec (self other : EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hother : other.IsBounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (r : subtle.Choice) =>
      r.IsValid ∧ (r = 1#u8 ↔ self.toPoint = other.toPoint) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec

end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts.SubtleConstantTimeEq

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts.SubtleConstantTimeEq

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ConstantTimeEq for EdwardsPoint` on points: equality of the represented points. -/
recall ct_eq_spec (self other : EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hother : other.IsBounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (r : subtle.Choice) =>
      r.IsValid ∧ (r = 1#u8 ↔ self.toPoint = other.toPoint) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec

end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts.SubtleConstantTimeEq

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace SubtleConstantTimeEq

/-- `ConstantTimeEq for EdwardsPoint` on points: equality of the represented points. -/
recall ct_eq_spec (self other : EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hother : other.IsBounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (r : subtle.Choice) =>
      r.IsValid ∧ (r = 1#u8 ↔ self.toPoint = other.toPoint) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec

end SubtleConstantTimeEq
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace SubtleConstantTimeEq

/-- `ConstantTimeEq for EdwardsPoint` on points: equality of the represented points. -/
recall ct_eq_spec (self other : EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hother : other.IsBounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (r : subtle.Choice) =>
      r.IsValid ∧ (r = 1#u8 ↔ self.toPoint = other.toPoint) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec

end SubtleConstantTimeEq
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreCmpPartialEqEdwardsPointx86_64-tables»

/-- `PartialEq for EdwardsPoint` on points: equality of the represented points. -/
recall eq_spec (self other : EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hother : other.IsBounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (r : Bool) => r = true ↔ self.toPoint = other.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec

end «CoreCmpPartialEqEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreCmpPartialEqEdwardsPointi686-tables»

/-- `PartialEq for EdwardsPoint` on points: equality of the represented points. -/
recall eq_spec (self other : EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hother : other.IsBounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (r : Bool) => r = true ↔ self.toPoint = other.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec

end «CoreCmpPartialEqEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreCmpPartialEqEdwardsPointx86_64-no-tables»

/-- `PartialEq for EdwardsPoint` on points: equality of the represented points. -/
recall eq_spec (self other : EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hother : other.IsBounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (r : Bool) => r = true ↔ self.toPoint = other.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec

end «CoreCmpPartialEqEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreCmpPartialEqEdwardsPointi686-no-tables»

/-- `PartialEq for EdwardsPoint` on points: equality of the represented points. -/
recall eq_spec (self other : EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hother : other.IsBounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (r : Bool) => r = true ↔ self.toPoint = other.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec

end «CoreCmpPartialEqEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::to_montgomery`: RFC 7748's encoding of the `u`-coordinate of the
Montgomery image of the represented point (`0` for the identity). -/
recall to_montgomery_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    to_montgomery self ⦃ (r : montgomery.MontgomeryPoint) =>
      r.toVector = encodeUCoordinate (edwardsToMontgomery self.toPoint).u ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_montgomery_spec

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::to_montgomery`: RFC 7748's encoding of the `u`-coordinate of the
Montgomery image of the represented point (`0` for the identity). -/
recall to_montgomery_spec (self : EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    to_montgomery self ⦃ (r : montgomery.MontgomeryPoint) =>
      r.toVector = encodeUCoordinate (edwardsToMontgomery self.toPoint).u ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_montgomery_spec

end «EdwardsPointi686-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::to_montgomery`: RFC 7748's encoding of the `u`-coordinate of the
Montgomery image of the represented point (`0` for the identity). -/
recall to_montgomery_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    to_montgomery self ⦃ (r : montgomery.MontgomeryPoint) =>
      r.toVector = encodeUCoordinate (edwardsToMontgomery self.toPoint).u ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_montgomery_spec

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::to_montgomery`: RFC 7748's encoding of the `u`-coordinate of the
Montgomery image of the represented point (`0` for the identity). -/
recall to_montgomery_spec (self : EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    to_montgomery self ⦃ (r : montgomery.MontgomeryPoint) =>
      r.toVector = encodeUCoordinate (edwardsToMontgomery self.toPoint).u ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_montgomery_spec

end «EdwardsPointi686-no-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is RFC 7748's encoding of the
`u`-coordinate of the Montgomery image of point `i` (`0` for the identity). -/
recall to_montgomery_batch_spec (eds : Slice EdwardsPoint.«x86_64-tables»)
    (heds : ∀ i < eds.length, eds[i]!.IsBounded) (heds_on : ∀ i < eds.length, eds[i]!.OnCurve) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧
        ∀ i < eds.length, r[i]!.toVector = encodeUCoordinate
            (edwardsToMontgomery eds[i]!.toPoint).u ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_montgomery_batch_spec

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is RFC 7748's encoding of the
`u`-coordinate of the Montgomery image of point `i` (`0` for the identity). -/
recall to_montgomery_batch_spec (eds : Slice EdwardsPoint.«i686-tables»)
    (heds : ∀ i < eds.length, eds[i]!.IsBounded) (heds_on : ∀ i < eds.length, eds[i]!.OnCurve) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧
        ∀ i < eds.length, r[i]!.toVector = encodeUCoordinate
            (edwardsToMontgomery eds[i]!.toPoint).u ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_montgomery_batch_spec

end «EdwardsPointi686-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is RFC 7748's encoding of the
`u`-coordinate of the Montgomery image of point `i` (`0` for the identity). -/
recall to_montgomery_batch_spec (eds : Slice EdwardsPoint.«x86_64-no-tables»)
    (heds : ∀ i < eds.length, eds[i]!.IsBounded) (heds_on : ∀ i < eds.length, eds[i]!.OnCurve) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧
        ∀ i < eds.length, r[i]!.toVector = encodeUCoordinate
            (edwardsToMontgomery eds[i]!.toPoint).u ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_montgomery_batch_spec

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::to_montgomery_batch`: entry `i` is RFC 7748's encoding of the
`u`-coordinate of the Montgomery image of point `i` (`0` for the identity). -/
recall to_montgomery_batch_spec (eds : Slice EdwardsPoint.«i686-no-tables»)
    (heds : ∀ i < eds.length, eds[i]!.IsBounded) (heds_on : ∀ i < eds.length, eds[i]!.OnCurve) :
    to_montgomery_batch eds ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = eds.length ∧
        ∀ i < eds.length, r[i]!.toVector = encodeUCoordinate
            (edwardsToMontgomery eds[i]!.toPoint).u ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_montgomery_batch_spec

end «EdwardsPointi686-no-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::compress` is RFC 8032's encoding of the represented point. -/
recall compress_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.toVector = curve25519.encode self.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::compress` is RFC 8032's encoding of the represented point. -/
recall compress_spec (self : EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.toVector = curve25519.encode self.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_spec

end Curve25519Dalek.edwards.«EdwardsPointi686-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::compress` is RFC 8032's encoding of the represented point. -/
recall compress_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.toVector = curve25519.encode self.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::compress` is RFC 8032's encoding of the represented point. -/
recall compress_spec (self : EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.toVector = curve25519.encode self.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_spec

end Curve25519Dalek.edwards.«EdwardsPointi686-no-tables»

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::compress_batch`: entry `i` is RFC 8032's encoding of point `i`. -/
recall compress_batch_spec {N : Usize} (inputs : Array EdwardsPoint.«x86_64-tables» N)
    (hinputs : ∀ i < N.val, inputs[i]!.IsBounded) (hinputs_on : ∀ i < N.val, inputs[i]!.OnCurve) :
    compress_batch inputs ⦃ (r : Array CompressedEdwardsY N) =>
      ∀ i < N.val, r[i]!.toVector = curve25519.encode inputs[i]!.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_batch_spec

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::compress_batch`: entry `i` is RFC 8032's encoding of point `i`. -/
recall compress_batch_spec {N : Usize} (inputs : Array EdwardsPoint.«i686-tables» N)
    (hinputs : ∀ i < N.val, inputs[i]!.IsBounded) (hinputs_on : ∀ i < N.val, inputs[i]!.OnCurve) :
    compress_batch inputs ⦃ (r : Array CompressedEdwardsY N) =>
      ∀ i < N.val, r[i]!.toVector = curve25519.encode inputs[i]!.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_batch_spec

end «EdwardsPointi686-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::compress_batch`: entry `i` is RFC 8032's encoding of point `i`. -/
recall compress_batch_spec {N : Usize} (inputs : Array EdwardsPoint.«x86_64-no-tables» N)
    (hinputs : ∀ i < N.val, inputs[i]!.IsBounded) (hinputs_on : ∀ i < N.val, inputs[i]!.OnCurve) :
    compress_batch inputs ⦃ (r : Array CompressedEdwardsY N) =>
      ∀ i < N.val, r[i]!.toVector = curve25519.encode inputs[i]!.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_batch_spec

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::compress_batch`: entry `i` is RFC 8032's encoding of point `i`. -/
recall compress_batch_spec {N : Usize} (inputs : Array EdwardsPoint.«i686-no-tables» N)
    (hinputs : ∀ i < N.val, inputs[i]!.IsBounded) (hinputs_on : ∀ i < N.val, inputs[i]!.OnCurve) :
    compress_batch inputs ⦃ (r : Array CompressedEdwardsY N) =>
      ∀ i < N.val, r[i]!.toVector = curve25519.encode inputs[i]!.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_batch_spec

end «EdwardsPointi686-no-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is RFC 8032's encoding of point `i`. -/
recall compress_batch_alloc_spec (inputs : Slice EdwardsPoint.«x86_64-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.IsBounded)
    (hinputs_on : ∀ i < inputs.length, inputs[i]!.OnCurve) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧
        ∀ i < inputs.length, r[i]!.toVector = curve25519.encode inputs[i]!.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_batch_alloc_spec

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is RFC 8032's encoding of point `i`. -/
recall compress_batch_alloc_spec (inputs : Slice EdwardsPoint.«i686-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.IsBounded)
    (hinputs_on : ∀ i < inputs.length, inputs[i]!.OnCurve) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧
        ∀ i < inputs.length, r[i]!.toVector = curve25519.encode inputs[i]!.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_batch_alloc_spec

end «EdwardsPointi686-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is RFC 8032's encoding of point `i`. -/
recall compress_batch_alloc_spec (inputs : Slice EdwardsPoint.«x86_64-no-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.IsBounded)
    (hinputs_on : ∀ i < inputs.length, inputs[i]!.OnCurve) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧
        ∀ i < inputs.length, r[i]!.toVector = curve25519.encode inputs[i]!.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_batch_alloc_spec

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is RFC 8032's encoding of point `i`. -/
recall compress_batch_alloc_spec (inputs : Slice EdwardsPoint.«i686-no-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.IsBounded)
    (hinputs_on : ∀ i < inputs.length, inputs[i]!.OnCurve) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧
        ∀ i < inputs.length, r[i]!.toVector = curve25519.encode inputs[i]!.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_batch_alloc_spec

end «EdwardsPointi686-no-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Add<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall add_spec (self other : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.IsBounded) (hother : other.IsBounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointi686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithAddSharedAEdwardsPointi686-tablesEdwardsPointi686-tables»

/-- `Add<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall add_spec (self other : edwards.EdwardsPoint.«i686-tables»)
    (hself : self.IsBounded) (hother : other.IsBounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddSharedAEdwardsPointi686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.«Shared0EdwardsPointi686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Add<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_spec (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithAddEdwardsPointi686-tablesEdwardsPointi686-tables»

/-- `Add<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_spec (self rhs : EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddEdwardsPointi686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Add<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_spec (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithAddSharedBEdwardsPointi686-tablesEdwardsPointi686-tables»

/-- `Add<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_spec (self rhs : EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddSharedBEdwardsPointi686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointx86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Add<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall add_spec (self rhs : edwards.EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsPointx86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointi686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithAddEdwardsPointi686-tablesEdwardsPointi686-tables»

/-- `Add<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall add_spec (self rhs : edwards.EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddEdwardsPointi686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.«SharedAEdwardsPointi686-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Add<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall add_spec (self other : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.IsBounded) (hother : other.IsBounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointi686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithAddSharedAEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Add<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall add_spec (self other : edwards.EdwardsPoint.«i686-no-tables»)
    (hself : self.IsBounded) (hother : other.IsBounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddSharedAEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end Curve25519Dalek.«Shared0EdwardsPointi686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Add<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_spec (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithAddEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Add<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_spec (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Add<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_spec (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithAddSharedBEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Add<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_spec (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddSharedBEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointx86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Add<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall add_spec (self rhs : edwards.EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.«SharedAEdwardsPointx86_64-no-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointi686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithAddEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Add<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall add_spec (self rhs : edwards.EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end Curve25519Dalek.«SharedAEdwardsPointi686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddAssignSharedAEdwardsPointx86_64-tables»

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_assign_spec (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end «CoreOpsArithAddAssignSharedAEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithAddAssignSharedAEdwardsPointi686-tables»

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_assign_spec (self rhs : EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end «CoreOpsArithAddAssignSharedAEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddAssignEdwardsPointx86_64-tables»

/-- `AddAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_assign_spec (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end «CoreOpsArithAddAssignEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithAddAssignEdwardsPointi686-tables»

/-- `AddAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_assign_spec (self rhs : EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end «CoreOpsArithAddAssignEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddAssignSharedAEdwardsPointx86_64-no-tables»

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_assign_spec (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end «CoreOpsArithAddAssignSharedAEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithAddAssignSharedAEdwardsPointi686-no-tables»

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_assign_spec (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end «CoreOpsArithAddAssignSharedAEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddAssignEdwardsPointx86_64-no-tables»

/-- `AddAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_assign_spec (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end «CoreOpsArithAddAssignEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithAddAssignEdwardsPointi686-no-tables»

/-- `AddAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall add_assign_spec (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end «CoreOpsArithAddAssignEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Sub<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall sub_spec (self other : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.IsBounded) (hother : other.IsBounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointi686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithSubSharedAEdwardsPointi686-tablesEdwardsPointi686-tables»

/-- `Sub<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall sub_spec (self other : edwards.EdwardsPoint.«i686-tables»)
    (hself : self.IsBounded) (hother : other.IsBounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubSharedAEdwardsPointi686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.«Shared0EdwardsPointi686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Sub<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_spec (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithSubEdwardsPointi686-tablesEdwardsPointi686-tables»

/-- `Sub<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_spec (self rhs : EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubEdwardsPointi686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Sub<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_spec (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithSubSharedBEdwardsPointi686-tablesEdwardsPointi686-tables»

/-- `Sub<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_spec (self rhs : EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubSharedBEdwardsPointi686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointx86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Sub<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall sub_spec (self rhs : edwards.EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsPointx86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointi686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithSubEdwardsPointi686-tablesEdwardsPointi686-tables»

/-- `Sub<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall sub_spec (self rhs : edwards.EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubEdwardsPointi686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.«SharedAEdwardsPointi686-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Sub<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall sub_spec (self other : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.IsBounded) (hother : other.IsBounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointi686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithSubSharedAEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Sub<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall sub_spec (self other : edwards.EdwardsPoint.«i686-no-tables»)
    (hself : self.IsBounded) (hother : other.IsBounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubSharedAEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end Curve25519Dalek.«Shared0EdwardsPointi686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Sub<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_spec (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithSubEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Sub<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_spec (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Sub<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_spec (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithSubSharedBEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Sub<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_spec (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubSharedBEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointx86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Sub<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall sub_spec (self rhs : edwards.EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end Curve25519Dalek.«SharedAEdwardsPointx86_64-no-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointi686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithSubEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Sub<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
recall sub_spec (self rhs : edwards.EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end Curve25519Dalek.«SharedAEdwardsPointi686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubAssignSharedAEdwardsPointx86_64-tables»

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_assign_spec (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end «CoreOpsArithSubAssignSharedAEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithSubAssignSharedAEdwardsPointi686-tables»

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_assign_spec (self rhs : EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end «CoreOpsArithSubAssignSharedAEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubAssignEdwardsPointx86_64-tables»

/-- `SubAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_assign_spec (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end «CoreOpsArithSubAssignEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithSubAssignEdwardsPointi686-tables»

/-- `SubAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_assign_spec (self rhs : EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end «CoreOpsArithSubAssignEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubAssignSharedAEdwardsPointx86_64-no-tables»

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_assign_spec (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end «CoreOpsArithSubAssignSharedAEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithSubAssignSharedAEdwardsPointi686-no-tables»

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_assign_spec (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end «CoreOpsArithSubAssignSharedAEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubAssignEdwardsPointx86_64-no-tables»

/-- `SubAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_assign_spec (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end «CoreOpsArithSubAssignEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithSubAssignEdwardsPointi686-no-tables»

/-- `SubAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
recall sub_assign_spec (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hrhs : rhs.IsBounded) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end «CoreOpsArithSubAssignEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace CoreIterTraitsAccumSum

/-- `Sum for EdwardsPoint`: the sum of the points yielded by the iterator (through `borrow`). -/
recall sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T EdwardsPoint.«x86_64-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ps : List EdwardsPoint.«x86_64-tables») (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«x86_64-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.IsBounded) (hps_on : ∀ P ∈ ps, P.OnCurve) :
    sum borrowInst iterInst iter ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = (ps.map (·.toPoint)).sum ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sum_spec

end CoreIterTraitsAccumSum
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace CoreIterTraitsAccumSum

/-- `Sum for EdwardsPoint`: the sum of the points yielded by the iterator (through `borrow`). -/
recall sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T EdwardsPoint.«i686-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ps : List EdwardsPoint.«i686-tables») (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«i686-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.IsBounded) (hps_on : ∀ P ∈ ps, P.OnCurve) :
    sum borrowInst iterInst iter ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = (ps.map (·.toPoint)).sum ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sum_spec

end CoreIterTraitsAccumSum
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace CoreIterTraitsAccumSum

/-- `Sum for EdwardsPoint`: the sum of the points yielded by the iterator (through `borrow`). -/
recall sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T EdwardsPoint.«x86_64-no-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ps : List EdwardsPoint.«x86_64-no-tables») (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«x86_64-no-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.IsBounded) (hps_on : ∀ P ∈ ps, P.OnCurve) :
    sum borrowInst iterInst iter ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = (ps.map (·.toPoint)).sum ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sum_spec

end CoreIterTraitsAccumSum
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace CoreIterTraitsAccumSum

/-- `Sum for EdwardsPoint`: the sum of the points yielded by the iterator (through `borrow`). -/
recall sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T EdwardsPoint.«i686-no-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ps : List EdwardsPoint.«i686-no-tables») (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«i686-no-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.IsBounded) (hps_on : ∀ P ∈ ps, P.OnCurve) :
    sum borrowInst iterInst iter ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = (ps.map (·.toPoint)).sum ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sum_spec

end CoreIterTraitsAccumSum
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithNegEdwardsPointx86_64-tables»

/-- `Neg for &EdwardsPoint` negates the represented point. -/
recall neg_spec (self : edwards.EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end «CoreOpsArithNegEdwardsPointx86_64-tables»
end Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointi686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithNegEdwardsPointi686-tables»

/-- `Neg for &EdwardsPoint` negates the represented point. -/
recall neg_spec (self : edwards.EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end «CoreOpsArithNegEdwardsPointi686-tables»
end Curve25519Dalek.«Shared0EdwardsPointi686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithNegEdwardsPointx86_64-tables»

/-- `Neg for EdwardsPoint` (by value) negates the represented point. -/
recall neg_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end «CoreOpsArithNegEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithNegEdwardsPointi686-tables»

/-- `Neg for EdwardsPoint` (by value) negates the represented point. -/
recall neg_spec (self : EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end «CoreOpsArithNegEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithNegEdwardsPointx86_64-no-tables»

/-- `Neg for &EdwardsPoint` negates the represented point. -/
recall neg_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end «CoreOpsArithNegEdwardsPointx86_64-no-tables»
end Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointi686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithNegEdwardsPointi686-no-tables»

/-- `Neg for &EdwardsPoint` negates the represented point. -/
recall neg_spec (self : edwards.EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end «CoreOpsArithNegEdwardsPointi686-no-tables»
end Curve25519Dalek.«Shared0EdwardsPointi686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithNegEdwardsPointx86_64-no-tables»

/-- `Neg for EdwardsPoint` (by value) negates the represented point. -/
recall neg_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end «CoreOpsArithNegEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithNegEdwardsPointi686-no-tables»

/-- `Neg for EdwardsPoint` (by value) negates the represented point. -/
recall neg_spec (self : EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end «CoreOpsArithNegEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for EdwardsPoint`: as `Mul`, `scalar • self` (unreduced, `< 2^255`). -/
recall mul_assign_spec (self : edwards.EdwardsPoint.«x86_64-tables») (scalar : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end CoreOpsArithMulAssignSharedAScalar
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for EdwardsPoint`: as `Mul`, `scalar • self` (unreduced, `< 2^255`). -/
recall mul_assign_spec (self : edwards.EdwardsPoint.«i686-tables») (scalar : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end CoreOpsArithMulAssignSharedAScalar
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_assign_spec (self : edwards.EdwardsPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end CoreOpsArithMulAssignScalar
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_assign_spec (self : edwards.EdwardsPoint.«i686-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end CoreOpsArithMulAssignScalar
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for EdwardsPoint`: as `Mul`, `scalar • self` (unreduced, `< 2^255`). -/
recall mul_assign_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (scalar : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end CoreOpsArithMulAssignSharedAScalar
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for EdwardsPoint`: as `Mul`, `scalar • self` (unreduced, `< 2^255`). -/
recall mul_assign_spec (self : edwards.EdwardsPoint.«i686-no-tables») (scalar : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end CoreOpsArithMulAssignSharedAScalar
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_assign_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end CoreOpsArithMulAssignScalar
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_assign_spec (self : edwards.EdwardsPoint.«i686-no-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end CoreOpsArithMulAssignScalar
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»

/-- `Mul<&Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«i686-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointx86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithMulScalarEdwardsPointx86_64-tables»

/-- `Mul<Scalar> for &EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsPointx86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointi686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithMulScalarEdwardsPointi686-tables»

/-- `Mul<Scalar> for &EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«i686-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarEdwardsPointi686-tables»
end Curve25519Dalek.«SharedAEdwardsPointi686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithMulScalarEdwardsPointx86_64-tables»

/-- `Mul<Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithMulScalarEdwardsPointi686-tables»

/-- `Mul<Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«i686-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.scalar.Scalar.Insts
namespace «CoreOpsArithMulSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Mul<&EdwardsPoint> for Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithMulSharedBEdwardsPointi686-tablesEdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Mul<&EdwardsPoint> for Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBEdwardsPointi686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.scalar.Scalar.Insts

namespace Curve25519Dalek.SharedAScalar.Insts
namespace «CoreOpsArithMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Mul<EdwardsPoint> for &Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithMulEdwardsPointi686-tablesEdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Mul<EdwardsPoint> for &Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulEdwardsPointi686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.SharedAScalar.Insts

namespace Curve25519Dalek.scalar.Scalar.Insts
namespace «CoreOpsArithMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Mul<EdwardsPoint> for Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithMulEdwardsPointi686-tablesEdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Mul<EdwardsPoint> for Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulEdwardsPointi686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.scalar.Scalar.Insts

namespace Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithMulSharedAScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsPoint`: `scalar • self` (unreduced, `< 2^255`). -/
recall mul_spec (self : edwards.EdwardsPoint.«x86_64-tables») (scalar : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointi686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithMulSharedAScalarEdwardsPointi686-tables»

/-- `Mul<&Scalar> for &EdwardsPoint`: `scalar • self` (unreduced, `< 2^255`). -/
recall mul_spec (self : edwards.EdwardsPoint.«i686-tables») (scalar : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAScalarEdwardsPointi686-tables»
end Curve25519Dalek.«Shared0EdwardsPointi686-tables».Insts

namespace Curve25519Dalek.Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Mul<&EdwardsPoint> for &Scalar`: as `&EdwardsPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (point : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.IsBounded) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithMulSharedAEdwardsPointi686-tablesEdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Mul<&EdwardsPoint> for &Scalar`: as `&EdwardsPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (point : edwards.EdwardsPoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.IsBounded) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsPointi686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.Shared0Scalar.Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-no-tables»

/-- `Mul<&Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithMulSharedBScalarEdwardsPointi686-no-tables»

/-- `Mul<&Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«i686-no-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointx86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithMulScalarEdwardsPointx86_64-no-tables»

/-- `Mul<Scalar> for &EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarEdwardsPointx86_64-no-tables»
end Curve25519Dalek.«SharedAEdwardsPointx86_64-no-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsPointi686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithMulScalarEdwardsPointi686-no-tables»

/-- `Mul<Scalar> for &EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«i686-no-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarEdwardsPointi686-no-tables»
end Curve25519Dalek.«SharedAEdwardsPointi686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithMulScalarEdwardsPointx86_64-no-tables»

/-- `Mul<Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithMulScalarEdwardsPointi686-no-tables»

/-- `Mul<Scalar> for EdwardsPoint`: as the borrowed form. -/
recall mul_spec (self : edwards.EdwardsPoint.«i686-no-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.scalar.Scalar.Insts
namespace «CoreOpsArithMulSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Mul<&EdwardsPoint> for Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

namespace «CoreOpsArithMulSharedBEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Mul<&EdwardsPoint> for Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end Curve25519Dalek.scalar.Scalar.Insts

namespace Curve25519Dalek.SharedAScalar.Insts
namespace «CoreOpsArithMulEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Mul<EdwardsPoint> for &Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

namespace «CoreOpsArithMulEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Mul<EdwardsPoint> for &Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end Curve25519Dalek.SharedAScalar.Insts

namespace Curve25519Dalek.scalar.Scalar.Insts
namespace «CoreOpsArithMulEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Mul<EdwardsPoint> for Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

namespace «CoreOpsArithMulEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Mul<EdwardsPoint> for Scalar`: as the borrowed form. -/
recall mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end Curve25519Dalek.scalar.Scalar.Insts

namespace Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithMulSharedAScalarEdwardsPointx86_64-no-tables»

/-- `Mul<&Scalar> for &EdwardsPoint`: `scalar • self` (unreduced, `< 2^255`). -/
recall mul_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (scalar : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAScalarEdwardsPointx86_64-no-tables»
end Curve25519Dalek.«Shared0EdwardsPointx86_64-no-tables».Insts

namespace Curve25519Dalek.«Shared0EdwardsPointi686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithMulSharedAScalarEdwardsPointi686-no-tables»

/-- `Mul<&Scalar> for &EdwardsPoint`: `scalar • self` (unreduced, `< 2^255`). -/
recall mul_spec (self : edwards.EdwardsPoint.«i686-no-tables») (scalar : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAScalarEdwardsPointi686-no-tables»
end Curve25519Dalek.«Shared0EdwardsPointi686-no-tables».Insts

namespace Curve25519Dalek.Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Mul<&EdwardsPoint> for &Scalar`: as `&EdwardsPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (point : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.IsBounded) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

namespace «CoreOpsArithMulSharedAEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Mul<&EdwardsPoint> for &Scalar`: as `&EdwardsPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (point : edwards.EdwardsPoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.IsBounded) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end Curve25519Dalek.Shared0Scalar.Insts

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`). -/
recall mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`). -/
recall mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end Curve25519Dalek.edwards.«EdwardsPointi686-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`). -/
recall mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`). -/
recall mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end Curve25519Dalek.edwards.«EdwardsPointi686-no-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::mul_clamped`: `clamp bytes • self`, with RFC 7748's clamping of the
little-endian value of `bytes`. -/
recall mul_clamped_spec (self : EdwardsPoint.«x86_64-tables») (bytes : Array U8 32#usize)
    (hself : self.IsBounded) (hon : self.OnCurve) :
    mul_clamped self bytes ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_clamped_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::mul_clamped`: `clamp bytes • self`, with RFC 7748's clamping of the
little-endian value of `bytes`. -/
recall mul_clamped_spec (self : EdwardsPoint.«i686-tables») (bytes : Array U8 32#usize)
    (hself : self.IsBounded) (hon : self.OnCurve) :
    mul_clamped self bytes ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_clamped_spec

end Curve25519Dalek.edwards.«EdwardsPointi686-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::mul_clamped`: `clamp bytes • self`, with RFC 7748's clamping of the
little-endian value of `bytes`. -/
recall mul_clamped_spec (self : EdwardsPoint.«x86_64-no-tables») (bytes : Array U8 32#usize)
    (hself : self.IsBounded) (hon : self.OnCurve) :
    mul_clamped self bytes ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_clamped_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::mul_clamped`: `clamp bytes • self`, with RFC 7748's clamping of the
little-endian value of `bytes`. -/
recall mul_clamped_spec (self : EdwardsPoint.«i686-no-tables») (bytes : Array U8 32#usize)
    (hself : self.IsBounded) (hon : self.OnCurve) :
    mul_clamped self bytes ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_clamped_spec

end Curve25519Dalek.edwards.«EdwardsPointi686-no-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::mul_base_clamped`: `clamp bytes • B`, with RFC 7748's clamping of the
little-endian value of `bytes`. -/
recall mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_clamped_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::mul_base_clamped`: `clamp bytes • B`, with RFC 7748's clamping of the
little-endian value of `bytes`. -/
recall mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_clamped_spec

end Curve25519Dalek.edwards.«EdwardsPointi686-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::mul_base_clamped`: `clamp bytes • B`, with RFC 7748's clamping of the
little-endian value of `bytes`. -/
recall mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_clamped_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::mul_base_clamped`: `clamp bytes • B`, with RFC 7748's clamping of the
little-endian value of `bytes`. -/
recall mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_clamped_spec

end Curve25519Dalek.edwards.«EdwardsPointi686-no-tables»

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-tables»

/-- `MultiscalarMul::multiscalar_mul` for `EdwardsPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`). -/
recall multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«x86_64-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«x86_64-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«x86_64-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms multiscalar_mul_spec

end «Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsMultiscalarMulEdwardsPointi686-tables»

/-- `MultiscalarMul::multiscalar_mul` for `EdwardsPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`). -/
recall multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«i686-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«i686-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«i686-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«i686-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms multiscalar_mul_spec

end «Curve25519_dalekTraitsMultiscalarMulEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `MultiscalarMul::multiscalar_mul` for `EdwardsPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`). -/
recall multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«x86_64-no-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«x86_64-no-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«x86_64-no-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms multiscalar_mul_spec

end «Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsMultiscalarMulEdwardsPointi686-no-tables»

/-- `MultiscalarMul::multiscalar_mul` for `EdwardsPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`). -/
recall multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«i686-no-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«i686-no-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«i686-no-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms multiscalar_mul_spec

end «Curve25519_dalekTraitsMultiscalarMulEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `EdwardsPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; Straus below `190` points, Pippenger from `190` on; unreduced scalars
`< 2^255`). -/
recall optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«x86_64-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«x86_64-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.IsBounded)
    (hps_on : ∀ P, some P ∈ ops → P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-tables») => (none ∈ ops → r = none) ∧
        ∀ ps, ops = ps.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧
          R.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms optional_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-tables»

/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `EdwardsPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; Straus below `190` points, Pippenger from `190` on; unreduced scalars
`< 2^255`). -/
recall optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«i686-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«i686-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.IsBounded)
    (hps_on : ∀ P, some P ∈ ops → P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«i686-tables») => (none ∈ ops → r = none) ∧
        ∀ ps, ops = ps.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧
          R.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms optional_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `EdwardsPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; Straus below `190` points, Pippenger from `190` on; unreduced scalars
`< 2^255`). -/
recall optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«x86_64-no-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«x86_64-no-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.IsBounded)
    (hps_on : ∀ P, some P ∈ ops → P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-no-tables») => (none ∈ ops → r = none) ∧
        ∀ ps, ops = ps.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧
          R.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms optional_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-no-tables»

/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `EdwardsPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; Straus below `190` points, Pippenger from `190` on; unreduced scalars
`< 2^255`). -/
recall optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«i686-no-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«i686-no-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.IsBounded)
    (hps_on : ∀ P, some P ∈ ops → P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«i686-no-tables») => (none ∈ ops → r = none) ∧
        ∀ ps, ops = ps.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧
          R.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms optional_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeEdwardsPrecomputation`: a precomputation
of the points the input yields (through `borrow`). -/
recall new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«x86_64-tables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«x86_64-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«x86_64-tables») => P' = P ⦄)
      ys ps)
    (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeEdwardsPrecomputation.«x86_64-tables») =>
        r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms new_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeEdwardsPrecomputation`: a precomputation
of the points the input yields (through `borrow`). -/
recall new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«i686-tables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«i686-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«i686-tables») => P' = P ⦄)
      ys ps)
    (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeEdwardsPrecomputation.«i686-tables») =>
        r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms new_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeEdwardsPrecomputation`: a precomputation
of the points the input yields (through `borrow`). -/
recall new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«x86_64-no-tables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«x86_64-no-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«x86_64-no-tables») => P' = P ⦄)
      ys ps)
    (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeEdwardsPrecomputation.«x86_64-no-tables») =>
        r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms new_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeEdwardsPrecomputation`: a precomputation
of the points the input yields (through `borrow`). -/
recall new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«i686-no-tables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«i686-no-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«i686-no-tables») => P' = P ⦄)
      ys ps)
    (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeEdwardsPrecomputation.«i686-no-tables») =>
        r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms new_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeEdwardsPrecomputation`: the number of
static points. -/
recall len_spec (self : VartimeEdwardsPrecomputation.«x86_64-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms len_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeEdwardsPrecomputation`: the number of
static points. -/
recall len_spec (self : VartimeEdwardsPrecomputation.«i686-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms len_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeEdwardsPrecomputation`: the number of
static points. -/
recall len_spec (self : VartimeEdwardsPrecomputation.«x86_64-no-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms len_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeEdwardsPrecomputation`: the number of
static points. -/
recall len_spec (self : VartimeEdwardsPrecomputation.«i686-no-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms len_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeEdwardsPrecomputation`: whether
there are no static points. -/
recall is_empty_spec (self : VartimeEdwardsPrecomputation.«x86_64-tables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.alloc] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_empty_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»

/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeEdwardsPrecomputation`: whether
there are no static points. -/
recall is_empty_spec (self : VartimeEdwardsPrecomputation.«i686-tables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.alloc] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_empty_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeEdwardsPrecomputation`: whether
there are no static points. -/
recall is_empty_spec (self : VartimeEdwardsPrecomputation.«x86_64-no-tables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.alloc] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_empty_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»

/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeEdwardsPrecomputation`: whether
there are no static points. -/
recall is_empty_spec (self : VartimeEdwardsPrecomputation.«i686-no-tables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.alloc] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_empty_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeEdwardsPrecomputation` (static points `self.points`): `none` iff some dynamic point is
`none`; otherwise `∑ s_i • P_i + ∑ d_i • Q_i`, missing static scalars counting as `0` (if no point
is `none`, at most `|self.points|` static scalars and as many dynamic scalars as dynamic points). -/
recall optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«x86_64-tables») Clause4_IntoIter)
    (self : VartimeEdwardsPrecomputation.«x86_64-tables»)
    (static_scalars : I) (dynamic_scalars : J) (dynamic_points : K) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«x86_64-tables»))
    (hself : self.IsValid) (hself_b : self.IsBounded)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.IsBounded)
    (hqs_on : ∀ Q, some Q ∈ qops → Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ self.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-tables») => (none ∈ qops → r = none) ∧
        ∀ qs, qops = qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds qs).sum ∧
          R.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms optional_mixed_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»

/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeEdwardsPrecomputation` (static points `self.points`): `none` iff some dynamic point is
`none`; otherwise `∑ s_i • P_i + ∑ d_i • Q_i`, missing static scalars counting as `0` (if no point
is `none`, at most `|self.points|` static scalars and as many dynamic scalars as dynamic points). -/
recall optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«i686-tables») Clause4_IntoIter)
    (self : VartimeEdwardsPrecomputation.«i686-tables»)
    (static_scalars : I) (dynamic_scalars : J) (dynamic_points : K) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«i686-tables»))
    (hself : self.IsValid) (hself_b : self.IsBounded)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.IsBounded)
    (hqs_on : ∀ Q, some Q ∈ qops → Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ self.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«i686-tables») => (none ∈ qops → r = none) ∧
        ∀ qs, qops = qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds qs).sum ∧
          R.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms optional_mixed_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeEdwardsPrecomputation` (static points `self.points`): `none` iff some dynamic point is
`none`; otherwise `∑ s_i • P_i + ∑ d_i • Q_i`, missing static scalars counting as `0` (if no point
is `none`, at most `|self.points|` static scalars and as many dynamic scalars as dynamic points). -/
recall optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«x86_64-no-tables») Clause4_IntoIter)
    (self : VartimeEdwardsPrecomputation.«x86_64-no-tables»)
    (static_scalars : I) (dynamic_scalars : J) (dynamic_points : K) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«x86_64-no-tables»))
    (hself : self.IsValid) (hself_b : self.IsBounded)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.IsBounded)
    (hqs_on : ∀ Q, some Q ∈ qops → Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ self.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-no-tables») => (none ∈ qops → r = none) ∧
        ∀ qs, qops = qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds qs).sum ∧
          R.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms optional_mixed_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»

/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeEdwardsPrecomputation` (static points `self.points`): `none` iff some dynamic point is
`none`; otherwise `∑ s_i • P_i + ∑ d_i • Q_i`, missing static scalars counting as `0` (if no point
is `none`, at most `|self.points|` static scalars and as many dynamic scalars as dynamic points). -/
recall optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«i686-no-tables») Clause4_IntoIter)
    (self : VartimeEdwardsPrecomputation.«i686-no-tables»)
    (static_scalars : I) (dynamic_scalars : J) (dynamic_points : K) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«i686-no-tables»))
    (hself : self.IsValid) (hself_b : self.IsBounded)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.IsBounded)
    (hqs_on : ∀ Q, some Q ∈ qops → Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ self.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«i686-no-tables») => (none ∈ qops → r = none) ∧
        ∀ qs, qops = qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds qs).sum ∧
          R.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms optional_mixed_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-no-tables».Insts

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`). -/
recall vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : EdwardsPoint.«x86_64-tables») (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255)
    (hA : A.IsBounded) (hon : A.OnCurve) (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms vartime_double_scalar_mul_basepoint_spec

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`). -/
recall vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : EdwardsPoint.«i686-tables») (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255)
    (hA : A.IsBounded) (hon : A.OnCurve) (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms vartime_double_scalar_mul_basepoint_spec

end «EdwardsPointi686-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`). -/
recall vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : EdwardsPoint.«x86_64-no-tables») (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255)
    (hA : A.IsBounded) (hon : A.OnCurve) (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms vartime_double_scalar_mul_basepoint_spec

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`). -/
recall vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : EdwardsPoint.«i686-no-tables») (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255)
    (hA : A.IsBounded) (hon : A.OnCurve) (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms vartime_double_scalar_mul_basepoint_spec

end «EdwardsPointi686-no-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::vartime_triple_scalar_mul_basepoint`: `a1 • A1 + a2 • A2 + b • B` for the
basepoint `B` (any `b`, which the code splits
into two `128`-bit halves). -/
recall vartime_triple_scalar_mul_basepoint_spec (a1 : scalar.HalfWidthScalar)
    (A1 : EdwardsPoint.«x86_64-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : EdwardsPoint.«x86_64-tables»)
    (b : scalar.Scalar) (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.IsBounded) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.IsBounded) (hA2_on : A2.OnCurve) :
    vartime_triple_scalar_mul_basepoint a1 A1 a2 A2 b ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧
        r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms vartime_triple_scalar_mul_basepoint_spec

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::vartime_triple_scalar_mul_basepoint`: `a1 • A1 + a2 • A2 + b • B` for the
basepoint `B` (any `b`, which the code splits
into two `128`-bit halves). -/
recall vartime_triple_scalar_mul_basepoint_spec (a1 : scalar.HalfWidthScalar)
    (A1 : EdwardsPoint.«i686-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : EdwardsPoint.«i686-tables»)
    (b : scalar.Scalar) (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.IsBounded) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.IsBounded) (hA2_on : A2.OnCurve) :
    vartime_triple_scalar_mul_basepoint a1 A1 a2 A2 b ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧
        r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms vartime_triple_scalar_mul_basepoint_spec

end «EdwardsPointi686-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards
namespace «EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::vartime_triple_scalar_mul_basepoint`: `a1 • A1 + a2 • A2 + b • B` for the
basepoint `B` (any `b`, which the code splits
into two `128`-bit halves). -/
recall vartime_triple_scalar_mul_basepoint_spec (a1 : scalar.HalfWidthScalar)
    (A1 : EdwardsPoint.«x86_64-no-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : EdwardsPoint.«x86_64-no-tables»)
    (b : scalar.Scalar) (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.IsBounded) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.IsBounded) (hA2_on : A2.OnCurve) :
    vartime_triple_scalar_mul_basepoint a1 A1 a2 A2 b ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧
        r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms vartime_triple_scalar_mul_basepoint_spec

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::vartime_triple_scalar_mul_basepoint`: `a1 • A1 + a2 • A2 + b • B` for the
basepoint `B` (any `b`, which the code splits
into two `128`-bit halves). -/
recall vartime_triple_scalar_mul_basepoint_spec (a1 : scalar.HalfWidthScalar)
    (A1 : EdwardsPoint.«i686-no-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : EdwardsPoint.«i686-no-tables»)
    (b : scalar.Scalar) (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.IsBounded) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.IsBounded) (hA2_on : A2.OnCurve) :
    vartime_triple_scalar_mul_basepoint a1 A1 a2 A2 b ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧
        r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms vartime_triple_scalar_mul_basepoint_spec

end «EdwardsPointi686-no-tables»
end Curve25519Dalek.edwards

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open window.«LookupTableAffineNielsPointx86_64-tables».Insts in
/-- `BasepointTable::create` (radix `2^4`): row `i` is the lookup table of
`2^(8 i) • basepoint`. -/
recall create_spec (basepoint : EdwardsPoint.«x86_64-tables») (hbasepoint : basepoint.IsBounded)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTable.«x86_64-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

open window.«LookupTableAffineNielsPointi686-tables».Insts in
/-- `BasepointTable::create` (radix `2^4`): row `i` is the lookup table of
`2^(8 i) • basepoint`. -/
recall create_spec (basepoint : EdwardsPoint.«i686-tables») (hbasepoint : basepoint.IsBounded)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTable.«i686-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::basepoint` (radix `2^4`): the table's point `self.point`. -/
recall basepoint_spec (self : EdwardsBasepointTable.«x86_64-tables») (hself : self.IsBounded)
    (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

/-- `BasepointTable::basepoint` (radix `2^4`): the table's point `self.point`. -/
recall basepoint_spec (self : EdwardsBasepointTable.«i686-tables») (hself : self.IsBounded)
    (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::mul_base` (radix `2^4`): `s • self.point` (unreduced,
`s.asNat < 2^255`). -/
recall mul_base_spec (self : EdwardsBasepointTable.«x86_64-tables») (s : scalar.Scalar)
    (hself : self.IsBounded) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

/-- `BasepointTable::mul_base` (radix `2^4`): `s • self.point` (unreduced,
`s.asNat < 2^255`). -/
recall mul_base_spec (self : EdwardsBasepointTable.«i686-tables») (s : scalar.Scalar)
    (hself : self.IsBounded) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTablex86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTable`: `mul_base`, i.e. `scalar • self.point`. -/
recall mul_spec (self : edwards.EdwardsBasepointTable.«x86_64-tables»)
    (scalar : scalar.Scalar) (hself : self.IsBounded)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTablex86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTablei686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTable`: `mul_base`, i.e. `scalar • self.point`. -/
recall mul_spec (self : edwards.EdwardsBasepointTable.«i686-tables»)
    (scalar : scalar.Scalar) (hself : self.IsBounded)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTablei686-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts
namespace «CoreOpsArithMulSharedAEdwardsBasepointTablex86_64-tablesEdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Mul<&EdwardsBasepointTable> for &Scalar`: as the other order. -/
recall mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTable.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.IsBounded) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsBasepointTablex86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithMulSharedAEdwardsBasepointTablei686-tablesEdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Mul<&EdwardsBasepointTable> for &Scalar`: as the other order. -/
recall mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTable.«i686-tables»)
    (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.IsBounded) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsBasepointTablei686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open window.«LookupTableRadix32AffineNielsPointx86_64-tables».Insts in
/-- `BasepointTable::create` (radix `2^5`): row `i` is the lookup table of
`2^(10 i) • basepoint`. -/
recall create_spec (basepoint : EdwardsPoint.«x86_64-tables») (hbasepoint : basepoint.IsBounded)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix32.«x86_64-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

open window.«LookupTableRadix32AffineNielsPointi686-tables».Insts in
/-- `BasepointTable::create` (radix `2^5`): row `i` is the lookup table of
`2^(10 i) • basepoint`. -/
recall create_spec (basepoint : EdwardsPoint.«i686-tables») (hbasepoint : basepoint.IsBounded)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix32.«i686-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::basepoint` (radix `2^5`): the table's point `self.point`. -/
recall basepoint_spec (self : EdwardsBasepointTableRadix32.«x86_64-tables»)
    (hself : self.IsBounded) (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

/-- `BasepointTable::basepoint` (radix `2^5`): the table's point `self.point`. -/
recall basepoint_spec (self : EdwardsBasepointTableRadix32.«i686-tables»)
    (hself : self.IsBounded) (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::mul_base` (radix `2^5`): `s • self.point` (unreduced,
`s.asNat < 2^255`). -/
recall mul_base_spec (self : EdwardsBasepointTableRadix32.«x86_64-tables») (s : scalar.Scalar)
    (hself : self.IsBounded) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

/-- `BasepointTable::mul_base` (radix `2^5`): `s • self.point` (unreduced,
`s.asNat < 2^255`). -/
recall mul_base_spec (self : EdwardsBasepointTableRadix32.«i686-tables») (s : scalar.Scalar)
    (hself : self.IsBounded) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix32x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix32`: `mul_base`, i.e. `scalar • self.point`. -/
recall mul_spec (self : edwards.EdwardsBasepointTableRadix32.«x86_64-tables»)
    (scalar : scalar.Scalar) (hself : self.IsBounded)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix32x86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix32i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix32`: `mul_base`, i.e. `scalar • self.point`. -/
recall mul_spec (self : edwards.EdwardsBasepointTableRadix32.«i686-tables»)
    (scalar : scalar.Scalar) (hself : self.IsBounded)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix32i686-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts
namespace «CoreOpsArithMulSharedAEdwardsBasepointTableRadix32x86_64-tablesEdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Mul<&EdwardsBasepointTableRadix32> for &Scalar`: as the other order. -/
recall mul_spec
    (self : scalar.Scalar)
    (basepoint_table : edwards.EdwardsBasepointTableRadix32.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.IsBounded) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsBasepointTableRadix32x86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithMulSharedAEdwardsBasepointTableRadix32i686-tablesEdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Mul<&EdwardsBasepointTableRadix32> for &Scalar`: as the other order. -/
recall mul_spec
    (self : scalar.Scalar)
    (basepoint_table : edwards.EdwardsBasepointTableRadix32.«i686-tables»)
    (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.IsBounded) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsBasepointTableRadix32i686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open window.«LookupTableRadix64AffineNielsPointx86_64-tables».Insts in
/-- `BasepointTable::create` (radix `2^6`): row `i` is the lookup table of
`2^(12 i) • basepoint`. -/
recall create_spec (basepoint : EdwardsPoint.«x86_64-tables») (hbasepoint : basepoint.IsBounded)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix64.«x86_64-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

open window.«LookupTableRadix64AffineNielsPointi686-tables».Insts in
/-- `BasepointTable::create` (radix `2^6`): row `i` is the lookup table of
`2^(12 i) • basepoint`. -/
recall create_spec (basepoint : EdwardsPoint.«i686-tables») (hbasepoint : basepoint.IsBounded)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix64.«i686-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::basepoint` (radix `2^6`): the table's point `self.point`. -/
recall basepoint_spec (self : EdwardsBasepointTableRadix64.«x86_64-tables»)
    (hself : self.IsBounded) (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

/-- `BasepointTable::basepoint` (radix `2^6`): the table's point `self.point`. -/
recall basepoint_spec (self : EdwardsBasepointTableRadix64.«i686-tables»)
    (hself : self.IsBounded) (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::mul_base` (radix `2^6`): `s • self.point` (unreduced,
`s.asNat < 2^255`). -/
recall mul_base_spec (self : EdwardsBasepointTableRadix64.«x86_64-tables») (s : scalar.Scalar)
    (hself : self.IsBounded) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

/-- `BasepointTable::mul_base` (radix `2^6`): `s • self.point` (unreduced,
`s.asNat < 2^255`). -/
recall mul_base_spec (self : EdwardsBasepointTableRadix64.«i686-tables») (s : scalar.Scalar)
    (hself : self.IsBounded) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix64x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix64`: `mul_base`, i.e. `scalar • self.point`. -/
recall mul_spec (self : edwards.EdwardsBasepointTableRadix64.«x86_64-tables»)
    (scalar : scalar.Scalar) (hself : self.IsBounded)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix64x86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix64i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix64`: `mul_base`, i.e. `scalar • self.point`. -/
recall mul_spec (self : edwards.EdwardsBasepointTableRadix64.«i686-tables»)
    (scalar : scalar.Scalar) (hself : self.IsBounded)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix64i686-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts
namespace «CoreOpsArithMulSharedAEdwardsBasepointTableRadix64x86_64-tablesEdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Mul<&EdwardsBasepointTableRadix64> for &Scalar`: as the other order. -/
recall mul_spec
    (self : scalar.Scalar)
    (basepoint_table : edwards.EdwardsBasepointTableRadix64.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.IsBounded) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsBasepointTableRadix64x86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithMulSharedAEdwardsBasepointTableRadix64i686-tablesEdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Mul<&EdwardsBasepointTableRadix64> for &Scalar`: as the other order. -/
recall mul_spec
    (self : scalar.Scalar)
    (basepoint_table : edwards.EdwardsBasepointTableRadix64.«i686-tables»)
    (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.IsBounded) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsBasepointTableRadix64i686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open window.«LookupTableRadix128AffineNielsPointx86_64-tables».Insts in
/-- `BasepointTable::create` (radix `2^7`): row `i` is the lookup table of
`2^(14 i) • basepoint`. -/
recall create_spec (basepoint : EdwardsPoint.«x86_64-tables») (hbasepoint : basepoint.IsBounded)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix128.«x86_64-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

open window.«LookupTableRadix128AffineNielsPointi686-tables».Insts in
/-- `BasepointTable::create` (radix `2^7`): row `i` is the lookup table of
`2^(14 i) • basepoint`. -/
recall create_spec (basepoint : EdwardsPoint.«i686-tables») (hbasepoint : basepoint.IsBounded)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix128.«i686-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::basepoint` (radix `2^7`): the table's point `self.point`. -/
recall basepoint_spec (self : EdwardsBasepointTableRadix128.«x86_64-tables»)
    (hself : self.IsBounded) (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

/-- `BasepointTable::basepoint` (radix `2^7`): the table's point `self.point`. -/
recall basepoint_spec (self : EdwardsBasepointTableRadix128.«i686-tables»)
    (hself : self.IsBounded) (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::mul_base` (radix `2^7`): `s • self.point` (unreduced,
`s.asNat < 2^255`). -/
recall mul_base_spec (self : EdwardsBasepointTableRadix128.«x86_64-tables») (s : scalar.Scalar)
    (hself : self.IsBounded) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

/-- `BasepointTable::mul_base` (radix `2^7`): `s • self.point` (unreduced,
`s.asNat < 2^255`). -/
recall mul_base_spec (self : EdwardsBasepointTableRadix128.«i686-tables») (s : scalar.Scalar)
    (hself : self.IsBounded) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix128x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix128`: `mul_base`, i.e. `scalar • self.point`. -/
recall mul_spec (self : edwards.EdwardsBasepointTableRadix128.«x86_64-tables»)
    (scalar : scalar.Scalar) (hself : self.IsBounded)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix128x86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix128i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix128`: `mul_base`, i.e. `scalar • self.point`. -/
recall mul_spec (self : edwards.EdwardsBasepointTableRadix128.«i686-tables»)
    (scalar : scalar.Scalar) (hself : self.IsBounded)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix128i686-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts
set_option linter.style.longLine false
namespace «CoreOpsArithMulSharedAEdwardsBasepointTableRadix128x86_64-tablesEdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

set_option linter.style.longLine true

/-- `Mul<&EdwardsBasepointTableRadix128> for &Scalar`: as the other order. -/
recall mul_spec
    (self : scalar.Scalar)
    (basepoint_table : edwards.EdwardsBasepointTableRadix128.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.IsBounded) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsBasepointTableRadix128x86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithMulSharedAEdwardsBasepointTableRadix128i686-tablesEdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

set_option linter.style.longLine true

/-- `Mul<&EdwardsBasepointTableRadix128> for &Scalar`: as the other order. -/
recall mul_spec
    (self : scalar.Scalar)
    (basepoint_table : edwards.EdwardsBasepointTableRadix128.«i686-tables»)
    (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.IsBounded) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsBasepointTableRadix128i686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open window.«LookupTableRadix256AffineNielsPointx86_64-tables».Insts in
/-- `BasepointTable::create` (radix `2^8`): row `i` is the lookup table of
`2^(16 i) • basepoint`. -/
recall create_spec (basepoint : EdwardsPoint.«x86_64-tables») (hbasepoint : basepoint.IsBounded)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix256.«x86_64-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

open window.«LookupTableRadix256AffineNielsPointi686-tables».Insts in
/-- `BasepointTable::create` (radix `2^8`): row `i` is the lookup table of
`2^(16 i) • basepoint`. -/
recall create_spec (basepoint : EdwardsPoint.«i686-tables») (hbasepoint : basepoint.IsBounded)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix256.«i686-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::basepoint` (radix `2^8`): the table's point `self.point`. -/
recall basepoint_spec (self : EdwardsBasepointTableRadix256.«x86_64-tables»)
    (hself : self.IsBounded) (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

/-- `BasepointTable::basepoint` (radix `2^8`): the table's point `self.point`. -/
recall basepoint_spec (self : EdwardsBasepointTableRadix256.«i686-tables»)
    (hself : self.IsBounded) (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `BasepointTable::mul_base` (radix `2^8`): `s • self.point` (unreduced,
`s.asNat < 2^255`). -/
recall mul_base_spec (self : EdwardsBasepointTableRadix256.«x86_64-tables») (s : scalar.Scalar)
    (hself : self.IsBounded) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

/-- `BasepointTable::mul_base` (radix `2^8`): `s • self.point` (unreduced,
`s.asNat < 2^255`). -/
recall mul_base_spec (self : EdwardsBasepointTableRadix256.«i686-tables») (s : scalar.Scalar)
    (hself : self.IsBounded) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix256x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix256`: `mul_base`, i.e. `scalar • self.point`. -/
recall mul_spec (self : edwards.EdwardsBasepointTableRadix256.«x86_64-tables»)
    (scalar : scalar.Scalar) (hself : self.IsBounded)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix256x86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix256i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix256`: `mul_base`, i.e. `scalar • self.point`. -/
recall mul_spec (self : edwards.EdwardsBasepointTableRadix256.«i686-tables»)
    (scalar : scalar.Scalar) (hself : self.IsBounded)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix256i686-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts
set_option linter.style.longLine false
namespace «CoreOpsArithMulSharedAEdwardsBasepointTableRadix256x86_64-tablesEdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

set_option linter.style.longLine true

/-- `Mul<&EdwardsBasepointTableRadix256> for &Scalar`: as the other order. -/
recall mul_spec
    (self : scalar.Scalar)
    (basepoint_table : edwards.EdwardsBasepointTableRadix256.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.IsBounded) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsBasepointTableRadix256x86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithMulSharedAEdwardsBasepointTableRadix256i686-tablesEdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

set_option linter.style.longLine true

/-- `Mul<&EdwardsBasepointTableRadix256> for &Scalar`: as the other order. -/
recall mul_spec
    (self : scalar.Scalar)
    (basepoint_table : edwards.EdwardsBasepointTableRadix256.«i686-tables»)
    (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.IsBounded) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAEdwardsBasepointTableRadix256i686-tablesEdwardsPointi686-tables»
end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTable`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix32.«x86_64-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTable.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32i686-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTable`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix32.«i686-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTable.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTable`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix64.«x86_64-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTable.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64i686-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTable`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix64.«i686-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTable.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTable`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix128.«x86_64-tables»)
    (htable : table.IsBounded) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTable.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128i686-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTable`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix128.«i686-tables»)
    (htable : table.IsBounded) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTable.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTable`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix256.«x86_64-tables»)
    (htable : table.IsBounded) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTable.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256i686-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTable`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix256.«i686-tables»)
    (htable : table.IsBounded) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTable.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix32`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTable.«x86_64-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTablei686-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix32`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTable.«i686-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTablei686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix32`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix64.«x86_64-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64i686-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix32`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix64.«i686-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix32`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix128.«x86_64-tables»)
    (htable : table.IsBounded) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128i686-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix32`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix128.«i686-tables»)
    (htable : table.IsBounded) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix32`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix256.«x86_64-tables»)
    (htable : table.IsBounded) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256i686-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix32`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix256.«i686-tables»)
    (htable : table.IsBounded) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix64`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTable.«x86_64-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTablei686-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix64`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTable.«i686-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTablei686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix64`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix32.«x86_64-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32i686-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix64`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix32.«i686-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix64`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix128.«x86_64-tables»)
    (htable : table.IsBounded) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128i686-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix64`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix128.«i686-tables»)
    (htable : table.IsBounded) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix64`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix256.«x86_64-tables»)
    (htable : table.IsBounded) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256i686-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix64`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix256.«i686-tables»)
    (htable : table.IsBounded) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix128`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTable.«x86_64-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTablei686-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix128`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTable.«i686-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTablei686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix128`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix32.«x86_64-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32i686-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix128`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix32.«i686-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix128`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix64.«x86_64-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64i686-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix128`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix64.«i686-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix128`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix256.«x86_64-tables»)
    (htable : table.IsBounded) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256i686-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix128`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix256.«i686-tables»)
    (htable : table.IsBounded) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix256`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTable.«x86_64-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTablei686-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix256`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTable.«i686-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTablei686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix256`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix32.«x86_64-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32i686-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix256`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix32.«i686-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix256`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix64.«x86_64-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64i686-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix256`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix64.«i686-tables») (htable : table.IsBounded)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix256`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix128.«x86_64-tables»)
    (htable : table.IsBounded) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«x86_64-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128i686-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix256`: a table of the same
point. -/
recall from_spec (table : EdwardsBasepointTableRadix128.«i686-tables»)
    (htable : table.IsBounded) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«i686-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::mul_by_cofactor`: `8 • self`. -/
recall mul_by_cofactor_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    mul_by_cofactor self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 8 • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_by_cofactor_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::mul_by_cofactor`: `8 • self`. -/
recall mul_by_cofactor_spec (self : EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    mul_by_cofactor self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = 8 • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_by_cofactor_spec

end Curve25519Dalek.edwards.«EdwardsPointi686-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::mul_by_cofactor`: `8 • self`. -/
recall mul_by_cofactor_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    mul_by_cofactor self ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 8 • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_by_cofactor_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::mul_by_cofactor`: `8 • self`. -/
recall mul_by_cofactor_spec (self : EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    mul_by_cofactor self ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = 8 • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_by_cofactor_spec

end Curve25519Dalek.edwards.«EdwardsPointi686-no-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::is_small_order`: `8 • self = 0`. -/
recall is_small_order_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    is_small_order self ⦃ (r : Bool) => r = true ↔ 8 • self.toPoint = 0 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_small_order_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::is_small_order`: `8 • self = 0`. -/
recall is_small_order_spec (self : EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    is_small_order self ⦃ (r : Bool) => r = true ↔ 8 • self.toPoint = 0 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_small_order_spec

end Curve25519Dalek.edwards.«EdwardsPointi686-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::is_small_order`: `8 • self = 0`. -/
recall is_small_order_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    is_small_order self ⦃ (r : Bool) => r = true ↔ 8 • self.toPoint = 0 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_small_order_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::is_small_order`: `8 • self = 0`. -/
recall is_small_order_spec (self : EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    is_small_order self ⦃ (r : Bool) => r = true ↔ 8 • self.toPoint = 0 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_small_order_spec

end Curve25519Dalek.edwards.«EdwardsPointi686-no-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::is_torsion_free`: `L • self = 0` (multiplication by the unreduced
`BASEPOINT_ORDER`). -/
recall is_torsion_free_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    is_torsion_free self ⦃ (r : Bool) => r = true ↔ L • self.toPoint = 0 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_torsion_free_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::is_torsion_free`: `L • self = 0` (multiplication by the unreduced
`BASEPOINT_ORDER`). -/
recall is_torsion_free_spec (self : EdwardsPoint.«i686-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    is_torsion_free self ⦃ (r : Bool) => r = true ↔ L • self.toPoint = 0 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_torsion_free_spec

end Curve25519Dalek.edwards.«EdwardsPointi686-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::is_torsion_free`: `L • self = 0` (multiplication by the unreduced
`BASEPOINT_ORDER`). -/
recall is_torsion_free_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    is_torsion_free self ⦃ (r : Bool) => r = true ↔ L • self.toPoint = 0 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_torsion_free_spec

end Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables»

namespace Curve25519Dalek.edwards.«EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::is_torsion_free`: `L • self = 0` (multiplication by the unreduced
`BASEPOINT_ORDER`). -/
recall is_torsion_free_spec (self : EdwardsPoint.«i686-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    is_torsion_free self ⦃ (r : Bool) => r = true ↔ L • self.toPoint = 0 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_torsion_free_spec

end Curve25519Dalek.edwards.«EdwardsPointi686-no-tables»
