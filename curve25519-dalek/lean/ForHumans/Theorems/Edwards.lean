/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Curve25519.Edwards.Basepoint
public import Proofs.Curve25519.Edwards.Encoding
public import Proofs.Curve25519.Montgomery
public import Proofs.Curve25519.X25519
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import ForHumans.Specs.Representation.Scalar
public import ForHumans.Specs.Representation
public import Proofs.Representation.Window
public import Proofs.External.Subtle
public import ForHumans.Specs.Representation.Iterator
import Proofs
import Proofs.External.Zeroize.Instances
public section

/-! # Theorems about `src/edwards.rs`

The public items of `edwards.rs`, in its order.

Points are specified through `toPoint` under the invariants `OnCurve` and `IsBounded`, basepoint
tables through `point` under `IsTable` and `IsBounded`, precomputations through `points` under
`IsValid` and `IsBounded`. Scalars act by their unreduced value `asNat`, which must be `< 2^255`
(invariant #1 of `Scalar` in `scalar.rs`). Iterator inputs are given by the lists they yield. The
multiscalar statements are about the patched code
(`translation-patches/edwards-{multiscalar,optional_multiscalar}_mul.patch`), which requires as many
scalars as points; the original panics unless both inputs' `size_hint`s are exact and equal.

`CompressedEdwardsY` does not depend on the configuration. Everything else is stated after it, for
`x86_64-tables`; the other configurations' copies are generated in `Edwards/`, without the
basepoint tables for the configurations without precomputed tables.

Definitions used, in `ForHumans/Specs/`: `edwards`, `montgomery` (`Curves.lean`), `p`, `L`
(`Constants.lean`), `basepoint`, `encode`, `decodeLenient` (`Edwards.lean`), `edwardsToMontgomery`
(`Montgomery.lean`), `decodeScalar25519`, `encodeUCoordinate` (`X25519.lean`),
`EdwardsPoint.toPoint`, `OnCurve` (`Representation/Edwards.lean`), `Scalar.asNat`,
`HalfWidthScalar.asNat` (`Representation/Scalar.lean`), `Array.toVector`
(`Representation/Array.lean`), `Iterator.Yields`, `IntoIterator.Yields`
(`Representation/Iterator.lean`), `subtle.Choice`, `Choice.IsValid` (`External/Subtle/`).
Not to be read (see `Basic.lean`): the invariants `IsBounded`, the tables' `IsTable`, `IsBounded`
and `point`, the precomputations' `IsValid`, `IsBounded` and `points`, defined in
`Proofs/Representation/`.

Not translated: `Debug`, `Hash`, the `group` and `serde` impls, `random`, hash-to-curve, and the
provided methods of the traits. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel Curve25519Dalek
open Curve25519Dalek.edwards (CompressedEdwardsY)
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)

namespace Theorems.edwards.CompressedEdwardsY

/-- `ConstantTimeEq`: byte equality (two encodings of one point can differ). -/
theorem ct_eq (a b : CompressedEdwardsY) :
    CompressedEdwardsY.Insts.SubtleConstantTimeEq.ct_eq a b ⦃ (r : subtle.Choice) =>
      r.IsValid ∧ (r = 1#u8 ↔ a = b) ⦄ :=
  CompressedEdwardsY.Insts.SubtleConstantTimeEq.ct_eq_spec a b

/-- `PartialEq`: byte equality (two encodings of one point can differ). -/
theorem eq (a b : CompressedEdwardsY) :
    CompressedEdwardsY.Insts.CoreCmpPartialEqCompressedEdwardsY.eq a b ⦃ (r : Bool) =>
      r = true ↔ a = b ⦄ :=
  CompressedEdwardsY.Insts.CoreCmpPartialEqCompressedEdwardsY.eq_spec a b

/-- `as_bytes`: the bytes. -/
theorem as_bytes (c : CompressedEdwardsY) :
    CompressedEdwardsY.as_bytes c ⦃ (r : Array U8 32#usize) => r = c ⦄ :=
  CompressedEdwardsY.as_bytes_spec c

/-- `to_bytes`: the bytes. -/
theorem to_bytes (c : CompressedEdwardsY) :
    CompressedEdwardsY.to_bytes c ⦃ (r : Array U8 32#usize) => r = c ⦄ :=
  CompressedEdwardsY.to_bytes_spec c

/-- `TryFrom<&[u8]>`: as `from_slice`. -/
theorem try_from (slice : Slice U8) :
    CompressedEdwardsY.Insts.CoreConvertTryFromShared0SliceU8TryFromSliceError.try_from slice
      ⦃ (r : core.result.Result CompressedEdwardsY core.array.TryFromSliceError) =>
        match r with
        | .Ok c => slice.length = 32 ∧ ∀ i < 32, c[i]! = slice[i]!
        | .Err _ => slice.length ≠ 32 ⦄ :=
  CompressedEdwardsY.Insts.CoreConvertTryFromShared0SliceU8TryFromSliceError.try_from_spec slice

/-- `Identity`: the encoding of the neutral element. -/
theorem identity :
    CompressedEdwardsY.Insts.Curve25519_dalekTraitsIdentity.identity ⦃ (r : CompressedEdwardsY) =>
      r.toVector = encode 0 ⦄ :=
  CompressedEdwardsY.Insts.Curve25519_dalekTraitsIdentity.identity_spec

/-- `Default`: the encoding of the neutral element. -/
theorem default :
    CompressedEdwardsY.Insts.CoreDefaultDefault.default ⦃ (r : CompressedEdwardsY) =>
      r.toVector = encode 0 ⦄ :=
  CompressedEdwardsY.Insts.CoreDefaultDefault.default_spec

/-- `from_slice`: the bytes of a slice of length `32`, an error otherwise. -/
theorem from_slice (bytes : Slice U8) :
    CompressedEdwardsY.from_slice bytes
      ⦃ (r : core.result.Result CompressedEdwardsY core.array.TryFromSliceError) =>
        match r with
        | .Ok c => bytes.length = 32 ∧ ∀ i < 32, c[i]! = bytes[i]!
        | .Err _ => bytes.length ≠ 32 ⦄ :=
  CompressedEdwardsY.from_slice_spec bytes

/-- `Zeroize`: leaves the encoding of the neutral element. -/
theorem zeroize (c : CompressedEdwardsY) :
    CompressedEdwardsY.Insts.ZeroizeZeroize.zeroize c ⦃ (r : CompressedEdwardsY) =>
      r.toVector = encode 0 ⦄ :=
  CompressedEdwardsY.Insts.ZeroizeZeroize.zeroize_spec c

end Theorems.edwards.CompressedEdwardsY

/-! ## Per configuration -/

-- BEGIN PER-CONFIG
namespace Theorems.edwards.«x86_64-tables»

/-- `EdwardsPoint` in this configuration. -/
abbrev EdwardsPoint := edwards.EdwardsPoint.«x86_64-tables»

/-- `VartimeEdwardsPrecomputation` in this configuration. -/
abbrev VartimeEdwardsPrecomputation := edwards.VartimeEdwardsPrecomputation.«x86_64-tables»

/-- `CompressedEdwardsY::decompress`: the lenient decoding `decodeLenient` of the bytes (`y`
reduced modulo `p`, `x = 0` accepted with either sign); the point is on the curve. -/
theorem CompressedEdwardsY.decompress (c : CompressedEdwardsY) :
    CompressedEdwardsY.decompress.«x86_64-tables» c ⦃ (r : Option EdwardsPoint) =>
      r.map (·.toPoint) = decodeLenient c.toVector ∧ ∀ P, r = some P → P.OnCurve ∧ P.IsBounded ⦄ :=
  edwards.CompressedEdwardsY.«x86_64-tables».decompress_spec c

namespace EdwardsPoint

open edwards.EdwardsPoint.«x86_64-tables».Insts

/-- `Identity`: the neutral element. -/
theorem identity :
    Curve25519_dalekTraitsIdentity.identity ⦃ (r : EdwardsPoint) =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄ :=
  Curve25519_dalekTraitsIdentity.identity_spec

/-- `Default`: the neutral element. -/
theorem default :
    CoreDefaultDefault.default ⦃ (r : EdwardsPoint) => r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄ :=
  CoreDefaultDefault.default_spec

/-- `Zeroize`: leaves the neutral element. -/
theorem zeroize (P : EdwardsPoint) :
    ZeroizeZeroize.zeroize P ⦃ (r : EdwardsPoint) => r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄ :=
  ZeroizeZeroize.zeroize_spec P

/-- `ConditionallySelectable`: `a` if `choice = 0`, `b` if `choice = 1`. -/
theorem conditional_select (a b : EdwardsPoint) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    SubtleConditionallySelectable.conditional_select a b choice ⦃ (r : EdwardsPoint) =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  SubtleConditionallySelectable.conditional_select_spec a b choice hchoice

/-- `ConstantTimeEq`: equality of the represented points. -/
theorem ct_eq (P Q : EdwardsPoint) (hP : P.OnCurve) (hP' : P.IsBounded) (hQ : Q.OnCurve)
    (hQ' : Q.IsBounded) :
    SubtleConstantTimeEq.ct_eq P Q ⦃ (r : subtle.Choice) =>
      r.IsValid ∧ (r = 1#u8 ↔ P.toPoint = Q.toPoint) ⦄ :=
  SubtleConstantTimeEq.ct_eq_spec P Q hP' hQ' hP hQ

/-- `PartialEq`: equality of the represented points. -/
theorem eq (P Q : EdwardsPoint) (hP : P.OnCurve) (hP' : P.IsBounded) (hQ : Q.OnCurve)
    (hQ' : Q.IsBounded) :
    «CoreCmpPartialEqEdwardsPointx86_64-tables».eq P Q ⦃ (r : Bool) =>
      r = true ↔ P.toPoint = Q.toPoint ⦄ :=
  «CoreCmpPartialEqEdwardsPointx86_64-tables».eq_spec P Q hP' hQ' hP hQ

end EdwardsPoint

namespace EdwardsPoint

open edwards.«EdwardsPointx86_64-tables»

/-- `to_montgomery`: RFC 7748's encoding of the `u`-coordinate of the Montgomery image of the
point (`0` for the identity). -/
theorem to_montgomery (P : EdwardsPoint) (hP : P.OnCurve) (hP' : P.IsBounded) :
    to_montgomery P ⦃ (r : montgomery.MontgomeryPoint) =>
      r.toVector = encodeUCoordinate (edwardsToMontgomery P.toPoint).u ⦄ :=
  to_montgomery_spec P hP' hP

/-- `to_montgomery_batch`: entry `i` is RFC 7748's encoding of the `u`-coordinate of the
Montgomery image of point `i` (`0` for the identity). -/
theorem to_montgomery_batch (Ps : Slice EdwardsPoint) (hPs : ∀ i < Ps.length, Ps[i]!.OnCurve)
    (hPs' : ∀ i < Ps.length, Ps[i]!.IsBounded) :
    to_montgomery_batch Ps ⦃ (r : alloc.vec.Vec montgomery.MontgomeryPoint) =>
      r.length = Ps.length ∧
        ∀ i < Ps.length,
          r[i]!.toVector = encodeUCoordinate (edwardsToMontgomery Ps[i]!.toPoint).u ⦄ :=
  to_montgomery_batch_spec Ps hPs' hPs

/-- `compress`: RFC 8032's encoding of the point. -/
theorem compress (P : EdwardsPoint) (hP : P.OnCurve) (hP' : P.IsBounded) :
    compress P ⦃ (r : CompressedEdwardsY) => r.toVector = encode P.toPoint ⦄ :=
  compress_spec P hP' hP

/-- `compress_batch`: entry `i` is RFC 8032's encoding of point `i`. -/
theorem compress_batch {N : Usize} (Ps : Array EdwardsPoint N) (hPs : ∀ i < N.val, Ps[i]!.OnCurve)
    (hPs' : ∀ i < N.val, Ps[i]!.IsBounded) :
    compress_batch Ps ⦃ (r : Array CompressedEdwardsY N) =>
      ∀ i < N.val, r[i]!.toVector = encode Ps[i]!.toPoint ⦄ :=
  compress_batch_spec Ps hPs' hPs

/-- `compress_batch_alloc`: entry `i` is RFC 8032's encoding of point `i`. -/
theorem compress_batch_alloc (Ps : Slice EdwardsPoint) (hPs : ∀ i < Ps.length, Ps[i]!.OnCurve)
    (hPs' : ∀ i < Ps.length, Ps[i]!.IsBounded) :
    compress_batch_alloc Ps ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = Ps.length ∧ ∀ i < Ps.length, r[i]!.toVector = encode Ps[i]!.toPoint ⦄ :=
  compress_batch_alloc_spec Ps hPs' hPs

end EdwardsPoint

/-! ### Arithmetic

The operator impls, named by the Rust expression they evaluate (`P`, `Q` points, `s` a scalar). -/

/-- `impl Add<&EdwardsPoint> for &EdwardsPoint` -/
abbrev «&P + &Q» := open «Shared0EdwardsPointx86_64-tables».Insts in
  «CoreOpsArithAddSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».add
/-- `impl Add<&EdwardsPoint> for EdwardsPoint` -/
abbrev «P + &Q» := open edwards.EdwardsPoint.«x86_64-tables».Insts in
  «CoreOpsArithAddSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».add
/-- `impl Add<EdwardsPoint> for &EdwardsPoint` -/
abbrev «&P + Q» := open «SharedAEdwardsPointx86_64-tables».Insts in
  «CoreOpsArithAddEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».add
/-- `impl Add<EdwardsPoint> for EdwardsPoint` -/
abbrev «P + Q» := open edwards.EdwardsPoint.«x86_64-tables».Insts in
  «CoreOpsArithAddEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».add
/-- `impl AddAssign<&EdwardsPoint> for EdwardsPoint` -/
abbrev «P += &Q» := open edwards.EdwardsPoint.«x86_64-tables».Insts in
  «CoreOpsArithAddAssignSharedAEdwardsPointx86_64-tables».add_assign
/-- `impl AddAssign<EdwardsPoint> for EdwardsPoint` -/
abbrev «P += Q» := open edwards.EdwardsPoint.«x86_64-tables».Insts in
  «CoreOpsArithAddAssignEdwardsPointx86_64-tables».add_assign

/-- `impl Sub<&EdwardsPoint> for &EdwardsPoint` -/
abbrev «&P - &Q» := open «Shared0EdwardsPointx86_64-tables».Insts in
  «CoreOpsArithSubSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».sub
/-- `impl Sub<&EdwardsPoint> for EdwardsPoint` -/
abbrev «P - &Q» := open edwards.EdwardsPoint.«x86_64-tables».Insts in
  «CoreOpsArithSubSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».sub
/-- `impl Sub<EdwardsPoint> for &EdwardsPoint` -/
abbrev «&P - Q» := open «SharedAEdwardsPointx86_64-tables».Insts in
  «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».sub
/-- `impl Sub<EdwardsPoint> for EdwardsPoint` -/
abbrev «P - Q» := open edwards.EdwardsPoint.«x86_64-tables».Insts in
  «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».sub
/-- `impl SubAssign<&EdwardsPoint> for EdwardsPoint` -/
abbrev «P -= &Q» := open edwards.EdwardsPoint.«x86_64-tables».Insts in
  «CoreOpsArithSubAssignSharedAEdwardsPointx86_64-tables».sub_assign
/-- `impl SubAssign<EdwardsPoint> for EdwardsPoint` -/
abbrev «P -= Q» := open edwards.EdwardsPoint.«x86_64-tables».Insts in
  «CoreOpsArithSubAssignEdwardsPointx86_64-tables».sub_assign

/-- `impl Neg for &EdwardsPoint` -/
abbrev «-&P» := open «Shared0EdwardsPointx86_64-tables».Insts in
  «CoreOpsArithNegEdwardsPointx86_64-tables».neg
/-- `impl Neg for EdwardsPoint` -/
abbrev «-P» := open edwards.EdwardsPoint.«x86_64-tables».Insts in
  «CoreOpsArithNegEdwardsPointx86_64-tables».neg

/-- `impl Mul<&Scalar> for &EdwardsPoint` -/
abbrev «&P * &s» := open «Shared0EdwardsPointx86_64-tables».Insts in
  «CoreOpsArithMulSharedAScalarEdwardsPointx86_64-tables».mul
/-- `impl Mul<&Scalar> for EdwardsPoint` -/
abbrev «P * &s» := open edwards.EdwardsPoint.«x86_64-tables».Insts in
  «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables».mul
/-- `impl Mul<Scalar> for &EdwardsPoint` -/
abbrev «&P * s» := open «SharedAEdwardsPointx86_64-tables».Insts in
  «CoreOpsArithMulScalarEdwardsPointx86_64-tables».mul
/-- `impl Mul<Scalar> for EdwardsPoint` -/
abbrev «P * s» := open edwards.EdwardsPoint.«x86_64-tables».Insts in
  «CoreOpsArithMulScalarEdwardsPointx86_64-tables».mul
/-- `impl MulAssign<&Scalar> for EdwardsPoint` -/
abbrev «P *= &s» :=
  edwards.EdwardsPoint.«x86_64-tables».Insts.CoreOpsArithMulAssignSharedAScalar.mul_assign
/-- `impl MulAssign<Scalar> for EdwardsPoint` -/
abbrev «P *= s» :=
  edwards.EdwardsPoint.«x86_64-tables».Insts.CoreOpsArithMulAssignScalar.mul_assign

/-- `impl Mul<&EdwardsPoint> for &Scalar` -/
abbrev «&s * &P» := open Shared0Scalar.Insts in
  «CoreOpsArithMulSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».mul
/-- `impl Mul<&EdwardsPoint> for Scalar` -/
abbrev «s * &P» := open scalar.Scalar.Insts in
  «CoreOpsArithMulSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».mul
/-- `impl Mul<EdwardsPoint> for &Scalar` -/
abbrev «&s * P» := open SharedAScalar.Insts in
  «CoreOpsArithMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».mul
/-- `impl Mul<EdwardsPoint> for Scalar` -/
abbrev «s * P» := open scalar.Scalar.Insts in
  «CoreOpsArithMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».mul

namespace EdwardsPoint

/-- `Add` and `AddAssign`: the sum of the points. -/
theorem add (P Q : EdwardsPoint) (hP : P.OnCurve) (hP' : P.IsBounded) (hQ : Q.OnCurve)
    (hQ' : Q.IsBounded) :
    ∀ add ∈ [«&P + &Q», «P + &Q», «&P + Q», «P + Q», «P += &Q», «P += Q»],
      add P Q ⦃ (r : EdwardsPoint) =>
        r.OnCurve ∧ r.toPoint = P.toPoint + Q.toPoint ∧ r.IsBounded ⦄ := by
  open «Shared0EdwardsPointx86_64-tables».Insts in
  variants [«CoreOpsArithAddSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».add_spec]

/-- `Sub` and `SubAssign`: the difference of the points. -/
theorem sub (P Q : EdwardsPoint) (hP : P.OnCurve) (hP' : P.IsBounded) (hQ : Q.OnCurve)
    (hQ' : Q.IsBounded) :
    ∀ sub ∈ [«&P - &Q», «P - &Q», «&P - Q», «P - Q», «P -= &Q», «P -= Q»],
      sub P Q ⦃ (r : EdwardsPoint) =>
        r.OnCurve ∧ r.toPoint = P.toPoint - Q.toPoint ∧ r.IsBounded ⦄ := by
  open «Shared0EdwardsPointx86_64-tables».Insts in
  variants [«CoreOpsArithSubSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».sub_spec]

/-- `Sum`: the sum of the points the iterator yields (through `borrow`). -/
theorem sum {T I : Type} (borrowInst : core.borrow.Borrow T EdwardsPoint)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (Ps : List EdwardsPoint) (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint) => P' = P ⦄) xs Ps)
    (hPs : ∀ P ∈ Ps, P.OnCurve) (hPs' : ∀ P ∈ Ps, P.IsBounded) :
    edwards.EdwardsPoint.«x86_64-tables».Insts.CoreIterTraitsAccumSum.sum borrowInst iterInst iter
      ⦃ (r : EdwardsPoint) => r.OnCurve ∧ r.toPoint = (Ps.map (·.toPoint)).sum ∧ r.IsBounded ⦄ :=
  edwards.EdwardsPoint.«x86_64-tables».Insts.CoreIterTraitsAccumSum.sum_spec borrowInst iterInst
    iter xs Ps hiter hborrow hPs' hPs

/-- `Neg`: the negation of the point. -/
theorem neg (P : EdwardsPoint) (hP : P.OnCurve) (hP' : P.IsBounded) :
    ∀ neg ∈ [«-&P», «-P»],
      neg P ⦃ (r : EdwardsPoint) => r.OnCurve ∧ r.toPoint = -P.toPoint ∧ r.IsBounded ⦄ := by
  open «Shared0EdwardsPointx86_64-tables».Insts in
  variants [«CoreOpsArithNegEdwardsPointx86_64-tables».neg_spec]

/-- `Mul<Scalar>` and `MulAssign<Scalar>`: `s • P`. -/
theorem mul (P : EdwardsPoint) (s : Scalar) (hP : P.OnCurve) (hP' : P.IsBounded)
    (hs : s.asNat < 2 ^ 255) :
    ∀ mul ∈ [«&P * &s», «P * &s», «&P * s», «P * s», «P *= &s», «P *= s»],
      mul P s ⦃ (r : EdwardsPoint) =>
        r.OnCurve ∧ r.toPoint = s.asNat • P.toPoint ∧ r.IsBounded ⦄ := by
  open «Shared0EdwardsPointx86_64-tables».Insts in
  variants [«CoreOpsArithMulSharedAScalarEdwardsPointx86_64-tables».mul_spec]

/-- `Mul<EdwardsPoint> for Scalar`: `s • P`. -/
theorem mul_left (s : Scalar) (P : EdwardsPoint) (hs : s.asNat < 2 ^ 255) (hP : P.OnCurve)
    (hP' : P.IsBounded) :
    ∀ mul ∈ [«&s * &P», «s * &P», «&s * P», «s * P»],
      mul s P ⦃ (r : EdwardsPoint) =>
        r.OnCurve ∧ r.toPoint = s.asNat • P.toPoint ∧ r.IsBounded ⦄ := by
  open Shared0Scalar.Insts in
  variants [«CoreOpsArithMulSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».mul_spec]

open edwards.«EdwardsPointx86_64-tables»

/-- `mul_base`: `s • B` for the basepoint `B`. -/
theorem mul_base (s : Scalar) (hs : s.asNat < 2 ^ 255) :
    mul_base s ⦃ (r : EdwardsPoint) =>
      r.OnCurve ∧ r.toPoint = s.asNat • basepoint ∧ r.IsBounded ⦄ :=
  mul_base_spec s hs

/-- `mul_clamped`: `clamp bytes • P`, with RFC 7748's clamping of the little-endian value of
`bytes`. -/
theorem mul_clamped (P : EdwardsPoint) (bytes : Array U8 32#usize) (hP : P.OnCurve)
    (hP' : P.IsBounded) :
    mul_clamped P bytes ⦃ (r : EdwardsPoint) =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • P.toPoint ∧ r.IsBounded ⦄ :=
  mul_clamped_spec P bytes hP' hP

/-- `mul_base_clamped`: `clamp bytes • B`, with RFC 7748's clamping of the little-endian value of
`bytes`. -/
theorem mul_base_clamped (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (r : EdwardsPoint) =>
      r.OnCurve ∧ r.toPoint = decodeScalar25519 bytes.toVector • basepoint ∧ r.IsBounded ⦄ :=
  mul_base_clamped_spec bytes

end EdwardsPoint

/-! ### Multiscalar multiplication -/

namespace EdwardsPoint

open edwards.EdwardsPoint.«x86_64-tables».Insts

/-- `MultiscalarMul::multiscalar_mul`: `∑ s_i • P_i` over the scalars and points the two inputs
yield, which must be equally many (the patched `assert_eq!`). -/
theorem multiscalar_mul
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item EdwardsPoint)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List Scalar) (Ps : List EdwardsPoint)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y ⦃ (P' : EdwardsPoint) => P' = P ⦄) ys Ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hPs : ∀ P ∈ Ps, P.OnCurve)
    (hPs' : ∀ P ∈ Ps, P.IsBounded) (hxs : xs.length ≤ Usize.max) (hlen : xs.length = ys.length) :
    «Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-tables».multiscalar_mul
      scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : EdwardsPoint) => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss Ps).sum ∧ r.IsBounded ⦄ := by
  apply «Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-tables».multiscalar_mul_spec <;>
    assumption

/-- `VartimeMultiscalarMul::optional_multiscalar_mul`: `none` iff some point is `none`; otherwise
`∑ s_i • P_i` over the scalars and points, which must be equally many (the patched `assert_eq!`;
Straus below `190` points, Pippenger from `190` on). -/
theorem optional_multiscalar_mul {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J (Option EdwardsPoint) Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ops : List (Option EdwardsPoint))
    (ss : List Scalar) (hscalars : scalarsInst.Yields scalars xs)
    (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hPs : ∀ P, some P ∈ ops → P.OnCurve)
    (hPs' : ∀ P, some P ∈ ops → P.IsBounded) (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables».optional_multiscalar_mul
      scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option EdwardsPoint) => (none ∈ ops → r = none) ∧
        ∀ Ps, ops = Ps.map some → ∃ R, r = some R ∧ R.OnCurve ∧
          R.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss Ps).sum ∧
          R.IsBounded ⦄ := by
  open «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables» in
  apply optional_multiscalar_mul_spec <;> assumption

end EdwardsPoint

namespace VartimeEdwardsPrecomputation

open edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts
open «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimePrecomputedMultiscalarMul::new`: a precomputation of the points the input yields
(through `borrow`). -/
theorem new {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item EdwardsPoint)
    (static_points : I) (ys : List Clause0_Item) (Ps : List EdwardsPoint)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : EdwardsPoint) => P' = P ⦄) ys Ps)
    (hPs : ∀ P ∈ Ps, P.OnCurve) (hPs' : ∀ P ∈ Ps, P.IsBounded) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points ⦃ (r : VartimeEdwardsPrecomputation) =>
      r.IsValid ∧ r.points = Ps.map (·.toPoint) ∧ r.IsBounded ⦄ := by
  apply new_spec <;> assumption

/-- `VartimePrecomputedMultiscalarMul::len`: the number of static points. -/
theorem len (pre : VartimeEdwardsPrecomputation) :
    len pre ⦃ (r : Usize) => r.val = pre.points.length ⦄ :=
  len_spec pre

/-- `VartimePrecomputedMultiscalarMul::is_empty`: whether there are no static points. -/
theorem is_empty (pre : VartimeEdwardsPrecomputation) :
    is_empty pre ⦃ (r : Bool) => r = true ↔ pre.points = [] ⦄ :=
  is_empty_spec pre

/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` (static points
`pre.points`): `none` iff some dynamic point is `none`; otherwise `∑ s_i • P_i + ∑ d_i • Q_i`,
missing static scalars counting as `0` (if no point is `none`, at most `|pre.points|` static
scalars and as many dynamic scalars as dynamic points). -/
theorem optional_mixed_multiscalar_mul
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K (Option EdwardsPoint)
      Clause4_IntoIter)
    (pre : VartimeEdwardsPrecomputation)
    (static_scalars : I) (dynamic_scalars : J) (dynamic_points : K) (xs : List Clause0_Item)
    (ss : List Scalar) (ys : List Clause2_Item) (ds : List Scalar)
    (qops : List (Option EdwardsPoint))
    (hpre : pre.IsValid) (hpre' : pre.IsBounded)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hQs : ∀ Q, some Q ∈ qops → Q.OnCurve) (hQs' : ∀ Q, some Q ∈ qops → Q.IsBounded)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ pre.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst pre static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option EdwardsPoint) => (none ∈ qops → r = none) ∧
        ∀ Qs, qops = Qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧
          R.toPoint = (List.zipWith (fun s P => s.asNat • P) ss pre.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds Qs).sum ∧
          R.IsBounded ⦄ := by
  apply optional_mixed_multiscalar_mul_spec <;> assumption

end VartimeEdwardsPrecomputation

namespace EdwardsPoint

open edwards.«EdwardsPointx86_64-tables»

/-- `vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`. -/
theorem vartime_double_scalar_mul_basepoint (a : Scalar) (A : EdwardsPoint) (b : Scalar)
    (ha : a.asNat < 2 ^ 255) (hA : A.OnCurve) (hA' : A.IsBounded) (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : EdwardsPoint) =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.IsBounded ⦄ :=
  vartime_double_scalar_mul_basepoint_spec a A b ha hA' hA hb

/-- `vartime_triple_scalar_mul_basepoint`: `a1 • A1 + a2 • A2 + b • B` for the basepoint `B` (any
`b`, which the code splits into two `128`-bit halves). -/
theorem vartime_triple_scalar_mul_basepoint (a1 : HalfWidthScalar) (A1 : EdwardsPoint)
    (a2 : HalfWidthScalar) (A2 : EdwardsPoint) (b : Scalar) (ha1 : a1.asNat < 2 ^ 128)
    (hA1 : A1.OnCurve) (hA1' : A1.IsBounded) (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.OnCurve)
    (hA2' : A2.IsBounded) :
    vartime_triple_scalar_mul_basepoint a1 A1 a2 A2 b ⦃ (r : EdwardsPoint) =>
      r.OnCurve ∧ r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.IsBounded ⦄ :=
  vartime_triple_scalar_mul_basepoint_spec a1 A1 a2 A2 b ha1 hA1' hA1 ha2 hA2' hA2

end EdwardsPoint

-- BEGIN TABLES-ONLY
/-! ### Basepoint tables

The five table types, of radix `2^4` to `2^8`, have the same specs: a table `t` of radix `2^w`
represents the point `t.point`, with entry `j` of row `i` equal to `(j + 1) • 2^(2 w i) • t.point`
(`IsTable`). -/

/-- `EdwardsBasepointTable` (radix `2^4`) in this configuration. -/
abbrev EdwardsBasepointTable := edwards.EdwardsBasepointTable.«x86_64-tables»

/-- `EdwardsBasepointTableRadix32` (radix `2^5`) in this configuration. -/
abbrev EdwardsBasepointTableRadix32 := edwards.EdwardsBasepointTableRadix32.«x86_64-tables»

/-- `EdwardsBasepointTableRadix64` (radix `2^6`) in this configuration. -/
abbrev EdwardsBasepointTableRadix64 := edwards.EdwardsBasepointTableRadix64.«x86_64-tables»

/-- `EdwardsBasepointTableRadix128` (radix `2^7`) in this configuration. -/
abbrev EdwardsBasepointTableRadix128 := edwards.EdwardsBasepointTableRadix128.«x86_64-tables»

/-- `EdwardsBasepointTableRadix256` (radix `2^8`) in this configuration. -/
abbrev EdwardsBasepointTableRadix256 := edwards.EdwardsBasepointTableRadix256.«x86_64-tables»

namespace EdwardsBasepointTable

open edwards.EdwardsBasepointTable.«x86_64-tables».Insts
open «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `impl Mul<&Scalar> for &EdwardsBasepointTable` -/
abbrev «&t * &s» := open «SharedAEdwardsBasepointTablex86_64-tables».Insts in
  «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables».mul
/-- `impl Mul<&EdwardsBasepointTable> for &Scalar` -/
abbrev «&s * &t» := open SharedBScalar.Insts in
  «CoreOpsArithMulSharedAEdwardsBasepointTablex86_64-tablesEdwardsPointx86_64-tables».mul

/-- `BasepointTable::create`: a table of `B`. -/
theorem create (B : EdwardsPoint) (hB : B.OnCurve) (hB' : B.IsBounded) :
    create B ⦃ (t : EdwardsBasepointTable) => t.IsTable ∧ t.point = B.toPoint ∧ t.IsBounded ⦄ := by
  apply create_spec <;> assumption

/-- `BasepointTable::basepoint`: the table's point. -/
theorem basepoint (t : EdwardsBasepointTable) (ht : t.IsTable) (ht' : t.IsBounded) :
    basepoint t ⦃ (r : EdwardsPoint) => r.OnCurve ∧ r.toPoint = t.point ∧ r.IsBounded ⦄ := by
  apply basepoint_spec <;> assumption

/-- `BasepointTable::mul_base`, `Mul<&Scalar> for &EdwardsBasepointTable`
and its reverse: `s • t.point`. -/
theorem mul_base (t : EdwardsBasepointTable) (s : Scalar) (ht : t.IsTable)
    (ht' : t.IsBounded) (hs : s.asNat < 2 ^ 255) :
    ∀ ts ∈ [mul_base t s, «&t * &s» t s, «&s * &t» s t],
      ts ⦃ (r : EdwardsPoint) => r.OnCurve ∧ r.toPoint = s.asNat • t.point ∧ r.IsBounded ⦄ := by
  variants [mul_base_spec]

open edwards.EdwardsBasepointTable.«x86_64-tables».Insts in
/-- `From<&T> for EdwardsBasepointTable`, for the other four table types `T`: a table
of the same point. -/
theorem «from» :
    (∀ t : EdwardsBasepointTableRadix32, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTable) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) ∧
    (∀ t : EdwardsBasepointTableRadix64, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTable) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) ∧
    (∀ t : EdwardsBasepointTableRadix128, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTable) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) ∧
    (∀ t : EdwardsBasepointTableRadix256, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTable) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) :=
  ⟨fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables».from_spec t ht' ht,
    fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables».from_spec t ht' ht,
    fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables».from_spec t ht' ht,
    fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables».from_spec t ht' ht⟩

end EdwardsBasepointTable

namespace EdwardsBasepointTableRadix32

open edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts
open «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `impl Mul<&Scalar> for &EdwardsBasepointTableRadix32` -/
abbrev «&t * &s» := open «SharedAEdwardsBasepointTableRadix32x86_64-tables».Insts in
  «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables».mul
/-- `impl Mul<&EdwardsBasepointTableRadix32> for &Scalar` -/
abbrev «&s * &t» := open SharedBScalar.Insts in
  «CoreOpsArithMulSharedAEdwardsBasepointTableRadix32x86_64-tablesEdwardsPointx86_64-tables».mul

/-- `BasepointTable::create`: a table of `B`. -/
theorem create (B : EdwardsPoint) (hB : B.OnCurve) (hB' : B.IsBounded) :
    create B ⦃ (t : EdwardsBasepointTableRadix32) =>
      t.IsTable ∧ t.point = B.toPoint ∧ t.IsBounded ⦄ := by
  apply create_spec <;> assumption

/-- `BasepointTable::basepoint`: the table's point. -/
theorem basepoint (t : EdwardsBasepointTableRadix32) (ht : t.IsTable) (ht' : t.IsBounded) :
    basepoint t ⦃ (r : EdwardsPoint) => r.OnCurve ∧ r.toPoint = t.point ∧ r.IsBounded ⦄ := by
  apply basepoint_spec <;> assumption

/-- `BasepointTable::mul_base`, `Mul<&Scalar> for &EdwardsBasepointTableRadix32`
and its reverse: `s • t.point`. -/
theorem mul_base (t : EdwardsBasepointTableRadix32) (s : Scalar) (ht : t.IsTable)
    (ht' : t.IsBounded) (hs : s.asNat < 2 ^ 255) :
    ∀ ts ∈ [mul_base t s, «&t * &s» t s, «&s * &t» s t],
      ts ⦃ (r : EdwardsPoint) => r.OnCurve ∧ r.toPoint = s.asNat • t.point ∧ r.IsBounded ⦄ := by
  variants [mul_base_spec]

open edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts in
/-- `From<&T> for EdwardsBasepointTableRadix32`, for the other four table types `T`: a table
of the same point. -/
theorem «from» :
    (∀ t : EdwardsBasepointTable, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTableRadix32) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) ∧
    (∀ t : EdwardsBasepointTableRadix64, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTableRadix32) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) ∧
    (∀ t : EdwardsBasepointTableRadix128, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTableRadix32) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) ∧
    (∀ t : EdwardsBasepointTableRadix256, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTableRadix32) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) :=
  ⟨fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables».from_spec t ht' ht,
    fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables».from_spec t ht' ht,
    fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables».from_spec t ht' ht,
    fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables».from_spec t ht' ht⟩

end EdwardsBasepointTableRadix32

namespace EdwardsBasepointTableRadix64

open edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts
open «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `impl Mul<&Scalar> for &EdwardsBasepointTableRadix64` -/
abbrev «&t * &s» := open «SharedAEdwardsBasepointTableRadix64x86_64-tables».Insts in
  «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables».mul
/-- `impl Mul<&EdwardsBasepointTableRadix64> for &Scalar` -/
abbrev «&s * &t» := open SharedBScalar.Insts in
  «CoreOpsArithMulSharedAEdwardsBasepointTableRadix64x86_64-tablesEdwardsPointx86_64-tables».mul

/-- `BasepointTable::create`: a table of `B`. -/
theorem create (B : EdwardsPoint) (hB : B.OnCurve) (hB' : B.IsBounded) :
    create B ⦃ (t : EdwardsBasepointTableRadix64) =>
      t.IsTable ∧ t.point = B.toPoint ∧ t.IsBounded ⦄ := by
  apply create_spec <;> assumption

/-- `BasepointTable::basepoint`: the table's point. -/
theorem basepoint (t : EdwardsBasepointTableRadix64) (ht : t.IsTable) (ht' : t.IsBounded) :
    basepoint t ⦃ (r : EdwardsPoint) => r.OnCurve ∧ r.toPoint = t.point ∧ r.IsBounded ⦄ := by
  apply basepoint_spec <;> assumption

/-- `BasepointTable::mul_base`, `Mul<&Scalar> for &EdwardsBasepointTableRadix64`
and its reverse: `s • t.point`. -/
theorem mul_base (t : EdwardsBasepointTableRadix64) (s : Scalar) (ht : t.IsTable)
    (ht' : t.IsBounded) (hs : s.asNat < 2 ^ 255) :
    ∀ ts ∈ [mul_base t s, «&t * &s» t s, «&s * &t» s t],
      ts ⦃ (r : EdwardsPoint) => r.OnCurve ∧ r.toPoint = s.asNat • t.point ∧ r.IsBounded ⦄ := by
  variants [mul_base_spec]

open edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts in
/-- `From<&T> for EdwardsBasepointTableRadix64`, for the other four table types `T`: a table
of the same point. -/
theorem «from» :
    (∀ t : EdwardsBasepointTable, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTableRadix64) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) ∧
    (∀ t : EdwardsBasepointTableRadix32, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTableRadix64) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) ∧
    (∀ t : EdwardsBasepointTableRadix128, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTableRadix64) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) ∧
    (∀ t : EdwardsBasepointTableRadix256, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTableRadix64) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) :=
  ⟨fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables».from_spec t ht' ht,
    fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables».from_spec t ht' ht,
    fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables».from_spec t ht' ht,
    fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables».from_spec t ht' ht⟩

end EdwardsBasepointTableRadix64

namespace EdwardsBasepointTableRadix128

open edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts
open «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `impl Mul<&Scalar> for &EdwardsBasepointTableRadix128` -/
abbrev «&t * &s» := open «SharedAEdwardsBasepointTableRadix128x86_64-tables».Insts in
  «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables».mul
/-- `impl Mul<&EdwardsBasepointTableRadix128> for &Scalar` -/
abbrev «&s * &t» := open SharedBScalar.Insts in
  «CoreOpsArithMulSharedAEdwardsBasepointTableRadix128x86_64-tablesEdwardsPointx86_64-tables».mul

/-- `BasepointTable::create`: a table of `B`. -/
theorem create (B : EdwardsPoint) (hB : B.OnCurve) (hB' : B.IsBounded) :
    create B ⦃ (t : EdwardsBasepointTableRadix128) =>
      t.IsTable ∧ t.point = B.toPoint ∧ t.IsBounded ⦄ := by
  apply create_spec <;> assumption

/-- `BasepointTable::basepoint`: the table's point. -/
theorem basepoint (t : EdwardsBasepointTableRadix128) (ht : t.IsTable) (ht' : t.IsBounded) :
    basepoint t ⦃ (r : EdwardsPoint) => r.OnCurve ∧ r.toPoint = t.point ∧ r.IsBounded ⦄ := by
  apply basepoint_spec <;> assumption

/-- `BasepointTable::mul_base`, `Mul<&Scalar> for &EdwardsBasepointTableRadix128`
and its reverse: `s • t.point`. -/
theorem mul_base (t : EdwardsBasepointTableRadix128) (s : Scalar) (ht : t.IsTable)
    (ht' : t.IsBounded) (hs : s.asNat < 2 ^ 255) :
    ∀ ts ∈ [mul_base t s, «&t * &s» t s, «&s * &t» s t],
      ts ⦃ (r : EdwardsPoint) => r.OnCurve ∧ r.toPoint = s.asNat • t.point ∧ r.IsBounded ⦄ := by
  variants [mul_base_spec]

open edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts in
/-- `From<&T> for EdwardsBasepointTableRadix128`, for the other four table types `T`: a table
of the same point. -/
theorem «from» :
    (∀ t : EdwardsBasepointTable, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTableRadix128) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) ∧
    (∀ t : EdwardsBasepointTableRadix32, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTableRadix128) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) ∧
    (∀ t : EdwardsBasepointTableRadix64, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTableRadix128) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) ∧
    (∀ t : EdwardsBasepointTableRadix256, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTableRadix128) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) :=
  ⟨fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables».from_spec t ht' ht,
    fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables».from_spec t ht' ht,
    fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables».from_spec t ht' ht,
    fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables».from_spec t ht' ht⟩

end EdwardsBasepointTableRadix128

namespace EdwardsBasepointTableRadix256

open edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts
open «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- `impl Mul<&Scalar> for &EdwardsBasepointTableRadix256` -/
abbrev «&t * &s» := open «SharedAEdwardsBasepointTableRadix256x86_64-tables».Insts in
  «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables».mul
/-- `impl Mul<&EdwardsBasepointTableRadix256> for &Scalar` -/
abbrev «&s * &t» := open SharedBScalar.Insts in
  «CoreOpsArithMulSharedAEdwardsBasepointTableRadix256x86_64-tablesEdwardsPointx86_64-tables».mul

/-- `BasepointTable::create`: a table of `B`. -/
theorem create (B : EdwardsPoint) (hB : B.OnCurve) (hB' : B.IsBounded) :
    create B ⦃ (t : EdwardsBasepointTableRadix256) =>
      t.IsTable ∧ t.point = B.toPoint ∧ t.IsBounded ⦄ := by
  apply create_spec <;> assumption

/-- `BasepointTable::basepoint`: the table's point. -/
theorem basepoint (t : EdwardsBasepointTableRadix256) (ht : t.IsTable) (ht' : t.IsBounded) :
    basepoint t ⦃ (r : EdwardsPoint) => r.OnCurve ∧ r.toPoint = t.point ∧ r.IsBounded ⦄ := by
  apply basepoint_spec <;> assumption

/-- `BasepointTable::mul_base`, `Mul<&Scalar> for &EdwardsBasepointTableRadix256`
and its reverse: `s • t.point`. -/
theorem mul_base (t : EdwardsBasepointTableRadix256) (s : Scalar) (ht : t.IsTable)
    (ht' : t.IsBounded) (hs : s.asNat < 2 ^ 255) :
    ∀ ts ∈ [mul_base t s, «&t * &s» t s, «&s * &t» s t],
      ts ⦃ (r : EdwardsPoint) => r.OnCurve ∧ r.toPoint = s.asNat • t.point ∧ r.IsBounded ⦄ := by
  variants [mul_base_spec]

open edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts in
/-- `From<&T> for EdwardsBasepointTableRadix256`, for the other four table types `T`: a table
of the same point. -/
theorem «from» :
    (∀ t : EdwardsBasepointTable, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTableRadix256) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) ∧
    (∀ t : EdwardsBasepointTableRadix32, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTableRadix256) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) ∧
    (∀ t : EdwardsBasepointTableRadix64, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTableRadix256) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) ∧
    (∀ t : EdwardsBasepointTableRadix128, t.IsTable → t.IsBounded →
      «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables».«from» t
        ⦃ (r : EdwardsBasepointTableRadix256) => r.IsTable ∧ r.point = t.point ∧ r.IsBounded ⦄) :=
  ⟨fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables».from_spec t ht' ht,
    fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables».from_spec t ht' ht,
    fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables».from_spec t ht' ht,
    fun t ht ht' =>
      «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables».from_spec t ht' ht⟩

end EdwardsBasepointTableRadix256

-- END TABLES-ONLY


namespace EdwardsPoint

open edwards.«EdwardsPointx86_64-tables»

/-- `mul_by_cofactor`: `8 • P`. -/
theorem mul_by_cofactor (P : EdwardsPoint) (hP : P.OnCurve) (hP' : P.IsBounded) :
    mul_by_cofactor P ⦃ (r : EdwardsPoint) =>
      r.OnCurve ∧ r.toPoint = 8 • P.toPoint ∧ r.IsBounded ⦄ :=
  mul_by_cofactor_spec P hP' hP

/-- `is_small_order`: whether `8 • P = 0`. -/
theorem is_small_order (P : EdwardsPoint) (hP : P.OnCurve) (hP' : P.IsBounded) :
    is_small_order P ⦃ (r : Bool) => r = true ↔ 8 • P.toPoint = 0 ⦄ :=
  is_small_order_spec P hP' hP

/-- `is_torsion_free`: whether `L • P = 0` (multiplication by the unreduced `BASEPOINT_ORDER`). -/
theorem is_torsion_free (P : EdwardsPoint) (hP : P.OnCurve) (hP' : P.IsBounded) :
    is_torsion_free P ⦃ (r : Bool) => r = true ↔ L • P.toPoint = 0 ⦄ :=
  is_torsion_free_spec P hP' hP

end EdwardsPoint

end Theorems.edwards.«x86_64-tables»
-- END PER-CONFIG
