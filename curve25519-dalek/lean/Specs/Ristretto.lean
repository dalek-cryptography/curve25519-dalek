/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519.Ristretto.Encoding
public import Curve25519.Ristretto.Map
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import ToAeneas.Iterator
public import Defs.Ristretto
public import Defs.Scalar
public import Defs.ScalarMul
public import Subtle
import Proofs
import Zeroize.Instances
public section

/-! # Specs of `src/ristretto.rs` and `src/ristretto/elligator.rs`

The public items of `ristretto.rs` and its submodule `elligator.rs`, in their order.

A `RistrettoPoint` is an `EdwardsPoint` (`Defs/Ristretto.lean`): the statements are about the
represented Edwards point, which stands for an element of ristretto255 when it is even (Mathlib's
`Even`). The functions that create points (`decompress`, `from_uniform_bytes`, `map_to_curve`,
`identity`, `default`, `mul_base`, `RISTRETTO_BASEPOINT_POINT`) state that the point is even. Group
operations are stated exactly on representatives (as for `EdwardsPoint`), so they keep points even
and also hold for the elements; `ct_eq`/`eq` decide `curve25519.edwards.Rel` (equality in the
Ristretto group); `compress` is RFC 9496's encoding `Ristretto.encodeRep` of the represented point
(for any representative; on even points it is constant exactly on the classes of `Rel`,
`Ristretto.encodeRepNat_eq_iff`); `decompress` is RFC 9496's decoding `Ristretto.decodeRep`;
`from_uniform_bytes` is RFC 9496's one-way map `Ristretto.fromUniformRep` on 64 bytes, and
`map_to_curve` its `MAP` on 32 bytes (`Ristretto.mapRep`: the low 255 bits modulo `p`). Scalars are
unreduced and must be `< 2^255` (invariant #1 of `Scalar` in `scalar.rs`). The multiscalar
statements are about the patched code
(`translation-patches/ristretto-{multiscalar,optional_multiscalar}_mul.patch` on top of the
`EdwardsPoint` ones), which requires as many scalars as points; the original panics unless both
inputs' `size_hint`s are exact and equal.

`CompressedRistretto` does not depend on the configuration, except `decompress`. Everything else is
stated after it, for `x86_64-tables`; the other configurations' copies are generated in
`Specs/Ristretto/`, without `RistrettoBasepointTable` for the configurations without precomputed
tables.

Definitions used: `EdwardsPoint.toPoint`, `OnCurve`, `IsBounded`, the tables' `point`, `IsTable` and
`IsBounded`, the precomputations' `points`, `IsValid` and `IsBounded` (`Defs/Edwards.lean`,
`Defs/ScalarMul.lean`), `Array.toVector` (`ToAeneas/Array.lean`), `Scalar.asNat`
(`Defs/Scalar.lean`), `Iterator.Yields` (`ToAeneas/Iterator.lean`), Mathlib's `Even`,
`curve25519.edwards.Rel`, `Ristretto.encodeRep`, `Ristretto.decodeRep`, `Ristretto.mapRep`,
`Ristretto.fromUniformRep` (`Curve25519/Ristretto/`), `curve25519.basepoint` (`Curve25519/`),
`subtle.Choice.IsValid` (`Subtle/`).

Not specified: derived `Clone`/`Copy` impls. Not translated: `Debug`, `Hash`, `random`,
`try_random`, `hash_from_bytes`, `from_hash`, the `group` and `serde` impls.
`elligator_ristretto_flavor` (`pub(crate)`) and the private `coset4` are specified in their proof
files. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 Curve25519Dalek
open Curve25519Dalek.ristretto (CompressedRistretto)
open Curve25519Dalek.scalar (Scalar)

namespace Specs.ristretto.CompressedRistretto

/-- `PartialEq`: byte equality. -/
theorem eq (a b : CompressedRistretto) :
    CompressedRistretto.Insts.CoreCmpPartialEqCompressedRistretto.eq a b ⦃ (r : Bool) =>
      r = true ↔ a = b ⦄ :=
  CompressedRistretto.Insts.CoreCmpPartialEqCompressedRistretto.eq_spec a b

/-- `ConstantTimeEq`: byte equality. -/
theorem ct_eq (a b : CompressedRistretto) :
    CompressedRistretto.Insts.SubtleConstantTimeEq.ct_eq a b ⦃ (r : subtle.Choice) =>
      r.IsValid ∧ (r = 1#u8 ↔ a = b) ⦄ :=
  CompressedRistretto.Insts.SubtleConstantTimeEq.ct_eq_spec a b

/-- `to_bytes`: the bytes. -/
theorem to_bytes (c : CompressedRistretto) :
    CompressedRistretto.to_bytes c ⦃ (r : Array U8 32#usize) => r = c ⦄ :=
  CompressedRistretto.to_bytes_spec c

/-- `as_bytes`: the bytes. -/
theorem as_bytes (c : CompressedRistretto) :
    CompressedRistretto.as_bytes c ⦃ (r : Array U8 32#usize) => r = c ⦄ :=
  CompressedRistretto.as_bytes_spec c

/-- `from_slice`: the bytes of a slice of length `32`, an error otherwise. -/
theorem from_slice (bytes : Slice U8) :
    CompressedRistretto.from_slice bytes
      ⦃ (r : core.result.Result CompressedRistretto core.array.TryFromSliceError) =>
        match r with
        | .Ok c => bytes.length = 32 ∧ ∀ i < 32, c[i]! = bytes[i]!
        | .Err _ => bytes.length ≠ 32 ⦄ :=
  CompressedRistretto.from_slice_spec bytes

/-- `Identity`: the encoding of the neutral element. -/
theorem identity :
    CompressedRistretto.Insts.Curve25519_dalekTraitsIdentity.identity
      ⦃ (r : CompressedRistretto) => r.toVector = Ristretto.encodeRep 0 ⦄ :=
  CompressedRistretto.Insts.Curve25519_dalekTraitsIdentity.identity_spec

/-- `Default`: the encoding of the neutral element. -/
theorem default :
    CompressedRistretto.Insts.CoreDefaultDefault.default ⦃ (r : CompressedRistretto) =>
      r.toVector = Ristretto.encodeRep 0 ⦄ :=
  CompressedRistretto.Insts.CoreDefaultDefault.default_spec

/-- `TryFrom<&[u8]>`: as `from_slice`. -/
theorem try_from (slice : Slice U8) :
    CompressedRistretto.Insts.CoreConvertTryFromShared0SliceU8TryFromSliceError.try_from slice
      ⦃ (r : core.result.Result CompressedRistretto core.array.TryFromSliceError) =>
        match r with
        | .Ok c => slice.length = 32 ∧ ∀ i < 32, c[i]! = slice[i]!
        | .Err _ => slice.length ≠ 32 ⦄ :=
  CompressedRistretto.Insts.CoreConvertTryFromShared0SliceU8TryFromSliceError.try_from_spec slice

/-- `Zeroize`: thirty-two zero bytes, the encoding of the neutral element. -/
theorem zeroize (c : CompressedRistretto) :
    CompressedRistretto.Insts.ZeroizeZeroize.zeroize c ⦃ (r : CompressedRistretto) =>
      r.toVector = Ristretto.encodeRep 0 ⦄ :=
  CompressedRistretto.Insts.ZeroizeZeroize.zeroize_spec c

end Specs.ristretto.CompressedRistretto

/-! ## Per configuration -/

-- BEGIN PER-CONFIG
namespace Specs.ristretto.«x86_64-tables»

/-- `RistrettoPoint` in this configuration. -/
abbrev RistrettoPoint := ristretto.RistrettoPoint.«x86_64-tables»

/-- `VartimeRistrettoPrecomputation` in this configuration. -/
abbrev VartimeRistrettoPrecomputation := ristretto.VartimeRistrettoPrecomputation.«x86_64-tables»

/-- `CompressedRistretto::decompress`: RFC 9496's decoding `decodeRep` of the bytes, `none` exactly
when they are not a valid ristretto255 encoding; the point is even (a ristretto255
representative). -/
theorem CompressedRistretto.decompress (c : CompressedRistretto) :
    CompressedRistretto.decompress.«x86_64-tables» c ⦃ (r : Option RistrettoPoint) =>
      r.map (·.toPoint) = Ristretto.decodeRep c.toVector ∧
      ∀ P, r = some P → P.OnCurve ∧ Even P.toPoint ∧ P.IsBounded ⦄ :=
  ristretto.CompressedRistretto.«x86_64-tables».decompress_spec c

namespace RistrettoPoint

open ristretto.«RistrettoPointx86_64-tables»

/-- `compress`: RFC 9496's encoding of the represented point. -/
theorem compress (P : RistrettoPoint) (hP : P.OnCurve) (hP' : P.IsBounded) :
    compress P ⦃ (r : CompressedRistretto) => r.toVector = Ristretto.encodeRep P.toPoint ⦄ :=
  compress_spec P hP' hP

/-- `double_and_compress_batch`: entry `i` is RFC 9496's encoding of `2 P_i` for the points `P_i`
the input yields. -/
theorem double_and_compress_batch {I Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I RistrettoPoint Clause0_IntoIter)
    (points : I) (Ps : List RistrettoPoint) (hpoints : pointsInst.Yields points Ps)
    (hPs : ∀ P ∈ Ps, P.OnCurve) (hPs' : ∀ P ∈ Ps, P.IsBounded) (hlen : Ps.length ≤ Usize.max) :
    double_and_compress_batch pointsInst points ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = Ps.length ∧
        ∀ i < Ps.length, r[i]!.toVector = Ristretto.encodeRep (2 • Ps[i]!.toPoint) ⦄ := by
  apply double_and_compress_batch_spec <;> assumption

/-- `from_uniform_bytes`: RFC 9496's one-way map of the 64 bytes' little-endian value,
`MAP(r₀) + MAP(r₁)` for the two halves: an even point (a ristretto255 representative). -/
theorem from_uniform_bytes (bytes : Array U8 64#usize) :
    from_uniform_bytes bytes ⦃ (r : RistrettoPoint) =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.fromUniformRep bytes.toVector ∧
        r.IsBounded ⦄ :=
  from_uniform_bytes_spec bytes

end RistrettoPoint

namespace RistrettoPoint

open ristretto.RistrettoPoint.«x86_64-tables».Insts

/-- `Identity`: the neutral element. -/
theorem identity :
    Curve25519_dalekTraitsIdentity.identity ⦃ (r : RistrettoPoint) =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.IsBounded ⦄ :=
  Curve25519_dalekTraitsIdentity.identity_spec

/-- `Default`: the neutral element. -/
theorem default :
    CoreDefaultDefault.default ⦃ (r : RistrettoPoint) =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.IsBounded ⦄ :=
  CoreDefaultDefault.default_spec

/-- `PartialEq`: equality in the Ristretto group. -/
theorem eq (P Q : RistrettoPoint) (hP : P.OnCurve) (hP' : P.IsBounded) (hQ : Q.OnCurve)
    (hQ' : Q.IsBounded) :
    «CoreCmpPartialEqRistrettoPointx86_64-tables».eq P Q ⦃ (r : Bool) =>
      r = true ↔ edwards.Rel P.toPoint Q.toPoint ⦄ :=
  «CoreCmpPartialEqRistrettoPointx86_64-tables».eq_spec P Q hP' hQ' hP hQ

/-- `ConstantTimeEq`: equality in the Ristretto group, i.e. of the classes of the represented
points (`X₁ Y₂ = Y₁ X₂` or `X₁ X₂ = Y₁ Y₂`). -/
theorem ct_eq (P Q : RistrettoPoint) (hP : P.OnCurve) (hP' : P.IsBounded) (hQ : Q.OnCurve)
    (hQ' : Q.IsBounded) :
    SubtleConstantTimeEq.ct_eq P Q ⦃ (r : subtle.Choice) =>
      r.IsValid ∧ (r = 1#u8 ↔ edwards.Rel P.toPoint Q.toPoint) ⦄ :=
  SubtleConstantTimeEq.ct_eq_spec P Q hP' hQ' hP hQ

end RistrettoPoint

/-! ### Arithmetic

The operator impls, named by the Rust expression they evaluate (`P`, `Q` points, `s` a scalar). -/

/-- `impl Add<&RistrettoPoint> for &RistrettoPoint` -/
abbrev «&P + &Q» := open «Shared0RistrettoPointx86_64-tables».Insts in
  «CoreOpsArithAddSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables».add
/-- `impl Add<&RistrettoPoint> for RistrettoPoint` -/
abbrev «P + &Q» := open ristretto.RistrettoPoint.«x86_64-tables».Insts in
  «CoreOpsArithAddSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables».add
/-- `impl Add<RistrettoPoint> for &RistrettoPoint` -/
abbrev «&P + Q» := open «SharedARistrettoPointx86_64-tables».Insts in
  «CoreOpsArithAddRistrettoPointx86_64-tablesRistrettoPointx86_64-tables».add
/-- `impl Add<RistrettoPoint> for RistrettoPoint` -/
abbrev «P + Q» := open ristretto.RistrettoPoint.«x86_64-tables».Insts in
  «CoreOpsArithAddRistrettoPointx86_64-tablesRistrettoPointx86_64-tables».add
/-- `impl AddAssign<&RistrettoPoint> for RistrettoPoint` -/
abbrev «P += &Q» := open ristretto.RistrettoPoint.«x86_64-tables».Insts in
  «CoreOpsArithAddAssignShared0RistrettoPointx86_64-tables».add_assign
/-- `impl AddAssign<RistrettoPoint> for RistrettoPoint` -/
abbrev «P += Q» := open ristretto.RistrettoPoint.«x86_64-tables».Insts in
  «CoreOpsArithAddAssignRistrettoPointx86_64-tables».add_assign

/-- `impl Sub<&RistrettoPoint> for &RistrettoPoint` -/
abbrev «&P - &Q» := open «Shared0RistrettoPointx86_64-tables».Insts in
  «CoreOpsArithSubSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables».sub
/-- `impl Sub<&RistrettoPoint> for RistrettoPoint` -/
abbrev «P - &Q» := open ristretto.RistrettoPoint.«x86_64-tables».Insts in
  «CoreOpsArithSubSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables».sub
/-- `impl Sub<RistrettoPoint> for &RistrettoPoint` -/
abbrev «&P - Q» := open «SharedARistrettoPointx86_64-tables».Insts in
  «CoreOpsArithSubRistrettoPointx86_64-tablesRistrettoPointx86_64-tables».sub
/-- `impl Sub<RistrettoPoint> for RistrettoPoint` -/
abbrev «P - Q» := open ristretto.RistrettoPoint.«x86_64-tables».Insts in
  «CoreOpsArithSubRistrettoPointx86_64-tablesRistrettoPointx86_64-tables».sub
/-- `impl SubAssign<&RistrettoPoint> for RistrettoPoint` -/
abbrev «P -= &Q» := open ristretto.RistrettoPoint.«x86_64-tables».Insts in
  «CoreOpsArithSubAssignShared0RistrettoPointx86_64-tables».sub_assign
/-- `impl SubAssign<RistrettoPoint> for RistrettoPoint` -/
abbrev «P -= Q» := open ristretto.RistrettoPoint.«x86_64-tables».Insts in
  «CoreOpsArithSubAssignRistrettoPointx86_64-tables».sub_assign

/-- `impl Neg for &RistrettoPoint` -/
abbrev «-&P» := open «Shared0RistrettoPointx86_64-tables».Insts in
  «CoreOpsArithNegRistrettoPointx86_64-tables».neg
/-- `impl Neg for RistrettoPoint` -/
abbrev «-P» := open ristretto.RistrettoPoint.«x86_64-tables».Insts in
  «CoreOpsArithNegRistrettoPointx86_64-tables».neg

/-- `impl Mul<&Scalar> for &RistrettoPoint` -/
abbrev «&P * &s» := open «Shared0RistrettoPointx86_64-tables».Insts in
  «CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables».mul
/-- `impl Mul<&Scalar> for RistrettoPoint` -/
abbrev «P * &s» := open ristretto.RistrettoPoint.«x86_64-tables».Insts in
  «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-tables».mul
/-- `impl Mul<Scalar> for &RistrettoPoint` -/
abbrev «&P * s» := open «SharedARistrettoPointx86_64-tables».Insts in
  «CoreOpsArithMulScalarRistrettoPointx86_64-tables».mul
/-- `impl Mul<Scalar> for RistrettoPoint` -/
abbrev «P * s» := open ristretto.RistrettoPoint.«x86_64-tables».Insts in
  «CoreOpsArithMulScalarRistrettoPointx86_64-tables».mul
/-- `impl MulAssign<&Scalar> for RistrettoPoint` -/
abbrev «P *= &s» :=
  ristretto.RistrettoPoint.«x86_64-tables».Insts.CoreOpsArithMulAssignSharedAScalar.mul_assign
/-- `impl MulAssign<Scalar> for RistrettoPoint` -/
abbrev «P *= s» :=
  ristretto.RistrettoPoint.«x86_64-tables».Insts.CoreOpsArithMulAssignScalar.mul_assign

/-- `impl Mul<&RistrettoPoint> for &Scalar` -/
abbrev «&s * &P» := open Shared0Scalar.Insts in
  «CoreOpsArithMulSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables».mul
/-- `impl Mul<&RistrettoPoint> for Scalar` -/
abbrev «s * &P» := open scalar.Scalar.Insts in
  «CoreOpsArithMulSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables».mul
/-- `impl Mul<RistrettoPoint> for &Scalar` -/
abbrev «&s * P» := open SharedAScalar.Insts in
  «CoreOpsArithMulRistrettoPointx86_64-tablesRistrettoPointx86_64-tables».mul
/-- `impl Mul<RistrettoPoint> for Scalar` -/
abbrev «s * P» := open scalar.Scalar.Insts in
  «CoreOpsArithMulRistrettoPointx86_64-tablesRistrettoPointx86_64-tables».mul

namespace RistrettoPoint

/-- `Add` and `AddAssign`: the sum of the points. -/
theorem add (P Q : RistrettoPoint) (hP : P.OnCurve) (hP' : P.IsBounded) (hQ : Q.OnCurve)
    (hQ' : Q.IsBounded) :
    ∀ add ∈ [«&P + &Q», «P + &Q», «&P + Q», «P + Q», «P += &Q», «P += Q»],
      add P Q ⦃ (r : RistrettoPoint) =>
        r.OnCurve ∧ r.toPoint = P.toPoint + Q.toPoint ∧ r.IsBounded ⦄ := by
  open «Shared0RistrettoPointx86_64-tables».Insts in
  variants [«CoreOpsArithAddSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables».add_spec]

/-- `Sub` and `SubAssign`: the difference of the points. -/
theorem sub (P Q : RistrettoPoint) (hP : P.OnCurve) (hP' : P.IsBounded) (hQ : Q.OnCurve)
    (hQ' : Q.IsBounded) :
    ∀ sub ∈ [«&P - &Q», «P - &Q», «&P - Q», «P - Q», «P -= &Q», «P -= Q»],
      sub P Q ⦃ (r : RistrettoPoint) =>
        r.OnCurve ∧ r.toPoint = P.toPoint - Q.toPoint ∧ r.IsBounded ⦄ := by
  open «Shared0RistrettoPointx86_64-tables».Insts in
  variants [«CoreOpsArithSubSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables».sub_spec]

/-- `Sum`: the sum of the points the iterator yields (through `borrow`). -/
theorem sum {T I : Type} (borrowInst : core.borrow.Borrow T RistrettoPoint)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (Ps : List RistrettoPoint) (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : RistrettoPoint) => P' = P ⦄) xs Ps)
    (hPs : ∀ P ∈ Ps, P.OnCurve) (hPs' : ∀ P ∈ Ps, P.IsBounded) :
    ristretto.RistrettoPoint.«x86_64-tables».Insts.CoreIterTraitsAccumSum.sum borrowInst iterInst
      iter ⦃ (r : RistrettoPoint) =>
        r.OnCurve ∧ r.toPoint = (Ps.map (·.toPoint)).sum ∧ r.IsBounded ⦄ := by
  apply ristretto.RistrettoPoint.«x86_64-tables».Insts.CoreIterTraitsAccumSum.sum_spec <;>
    assumption

/-- `Neg`: the negation of the point. -/
theorem neg (P : RistrettoPoint) (hP : P.OnCurve) (hP' : P.IsBounded) :
    ∀ neg ∈ [«-&P», «-P»],
      neg P ⦃ (r : RistrettoPoint) => r.OnCurve ∧ r.toPoint = -P.toPoint ∧ r.IsBounded ⦄ := by
  open «Shared0RistrettoPointx86_64-tables».Insts in
  variants [«CoreOpsArithNegRistrettoPointx86_64-tables».neg_spec]

/-- `Mul<Scalar>` and `MulAssign<Scalar>`: `s • P`. -/
theorem mul (P : RistrettoPoint) (s : Scalar) (hP : P.OnCurve) (hP' : P.IsBounded)
    (hs : s.asNat < 2 ^ 255) :
    ∀ mul ∈ [«&P * &s», «P * &s», «&P * s», «P * s», «P *= &s», «P *= s»],
      mul P s ⦃ (r : RistrettoPoint) =>
        r.OnCurve ∧ r.toPoint = s.asNat • P.toPoint ∧ r.IsBounded ⦄ := by
  open «Shared0RistrettoPointx86_64-tables».Insts in
  variants [«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables».mul_spec]

/-- `Mul<RistrettoPoint> for Scalar`: `s • P`. -/
theorem mul_left (s : Scalar) (P : RistrettoPoint) (hs : s.asNat < 2 ^ 255) (hP : P.OnCurve)
    (hP' : P.IsBounded) :
    ∀ mul ∈ [«&s * &P», «s * &P», «&s * P», «s * P»],
      mul s P ⦃ (r : RistrettoPoint) =>
        r.OnCurve ∧ r.toPoint = s.asNat • P.toPoint ∧ r.IsBounded ⦄ := by
  open Shared0Scalar.Insts in
  variants [«CoreOpsArithMulSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables».mul_spec]

/-- `mul_base`: `s • B` for the basepoint `B`: an even point. -/
theorem mul_base (s : Scalar) (hs : s.asNat < 2 ^ 255) :
    ristretto.«RistrettoPointx86_64-tables».mul_base s ⦃ (r : RistrettoPoint) =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = s.asNat • basepoint ∧ r.IsBounded ⦄ :=
  ristretto.«RistrettoPointx86_64-tables».mul_base_spec s hs

end RistrettoPoint

/-! ### Multiscalar multiplication -/

namespace RistrettoPoint

open ristretto.RistrettoPoint.«x86_64-tables».Insts

/-- `MultiscalarMul::multiscalar_mul`: `∑ s_i • P_i` over the scalars and points the two inputs
yield, which must be equally many (the patched `assert_eq!`). -/
theorem multiscalar_mul
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item RistrettoPoint)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List Scalar) (Ps : List RistrettoPoint)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y ⦃ (P' : RistrettoPoint) => P' = P ⦄) ys Ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hPs : ∀ P ∈ Ps, P.OnCurve)
    (hPs' : ∀ P ∈ Ps, P.IsBounded) (hxs : xs.length ≤ Usize.max) (hlen : xs.length = ys.length) :
    «Curve25519_dalekTraitsMultiscalarMulRistrettoPointx86_64-tables».multiscalar_mul
      scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : RistrettoPoint) => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss Ps).sum ∧ r.IsBounded ⦄ := by
  apply «Curve25519_dalekTraitsMultiscalarMulRistrettoPointx86_64-tables».multiscalar_mul_spec <;>
    assumption

open «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPointx86_64-tables» in
/-- `VartimeMultiscalarMul::optional_multiscalar_mul`: `none` iff some point is `none`; otherwise
`∑ s_i • P_i` over the scalars and points, which must be equally many (the patched
`assert_eq!`). -/
theorem optional_multiscalar_mul {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J (Option RistrettoPoint) Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ops : List (Option RistrettoPoint))
    (ss : List Scalar) (hscalars : scalarsInst.Yields scalars xs)
    (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hPs : ∀ P, some P ∈ ops → P.OnCurve)
    (hPs' : ∀ P, some P ∈ ops → P.IsBounded) (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option RistrettoPoint) => (none ∈ ops → r = none) ∧
        ∀ Ps, ops = Ps.map some → ∃ R, r = some R ∧ R.OnCurve ∧
          R.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss Ps).sum ∧
          R.IsBounded ⦄ := by
  apply optional_multiscalar_mul_spec <;> assumption

end RistrettoPoint

namespace VartimeRistrettoPrecomputation

open ristretto.VartimeRistrettoPrecomputation.«x86_64-tables».Insts
open «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPointx86_64-tables»

/-- `VartimePrecomputedMultiscalarMul::new`: a precomputation of the points the input yields
(through `borrow`). -/
theorem new {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item RistrettoPoint)
    (static_points : I) (ys : List Clause0_Item) (Ps : List RistrettoPoint)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : RistrettoPoint) => P' = P ⦄) ys Ps)
    (hPs : ∀ P ∈ Ps, P.OnCurve) (hPs' : ∀ P ∈ Ps, P.IsBounded) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points ⦃ (r : VartimeRistrettoPrecomputation) =>
      r.IsValid ∧ r.points = Ps.map (·.toPoint) ∧ r.IsBounded ⦄ := by
  apply new_spec <;> assumption

/-- `VartimePrecomputedMultiscalarMul::len`: the number of static points. -/
theorem len (pre : VartimeRistrettoPrecomputation) :
    len pre ⦃ (r : Usize) => r.val = pre.points.length ⦄ :=
  len_spec pre

/-- `VartimePrecomputedMultiscalarMul::is_empty`: whether there are no static points. -/
theorem is_empty (pre : VartimeRistrettoPrecomputation) :
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
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K (Option RistrettoPoint)
      Clause4_IntoIter)
    (pre : VartimeRistrettoPrecomputation)
    (static_scalars : I) (dynamic_scalars : J) (dynamic_points : K) (xs : List Clause0_Item)
    (ss : List Scalar) (ys : List Clause2_Item) (ds : List Scalar)
    (qops : List (Option RistrettoPoint))
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
      ⦃ (r : Option RistrettoPoint) => (none ∈ qops → r = none) ∧
        ∀ Qs, qops = Qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧
          R.toPoint = (List.zipWith (fun s P => s.asNat • P) ss pre.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds Qs).sum ∧
          R.IsBounded ⦄ := by
  apply optional_mixed_multiscalar_mul_spec <;> assumption

end VartimeRistrettoPrecomputation

namespace RistrettoPoint

/-- `vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`. -/
theorem vartime_double_scalar_mul_basepoint (a : Scalar) (A : RistrettoPoint) (b : Scalar)
    (ha : a.asNat < 2 ^ 255) (hA : A.OnCurve) (hA' : A.IsBounded) (hb : b.asNat < 2 ^ 255) :
    ristretto.«RistrettoPointx86_64-tables».vartime_double_scalar_mul_basepoint a A b
      ⦃ (r : RistrettoPoint) =>
        r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.IsBounded ⦄ :=
  ristretto.«RistrettoPointx86_64-tables».vartime_double_scalar_mul_basepoint_spec a A b ha hA' hA
    hb

end RistrettoPoint

-- BEGIN TABLES-ONLY
/-! ### Basepoint table -/

/-- `RistrettoBasepointTable` in this configuration. -/
abbrev RistrettoBasepointTable := ristretto.RistrettoBasepointTable.«x86_64-tables»

namespace RistrettoBasepointTable

/-- `impl Mul<&Scalar> for &RistrettoBasepointTable` -/
abbrev «&t * &s» := open «Shared0RistrettoBasepointTablex86_64-tables».Insts in
  «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-tables».mul
/-- `impl Mul<&RistrettoBasepointTable> for &Scalar` -/
abbrev «&s * &t» := open Shared0Scalar.Insts in
  «CoreOpsArithMulSharedARistrettoBasepointTablex86_64-tablesRistrettoPointx86_64-tables».mul

/-- `Mul<&Scalar> for &RistrettoBasepointTable` and its reverse: `s • t.point`. -/
theorem mul (t : RistrettoBasepointTable) (s : Scalar) (ht : t.IsTable) (ht' : t.IsBounded)
    (hs : s.asNat < 2 ^ 255) :
    ∀ ts ∈ [«&t * &s» t s, «&s * &t» s t],
      ts ⦃ (r : RistrettoPoint) => r.OnCurve ∧ r.toPoint = s.asNat • t.point ∧ r.IsBounded ⦄ := by
  open «Shared0RistrettoBasepointTablex86_64-tables».Insts in
  variants [«CoreOpsArithMulSharedBScalarRistrettoPointx86_64-tables».mul_spec]

open ristretto.«RistrettoBasepointTablex86_64-tables»

/-- `create`: a table of `B`. -/
theorem create (B : RistrettoPoint) (hB : B.OnCurve) (hB' : B.IsBounded) :
    create B ⦃ (t : RistrettoBasepointTable) =>
      t.IsTable ∧ t.point = B.toPoint ∧ t.IsBounded ⦄ :=
  create_spec B hB' hB

/-- `basepoint`: the table's point. -/
theorem basepoint (t : RistrettoBasepointTable) (ht : t.IsTable) (ht' : t.IsBounded) :
    basepoint t ⦃ (r : RistrettoPoint) => r.OnCurve ∧ r.toPoint = t.point ∧ r.IsBounded ⦄ :=
  basepoint_spec t ht' ht

end RistrettoBasepointTable
-- END TABLES-ONLY

namespace RistrettoPoint

open ristretto.RistrettoPoint.«x86_64-tables».Insts

/-- `ConditionallySelectable`: `a` if `choice = 0`, `b` if `choice = 1`. -/
theorem conditional_select (a b : RistrettoPoint) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    SubtleConditionallySelectable.conditional_select a b choice ⦃ (r : RistrettoPoint) =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  SubtleConditionallySelectable.conditional_select_spec a b choice hchoice

/-- `Zeroize`: leaves the neutral element. -/
theorem zeroize (P : RistrettoPoint) :
    ZeroizeZeroize.zeroize P ⦃ (r : RistrettoPoint) => r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄ :=
  ZeroizeZeroize.zeroize_spec P

/-- `elligator`'s `RistrettoPoint::map_to_curve`: RFC 9496's `MAP` of the 32 bytes
(`Ristretto.mapRep`): an even point (a ristretto255 representative). -/
theorem map_to_curve (bytes : Array U8 32#usize) :
    ristretto.elligator.«RistrettoPointx86_64-tables».map_to_curve bytes ⦃ (r : RistrettoPoint) =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.mapRep bytes.toVector ∧ r.IsBounded ⦄ :=
  ristretto.elligator.«RistrettoPointx86_64-tables».map_to_curve_spec bytes

end RistrettoPoint

end Specs.ristretto.«x86_64-tables»
-- END PER-CONFIG
