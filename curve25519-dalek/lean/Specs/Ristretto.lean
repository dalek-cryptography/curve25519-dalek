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
import Proofs.Ristretto.Add
import Proofs.Ristretto.AddAssign
import Proofs.Ristretto.AsBytes
import Proofs.Ristretto.BasepointTable
import Proofs.Ristretto.Compress
import Proofs.Ristretto.CompressedCtEq
import Proofs.Ristretto.CompressedEq
import Proofs.Ristretto.CompressedIdentity
import Proofs.Ristretto.CompressedZeroize
import Proofs.Ristretto.ConditionalSelect
import Proofs.Ristretto.CtEq
import Proofs.Ristretto.Decompress
import Proofs.Ristretto.DoubleAndCompressBatch
import Proofs.Ristretto.Elligator
import Proofs.Ristretto.FromSlice
import Proofs.Ristretto.FromUniformBytes
import Proofs.Ristretto.Identity
import Proofs.Ristretto.Mul
import Proofs.Ristretto.MulAssign
import Proofs.Ristretto.MulBase
import Proofs.Ristretto.MultiscalarMul
import Proofs.Ristretto.Neg
import Proofs.Ristretto.OptionalMultiscalarMul
import Proofs.Ristretto.Sub
import Proofs.Ristretto.SubAssign
import Proofs.Ristretto.Sum
import Proofs.Ristretto.ToBytes
import Proofs.Ristretto.VartimeDoubleScalarMulBasepoint
import Proofs.Ristretto.VartimeRistrettoPrecomputation
import Zeroize.Instances
public section

/-! # Specs of `src/ristretto.rs` and `src/ristretto/elligator.rs`

Spec summary: the items of `ristretto.rs` (and its submodule `elligator.rs`) in the crate's public
API with their spec statements, restated with `recall` from the theorems proved in
`Proofs/Ristretto/`, and the axioms they depend on.

A `RistrettoPoint` is an `EdwardsPoint` (`Defs/Ristretto.lean`): the statements are about the
represented Edwards point, which stands for an element of ristretto255 when it is even (Mathlib's
`Even`). The functions that create points (`decompress`, `from_uniform_bytes`, `map_to_curve`,
`identity`, `default`, `mul_base`, `RISTRETTO_BASEPOINT_POINT`) state that the point is even. Group
operations are stated exactly on representatives (as for `EdwardsPoint`), so they keep points even
and also hold for the elements; `ct_eq`/`eq` decide `curve25519.edwards.Rel` (equality in the
Ristretto group); `compress` is RFC 9496's encoding `Ristretto.encodeRep` of the represented point,
as 32 bytes (for any representative; on even points it is constant exactly on the classes of `Rel`,
`Ristretto.encodeRepNat_eq_iff`); `decompress` is RFC 9496's decoding `Ristretto.decodeRep` of the
bytes; `double_and_compress_batch` encodes the doubled points; `from_uniform_bytes` is RFC 9496's
one-way map `Ristretto.fromUniformRep` on 64 bytes, and `map_to_curve` its `MAP` on 32 bytes
(`Ristretto.mapRep`: the low 255 bits modulo `p`). Scalars are unreduced and must be `< 2^255`
(invariant #1 of `Scalar` in `scalar.rs`). The multiscalar statements are about the patched code
(`translation-patches/ristretto-{multiscalar,optional_multiscalar}_mul.patch` on top of the
`EdwardsPoint` ones), which requires as many scalars as points; the original panics unless both
inputs' `size_hint`s are exact and equal. Functions with per-target variants are stated for all four
configurations (`«x86_64-tables»`, `«x86_64-no-tables»`, `«i686-tables»`, `«i686-no-tables»`);
`RistrettoBasepointTable` exists only with tables.

Definitions used: `EdwardsPoint.toPoint`, `OnCurve`, `IsBounded`, the tables' `point`, `IsTable` and
`IsBounded`, the precomputations' `points`, `IsValid` and `IsBounded` (`Defs/Edwards.lean`,
`Defs/ScalarMul.lean`), `Array.toVector`
(`ToAeneas/Array.lean`), `Scalar.asNat` (`Defs/Scalar.lean`), `Iterator.Yields`
(`ToAeneas/Iterator.lean`), Mathlib's `Even`, `curve25519.edwards.Rel`, `Ristretto.encodeRep`,
`Ristretto.decodeRep`, `Ristretto.mapRep`, `Ristretto.fromUniformRep` (`Curve25519/Ristretto/`),
`curve25519.basepoint` (`Curve25519/`), `subtle.Choice.IsValid` (`Subtle/`).

Not specified: derived `Clone`/`Copy` impls. Not translated: `Debug`, `Hash`, `random`,
`try_random`, `hash_from_bytes`, `from_hash`, the `group` and `serde` impls.
`elligator_ristretto_flavor`
(`pub(crate)`) and the private `coset4` are specified in their proof files. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.ristretto.CompressedRistretto.Insts.CoreCmpPartialEqCompressedRistretto

/-- `PartialEq for CompressedRistretto`: byte equality. -/
recall eq_spec (self other : CompressedRistretto) :
    eq self other ⦃ (r : Bool) => r = true ↔ self = other ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec

end Curve25519Dalek.ristretto.CompressedRistretto.Insts.CoreCmpPartialEqCompressedRistretto

namespace Curve25519Dalek.ristretto.CompressedRistretto.Insts.SubtleConstantTimeEq

/-- `ConstantTimeEq for CompressedRistretto`: byte equality. -/
recall ct_eq_spec (self other : CompressedRistretto) :
    ct_eq self other ⦃ (r : subtle.Choice) => r.IsValid ∧ (r = 1#u8 ↔ self = other) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec

end Curve25519Dalek.ristretto.CompressedRistretto.Insts.SubtleConstantTimeEq

namespace Curve25519Dalek.ristretto.CompressedRistretto

/-- `CompressedRistretto::to_bytes`: the bytes. -/
recall to_bytes_spec (self : CompressedRistretto) :
    to_bytes self ⦃ (r : Array U8 32#usize) => r = self ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_bytes_spec


/-- `CompressedRistretto::as_bytes`: the bytes. -/
recall as_bytes_spec (self : CompressedRistretto) :
    as_bytes self ⦃ (r : Array U8 32#usize) => r = self ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms as_bytes_spec


/-- `CompressedRistretto::from_slice`: the bytes of a slice of length `32`, an error otherwise. -/
recall from_slice_spec (bytes : Slice U8) :
    from_slice bytes ⦃ (r : core.result.Result CompressedRistretto core.array.TryFromSliceError) =>
      match r with
      | .Ok c => bytes.length = 32 ∧ ∀ i < 32, c[i]! = bytes[i]!
      | .Err _ => bytes.length ≠ 32 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_slice_spec

end Curve25519Dalek.ristretto.CompressedRistretto

namespace Curve25519Dalek.ristretto
namespace CompressedRistretto

/-- `CompressedRistretto::decompress`: RFC 9496's decoding `decodeRep` of the bytes, `none` exactly
when they are not a valid ristretto255 encoding; the point is even (a ristretto255
representative). -/
recall «x86_64-tables».decompress_spec (self : CompressedRistretto) :
    decompress.«x86_64-tables» self ⦃ (r : Option RistrettoPoint.«x86_64-tables») =>
      r.map edwards.EdwardsPoint.«x86_64-tables».toPoint = Ristretto.decodeRep self.toVector ∧
      ∀ q, r = some q → q.OnCurve ∧ Even q.toPoint ∧ q.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms «x86_64-tables».decompress_spec


/-- `CompressedRistretto::decompress`: RFC 9496's decoding `decodeRep` of the bytes, `none` exactly
when they are not a valid ristretto255 encoding; the point is even (a ristretto255
representative). -/
recall «i686-tables».decompress_spec (self : CompressedRistretto) :
    decompress.«i686-tables» self ⦃ (r : Option RistrettoPoint.«i686-tables») =>
      r.map edwards.EdwardsPoint.«i686-tables».toPoint = Ristretto.decodeRep self.toVector ∧
      ∀ q, r = some q → q.OnCurve ∧ Even q.toPoint ∧ q.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms «i686-tables».decompress_spec


/-- `CompressedRistretto::decompress`: RFC 9496's decoding `decodeRep` of the bytes, `none` exactly
when they are not a valid ristretto255 encoding; the point is even (a ristretto255
representative). -/
recall «x86_64-no-tables».decompress_spec (self : CompressedRistretto) :
    decompress.«x86_64-no-tables» self ⦃ (r : Option RistrettoPoint.«x86_64-no-tables») =>
      r.map edwards.EdwardsPoint.«x86_64-no-tables».toPoint = Ristretto.decodeRep self.toVector ∧
      ∀ q, r = some q → q.OnCurve ∧ Even q.toPoint ∧ q.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms «x86_64-no-tables».decompress_spec


/-- `CompressedRistretto::decompress`: RFC 9496's decoding `decodeRep` of the bytes, `none` exactly
when they are not a valid ristretto255 encoding; the point is even (a ristretto255
representative). -/
recall «i686-no-tables».decompress_spec (self : CompressedRistretto) :
    decompress.«i686-no-tables» self ⦃ (r : Option RistrettoPoint.«i686-no-tables») =>
      r.map edwards.EdwardsPoint.«i686-no-tables».toPoint = Ristretto.decodeRep self.toVector ∧
      ∀ q, r = some q → q.OnCurve ∧ Even q.toPoint ∧ q.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms «i686-no-tables».decompress_spec

end CompressedRistretto
end Curve25519Dalek.ristretto

namespace Curve25519Dalek.ristretto.CompressedRistretto
namespace Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for CompressedRistretto` is the encoding of the neutral element. -/
recall identity_spec :
    identity ⦃ (r : CompressedRistretto) => r.toVector = Ristretto.encodeRep 0 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms identity_spec

end Insts.Curve25519_dalekTraitsIdentity
end Curve25519Dalek.ristretto.CompressedRistretto

namespace Curve25519Dalek.ristretto.CompressedRistretto
namespace Insts.CoreDefaultDefault

/-- `Default for CompressedRistretto` is the encoding of the neutral element. -/
recall default_spec :
    default ⦃ (r : CompressedRistretto) => r.toVector = Ristretto.encodeRep 0 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec

end Insts.CoreDefaultDefault
end Curve25519Dalek.ristretto.CompressedRistretto

namespace Curve25519Dalek.ristretto.CompressedRistretto
namespace Insts.CoreConvertTryFromShared0SliceU8TryFromSliceError

/-- `TryFrom<&[u8]> for CompressedRistretto`: as `from_slice`. -/
recall try_from_spec (slice : Slice U8) :
    try_from slice ⦃ (r : core.result.Result CompressedRistretto core.array.TryFromSliceError) =>
      match r with
      | .Ok c => slice.length = 32 ∧ ∀ i < 32, c[i]! = slice[i]!
      | .Err _ => slice.length ≠ 32 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms try_from_spec

end Insts.CoreConvertTryFromShared0SliceU8TryFromSliceError
end Curve25519Dalek.ristretto.CompressedRistretto

namespace Curve25519Dalek.ristretto
namespace «RistrettoPointx86_64-tables»

/-- `RistrettoPoint::compress`: RFC 9496's encoding of the represented point. -/
recall compress_spec (self : RistrettoPoint.«x86_64-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedRistretto) =>
      r.toVector = Ristretto.encodeRep self.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_spec

end «RistrettoPointx86_64-tables»

namespace «RistrettoPointi686-tables»

/-- `RistrettoPoint::compress`: RFC 9496's encoding of the represented point. -/
recall compress_spec (self : RistrettoPoint.«i686-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedRistretto) =>
      r.toVector = Ristretto.encodeRep self.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_spec

end «RistrettoPointi686-tables»
end Curve25519Dalek.ristretto

namespace Curve25519Dalek.ristretto
namespace «RistrettoPointx86_64-no-tables»

/-- `RistrettoPoint::compress`: RFC 9496's encoding of the represented point. -/
recall compress_spec (self : RistrettoPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedRistretto) =>
      r.toVector = Ristretto.encodeRep self.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_spec

end «RistrettoPointx86_64-no-tables»

namespace «RistrettoPointi686-no-tables»

/-- `RistrettoPoint::compress`: RFC 9496's encoding of the represented point. -/
recall compress_spec (self : RistrettoPoint.«i686-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedRistretto) =>
      r.toVector = Ristretto.encodeRep self.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms compress_spec

end «RistrettoPointi686-no-tables»
end Curve25519Dalek.ristretto

namespace Curve25519Dalek.ristretto
namespace «RistrettoPointx86_64-tables»

/-- `RistrettoPoint::double_and_compress_batch`: entry `i` is RFC 9496's encoding of `2 P_i` for
the points `P_i` the input yields. -/
recall double_and_compress_batch_spec {I Clause0_IntoIter : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«x86_64-tables» Clause0_IntoIter)
    (points : I) (ps : List RistrettoPoint.«x86_64-tables»)
    (hpoints : pointsInst.Yields points ps)
    (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hlen : ps.length ≤ Usize.max) :
    double_and_compress_batch pointsInst points ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = ps.length ∧
        ∀ i < ps.length, r[i]!.toVector = Ristretto.encodeRep (2 • (ps[i]!).toPoint) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.alloc, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms double_and_compress_batch_spec

end «RistrettoPointx86_64-tables»

namespace «RistrettoPointi686-tables»

/-- `RistrettoPoint::double_and_compress_batch`: entry `i` is RFC 9496's encoding of `2 P_i` for
the points `P_i` the input yields. -/
recall double_and_compress_batch_spec {I Clause0_IntoIter : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«i686-tables» Clause0_IntoIter)
    (points : I) (ps : List RistrettoPoint.«i686-tables»)
    (hpoints : pointsInst.Yields points ps)
    (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hlen : ps.length ≤ Usize.max) :
    double_and_compress_batch pointsInst points ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = ps.length ∧
        ∀ i < ps.length, r[i]!.toVector = Ristretto.encodeRep (2 • (ps[i]!).toPoint) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.alloc, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms double_and_compress_batch_spec

end «RistrettoPointi686-tables»
end Curve25519Dalek.ristretto

namespace Curve25519Dalek.ristretto
namespace «RistrettoPointx86_64-no-tables»

/-- `RistrettoPoint::double_and_compress_batch`: entry `i` is RFC 9496's encoding of `2 P_i` for
the points `P_i` the input yields. -/
recall double_and_compress_batch_spec {I Clause0_IntoIter : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«x86_64-no-tables» Clause0_IntoIter)
    (points : I) (ps : List RistrettoPoint.«x86_64-no-tables»)
    (hpoints : pointsInst.Yields points ps)
    (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hlen : ps.length ≤ Usize.max) :
    double_and_compress_batch pointsInst points ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = ps.length ∧
        ∀ i < ps.length, r[i]!.toVector = Ristretto.encodeRep (2 • (ps[i]!).toPoint) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.alloc, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms double_and_compress_batch_spec

end «RistrettoPointx86_64-no-tables»

namespace «RistrettoPointi686-no-tables»

/-- `RistrettoPoint::double_and_compress_batch`: entry `i` is RFC 9496's encoding of `2 P_i` for
the points `P_i` the input yields. -/
recall double_and_compress_batch_spec {I Clause0_IntoIter : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«i686-no-tables» Clause0_IntoIter)
    (points : I) (ps : List RistrettoPoint.«i686-no-tables»)
    (hpoints : pointsInst.Yields points ps)
    (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hlen : ps.length ≤ Usize.max) :
    double_and_compress_batch pointsInst points ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = ps.length ∧
        ∀ i < ps.length, r[i]!.toVector = Ristretto.encodeRep (2 • (ps[i]!).toPoint) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.alloc, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms double_and_compress_batch_spec

end «RistrettoPointi686-no-tables»
end Curve25519Dalek.ristretto

namespace Curve25519Dalek.ristretto
namespace «RistrettoPointx86_64-tables»

/-- `RistrettoPoint::from_uniform_bytes`: RFC 9496's one-way map of the 64 bytes' little-endian
value, `MAP(r₀) + MAP(r₁)` for the two halves: an even point (a ristretto255 representative). -/
recall from_uniform_bytes_spec (bytes : Array U8 64#usize) :
    from_uniform_bytes bytes ⦃ (r : RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.fromUniformRep bytes.toVector ∧
        r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_uniform_bytes_spec

end «RistrettoPointx86_64-tables»

namespace «RistrettoPointi686-tables»

/-- `RistrettoPoint::from_uniform_bytes`: RFC 9496's one-way map of the 64 bytes' little-endian
value, `MAP(r₀) + MAP(r₁)` for the two halves: an even point (a ristretto255 representative). -/
recall from_uniform_bytes_spec (bytes : Array U8 64#usize) :
    from_uniform_bytes bytes ⦃ (r : RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.fromUniformRep bytes.toVector ∧
        r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_uniform_bytes_spec

end «RistrettoPointi686-tables»
end Curve25519Dalek.ristretto

namespace Curve25519Dalek.ristretto
namespace «RistrettoPointx86_64-no-tables»

/-- `RistrettoPoint::from_uniform_bytes`: RFC 9496's one-way map of the 64 bytes' little-endian
value, `MAP(r₀) + MAP(r₁)` for the two halves: an even point (a ristretto255 representative). -/
recall from_uniform_bytes_spec (bytes : Array U8 64#usize) :
    from_uniform_bytes bytes ⦃ (r : RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.fromUniformRep bytes.toVector ∧
        r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_uniform_bytes_spec

end «RistrettoPointx86_64-no-tables»

namespace «RistrettoPointi686-no-tables»

/-- `RistrettoPoint::from_uniform_bytes`: RFC 9496's one-way map of the 64 bytes' little-endian
value, `MAP(r₀) + MAP(r₁)` for the two halves: an even point (a ristretto255 representative). -/
recall from_uniform_bytes_spec (bytes : Array U8 64#usize) :
    from_uniform_bytes bytes ⦃ (r : RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.fromUniformRep bytes.toVector ∧
        r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_uniform_bytes_spec

end «RistrettoPointi686-no-tables»
end Curve25519Dalek.ristretto

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for RistrettoPoint` represents the neutral element. -/
recall identity_spec :
    identity ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms identity_spec

end ristretto.RistrettoPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity

namespace ristretto.RistrettoPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for RistrettoPoint` represents the neutral element. -/
recall identity_spec :
    identity ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms identity_spec

end ristretto.RistrettoPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts.CoreDefaultDefault

/-- `Default for RistrettoPoint` represents the neutral element. -/
recall default_spec :
    default ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec

end ristretto.RistrettoPoint.«x86_64-tables».Insts.CoreDefaultDefault

namespace ristretto.RistrettoPoint.«i686-tables».Insts.CoreDefaultDefault

/-- `Default for RistrettoPoint` represents the neutral element. -/
recall default_spec :
    default ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec

end ristretto.RistrettoPoint.«i686-tables».Insts.CoreDefaultDefault
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for RistrettoPoint` represents the neutral element. -/
recall identity_spec :
    identity ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms identity_spec

end ristretto.RistrettoPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for RistrettoPoint` represents the neutral element. -/
recall identity_spec :
    identity ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms identity_spec

end ristretto.RistrettoPoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts.CoreDefaultDefault

/-- `Default for RistrettoPoint` represents the neutral element. -/
recall default_spec :
    default ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec

end ristretto.RistrettoPoint.«x86_64-no-tables».Insts.CoreDefaultDefault

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts.CoreDefaultDefault

/-- `Default for RistrettoPoint` represents the neutral element. -/
recall default_spec :
    default ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec

end ristretto.RistrettoPoint.«i686-no-tables».Insts.CoreDefaultDefault
end Curve25519Dalek

namespace Curve25519Dalek.ristretto
namespace RistrettoPoint.«x86_64-tables».Insts
namespace «CoreCmpPartialEqRistrettoPointx86_64-tables»

/-- `PartialEq for RistrettoPoint`: equality in the Ristretto group. -/
recall eq_spec (self other : RistrettoPoint.«x86_64-tables») (hself : self.IsBounded)
    (hother : other.IsBounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (r : Bool) =>
      r = true ↔ curve25519.edwards.Rel self.toPoint other.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec

end «CoreCmpPartialEqRistrettoPointx86_64-tables»
end RistrettoPoint.«x86_64-tables».Insts

namespace RistrettoPoint.«i686-tables».Insts
namespace «CoreCmpPartialEqRistrettoPointi686-tables»

/-- `PartialEq for RistrettoPoint`: equality in the Ristretto group. -/
recall eq_spec (self other : RistrettoPoint.«i686-tables») (hself : self.IsBounded)
    (hother : other.IsBounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (r : Bool) =>
      r = true ↔ curve25519.edwards.Rel self.toPoint other.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec

end «CoreCmpPartialEqRistrettoPointi686-tables»
end RistrettoPoint.«i686-tables».Insts
end Curve25519Dalek.ristretto

namespace Curve25519Dalek.ristretto
namespace RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreCmpPartialEqRistrettoPointx86_64-no-tables»

/-- `PartialEq for RistrettoPoint`: equality in the Ristretto group. -/
recall eq_spec (self other : RistrettoPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hother : other.IsBounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (r : Bool) =>
      r = true ↔ curve25519.edwards.Rel self.toPoint other.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec

end «CoreCmpPartialEqRistrettoPointx86_64-no-tables»
end RistrettoPoint.«x86_64-no-tables».Insts

namespace RistrettoPoint.«i686-no-tables».Insts
namespace «CoreCmpPartialEqRistrettoPointi686-no-tables»

/-- `PartialEq for RistrettoPoint`: equality in the Ristretto group. -/
recall eq_spec (self other : RistrettoPoint.«i686-no-tables») (hself : self.IsBounded)
    (hother : other.IsBounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    eq self other ⦃ (r : Bool) =>
      r = true ↔ curve25519.edwards.Rel self.toPoint other.toPoint ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec

end «CoreCmpPartialEqRistrettoPointi686-no-tables»
end RistrettoPoint.«i686-no-tables».Insts
end Curve25519Dalek.ristretto

namespace Curve25519Dalek.ristretto
namespace RistrettoPoint.«x86_64-tables».Insts.SubtleConstantTimeEq

/-- `ConstantTimeEq for RistrettoPoint`: equality in the Ristretto group, i.e. of the classes of
the represented points (`X₁ Y₂ = Y₁ X₂` or `X₁ X₂ = Y₁ Y₂`). -/
recall ct_eq_spec (self other : RistrettoPoint.«x86_64-tables») (hself : self.IsBounded)
    (hother : other.IsBounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (r : subtle.Choice) =>
      r.IsValid ∧ (r = 1#u8 ↔ curve25519.edwards.Rel self.toPoint other.toPoint) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec

end RistrettoPoint.«x86_64-tables».Insts.SubtleConstantTimeEq

namespace RistrettoPoint.«i686-tables».Insts.SubtleConstantTimeEq

/-- `ConstantTimeEq for RistrettoPoint`: equality in the Ristretto group, i.e. of the classes of
the represented points (`X₁ Y₂ = Y₁ X₂` or `X₁ X₂ = Y₁ Y₂`). -/
recall ct_eq_spec (self other : RistrettoPoint.«i686-tables») (hself : self.IsBounded)
    (hother : other.IsBounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (r : subtle.Choice) =>
      r.IsValid ∧ (r = 1#u8 ↔ curve25519.edwards.Rel self.toPoint other.toPoint) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec

end RistrettoPoint.«i686-tables».Insts.SubtleConstantTimeEq
end Curve25519Dalek.ristretto

namespace Curve25519Dalek.ristretto
namespace RistrettoPoint.«x86_64-no-tables».Insts.SubtleConstantTimeEq

/-- `ConstantTimeEq for RistrettoPoint`: equality in the Ristretto group, i.e. of the classes of
the represented points (`X₁ Y₂ = Y₁ X₂` or `X₁ X₂ = Y₁ Y₂`). -/
recall ct_eq_spec (self other : RistrettoPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hother : other.IsBounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (r : subtle.Choice) =>
      r.IsValid ∧ (r = 1#u8 ↔ curve25519.edwards.Rel self.toPoint other.toPoint) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec

end RistrettoPoint.«x86_64-no-tables».Insts.SubtleConstantTimeEq

namespace RistrettoPoint.«i686-no-tables».Insts.SubtleConstantTimeEq

/-- `ConstantTimeEq for RistrettoPoint`: equality in the Ristretto group, i.e. of the classes of
the represented points (`X₁ Y₂ = Y₁ X₂` or `X₁ X₂ = Y₁ Y₂`). -/
recall ct_eq_spec (self other : RistrettoPoint.«i686-no-tables») (hself : self.IsBounded)
    (hother : other.IsBounded) (hself_on : self.OnCurve) (hother_on : other.OnCurve) :
    ct_eq self other ⦃ (r : subtle.Choice) =>
      r.IsValid ∧ (r = 1#u8 ↔ curve25519.edwards.Rel self.toPoint other.toPoint) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec

end RistrettoPoint.«i686-no-tables».Insts.SubtleConstantTimeEq
end Curve25519Dalek.ristretto

namespace Curve25519Dalek
namespace «Shared0RistrettoPointx86_64-tables».Insts
namespace «CoreOpsArithAddSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Add<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
recall add_spec (self other : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.IsBounded) (hother : other.IsBounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end «Shared0RistrettoPointx86_64-tables».Insts

namespace «Shared0RistrettoPointi686-tables».Insts
namespace «CoreOpsArithAddSharedARistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Add<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
recall add_spec (self other : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.IsBounded) (hother : other.IsBounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddSharedARistrettoPointi686-tablesRistrettoPointi686-tables»
end «Shared0RistrettoPointi686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithAddSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Add<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall add_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithAddSharedBRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Add<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall add_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddSharedBRistrettoPointi686-tablesRistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace «SharedARistrettoPointx86_64-tables».Insts
namespace «CoreOpsArithAddRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Add<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
recall add_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end «SharedARistrettoPointx86_64-tables».Insts

namespace «SharedARistrettoPointi686-tables».Insts
namespace «CoreOpsArithAddRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Add<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
recall add_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddRistrettoPointi686-tablesRistrettoPointi686-tables»
end «SharedARistrettoPointi686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithAddRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Add<RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall add_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithAddRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Add<RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall add_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddRistrettoPointi686-tablesRistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace «Shared0RistrettoPointx86_64-no-tables».Insts
namespace «CoreOpsArithAddSharedARistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Add<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
recall add_spec (self other : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.IsBounded) (hother : other.IsBounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddSharedARistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end «Shared0RistrettoPointx86_64-no-tables».Insts

namespace «Shared0RistrettoPointi686-no-tables».Insts
namespace «CoreOpsArithAddSharedARistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Add<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
recall add_spec (self other : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.IsBounded) (hother : other.IsBounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddSharedARistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end «Shared0RistrettoPointi686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithAddSharedBRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Add<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall add_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddSharedBRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithAddSharedBRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Add<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall add_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddSharedBRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace «SharedARistrettoPointx86_64-no-tables».Insts
namespace «CoreOpsArithAddRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Add<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
recall add_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end «SharedARistrettoPointx86_64-no-tables».Insts

namespace «SharedARistrettoPointi686-no-tables».Insts
namespace «CoreOpsArithAddRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Add<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
recall add_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end «SharedARistrettoPointi686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithAddRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Add<RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall add_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithAddRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Add<RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall add_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end «CoreOpsArithAddRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithAddAssignShared0RistrettoPointx86_64-tables»

/-- `AddAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall add_assign_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end «CoreOpsArithAddAssignShared0RistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithAddAssignShared0RistrettoPointi686-tables»

/-- `AddAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall add_assign_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end «CoreOpsArithAddAssignShared0RistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithAddAssignRistrettoPointx86_64-tables»

/-- `AddAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall add_assign_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end «CoreOpsArithAddAssignRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithAddAssignRistrettoPointi686-tables»

/-- `AddAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall add_assign_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end «CoreOpsArithAddAssignRistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithAddAssignShared0RistrettoPointx86_64-no-tables»

/-- `AddAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall add_assign_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end «CoreOpsArithAddAssignShared0RistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithAddAssignShared0RistrettoPointi686-no-tables»

/-- `AddAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall add_assign_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end «CoreOpsArithAddAssignShared0RistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithAddAssignRistrettoPointx86_64-no-tables»

/-- `AddAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall add_assign_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end «CoreOpsArithAddAssignRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithAddAssignRistrettoPointi686-no-tables»

/-- `AddAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall add_assign_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end «CoreOpsArithAddAssignRistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace «Shared0RistrettoPointx86_64-tables».Insts
namespace «CoreOpsArithSubSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Sub<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
recall sub_spec (self other : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.IsBounded) (hother : other.IsBounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end «Shared0RistrettoPointx86_64-tables».Insts

namespace «Shared0RistrettoPointi686-tables».Insts
namespace «CoreOpsArithSubSharedARistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Sub<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
recall sub_spec (self other : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.IsBounded) (hother : other.IsBounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubSharedARistrettoPointi686-tablesRistrettoPointi686-tables»
end «Shared0RistrettoPointi686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithSubSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Sub<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall sub_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithSubSharedBRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Sub<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall sub_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubSharedBRistrettoPointi686-tablesRistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace «SharedARistrettoPointx86_64-tables».Insts
namespace «CoreOpsArithSubRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Sub<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
recall sub_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end «SharedARistrettoPointx86_64-tables».Insts

namespace «SharedARistrettoPointi686-tables».Insts
namespace «CoreOpsArithSubRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Sub<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
recall sub_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubRistrettoPointi686-tablesRistrettoPointi686-tables»
end «SharedARistrettoPointi686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithSubRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Sub<RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall sub_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithSubRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Sub<RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall sub_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubRistrettoPointi686-tablesRistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace «Shared0RistrettoPointx86_64-no-tables».Insts
namespace «CoreOpsArithSubSharedARistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Sub<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
recall sub_spec (self other : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.IsBounded) (hother : other.IsBounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubSharedARistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end «Shared0RistrettoPointx86_64-no-tables».Insts

namespace «Shared0RistrettoPointi686-no-tables».Insts
namespace «CoreOpsArithSubSharedARistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Sub<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
recall sub_spec (self other : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.IsBounded) (hother : other.IsBounded) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubSharedARistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end «Shared0RistrettoPointi686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithSubSharedBRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Sub<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall sub_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubSharedBRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithSubSharedBRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Sub<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall sub_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubSharedBRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace «SharedARistrettoPointx86_64-no-tables».Insts
namespace «CoreOpsArithSubRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Sub<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
recall sub_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end «SharedARistrettoPointx86_64-no-tables».Insts

namespace «SharedARistrettoPointi686-no-tables».Insts
namespace «CoreOpsArithSubRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Sub<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
recall sub_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end «SharedARistrettoPointi686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithSubRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Sub<RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall sub_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithSubRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Sub<RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall sub_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end «CoreOpsArithSubRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithSubAssignShared0RistrettoPointx86_64-tables»

/-- `SubAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall sub_assign_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end «CoreOpsArithSubAssignShared0RistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithSubAssignShared0RistrettoPointi686-tables»

/-- `SubAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall sub_assign_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end «CoreOpsArithSubAssignShared0RistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithSubAssignRistrettoPointx86_64-tables»

/-- `SubAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall sub_assign_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end «CoreOpsArithSubAssignRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithSubAssignRistrettoPointi686-tables»

/-- `SubAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall sub_assign_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end «CoreOpsArithSubAssignRistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithSubAssignShared0RistrettoPointx86_64-no-tables»

/-- `SubAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall sub_assign_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end «CoreOpsArithSubAssignShared0RistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithSubAssignShared0RistrettoPointi686-no-tables»

/-- `SubAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall sub_assign_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end «CoreOpsArithSubAssignShared0RistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithSubAssignRistrettoPointx86_64-no-tables»

/-- `SubAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall sub_assign_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end «CoreOpsArithSubAssignRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithSubAssignRistrettoPointi686-no-tables»

/-- `SubAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
recall sub_assign_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.IsBounded) (hrhs : rhs.IsBounded) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end «CoreOpsArithSubAssignRistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek.ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace CoreIterTraitsAccumSum

/-- `Sum for RistrettoPoint`: the sum of the points yielded by the iterator (through `borrow`). -/
recall sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T RistrettoPoint.«x86_64-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ps : List RistrettoPoint.«x86_64-tables») (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : RistrettoPoint.«x86_64-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.IsBounded) (hps_on : ∀ P ∈ ps, P.OnCurve) :
    sum borrowInst iterInst iter ⦃ (r : RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = (ps.map (·.toPoint)).sum ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sum_spec

end CoreIterTraitsAccumSum
end Curve25519Dalek.ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«i686-tables».Insts
namespace CoreIterTraitsAccumSum

/-- `Sum for RistrettoPoint`: the sum of the points yielded by the iterator (through `borrow`). -/
recall sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T RistrettoPoint.«i686-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ps : List RistrettoPoint.«i686-tables») (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : RistrettoPoint.«i686-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.IsBounded) (hps_on : ∀ P ∈ ps, P.OnCurve) :
    sum borrowInst iterInst iter ⦃ (r : RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = (ps.map (·.toPoint)).sum ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sum_spec

end CoreIterTraitsAccumSum
end Curve25519Dalek.ristretto.RistrettoPoint.«i686-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace CoreIterTraitsAccumSum

/-- `Sum for RistrettoPoint`: the sum of the points yielded by the iterator (through `borrow`). -/
recall sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T RistrettoPoint.«x86_64-no-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ps : List RistrettoPoint.«x86_64-no-tables») (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : RistrettoPoint.«x86_64-no-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.IsBounded) (hps_on : ∀ P ∈ ps, P.OnCurve) :
    sum borrowInst iterInst iter ⦃ (r : RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = (ps.map (·.toPoint)).sum ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sum_spec

end CoreIterTraitsAccumSum
end Curve25519Dalek.ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace CoreIterTraitsAccumSum

/-- `Sum for RistrettoPoint`: the sum of the points yielded by the iterator (through `borrow`). -/
recall sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T RistrettoPoint.«i686-no-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ps : List RistrettoPoint.«i686-no-tables») (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : RistrettoPoint.«i686-no-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.IsBounded) (hps_on : ∀ P ∈ ps, P.OnCurve) :
    sum borrowInst iterInst iter ⦃ (r : RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = (ps.map (·.toPoint)).sum ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sum_spec

end CoreIterTraitsAccumSum
end Curve25519Dalek.ristretto.RistrettoPoint.«i686-no-tables».Insts

namespace Curve25519Dalek
namespace «Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithNegRistrettoPointx86_64-tables»

/-- `Neg for &RistrettoPoint` negates the represented point. -/
recall neg_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end «Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithNegRistrettoPointx86_64-tables»

namespace «Shared0RistrettoPointi686-tables».Insts.«CoreOpsArithNegRistrettoPointi686-tables»

/-- `Neg for &RistrettoPoint` negates the represented point. -/
recall neg_spec (self : ristretto.RistrettoPoint.«i686-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end «Shared0RistrettoPointi686-tables».Insts.«CoreOpsArithNegRistrettoPointi686-tables»
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithNegRistrettoPointx86_64-tables»

/-- `Neg for RistrettoPoint` negates the represented point. -/
recall neg_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end «CoreOpsArithNegRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithNegRistrettoPointi686-tables»

/-- `Neg for RistrettoPoint` negates the represented point. -/
recall neg_spec (self : ristretto.RistrettoPoint.«i686-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end «CoreOpsArithNegRistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace «Shared0RistrettoPointx86_64-no-tables».Insts
namespace «CoreOpsArithNegRistrettoPointx86_64-no-tables»

/-- `Neg for &RistrettoPoint` negates the represented point. -/
recall neg_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end «CoreOpsArithNegRistrettoPointx86_64-no-tables»
end «Shared0RistrettoPointx86_64-no-tables».Insts

namespace «Shared0RistrettoPointi686-no-tables».Insts
namespace «CoreOpsArithNegRistrettoPointi686-no-tables»

/-- `Neg for &RistrettoPoint` negates the represented point. -/
recall neg_spec (self : ristretto.RistrettoPoint.«i686-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end «CoreOpsArithNegRistrettoPointi686-no-tables»
end «Shared0RistrettoPointi686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithNegRistrettoPointx86_64-no-tables»

/-- `Neg for RistrettoPoint` negates the represented point. -/
recall neg_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end «CoreOpsArithNegRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithNegRistrettoPointi686-no-tables»

/-- `Neg for RistrettoPoint` negates the represented point. -/
recall neg_spec (self : ristretto.RistrettoPoint.«i686-no-tables») (hself : self.IsBounded)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end «CoreOpsArithNegRistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for RistrettoPoint`: as `Mul`. -/
recall mul_assign_spec (self : ristretto.RistrettoPoint.«x86_64-tables»)
    (scalar : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end ristretto.RistrettoPoint.«x86_64-tables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace ristretto.RistrettoPoint.«i686-tables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for RistrettoPoint`: as `Mul`. -/
recall mul_assign_spec (self : ristretto.RistrettoPoint.«i686-tables»)
    (scalar : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end ristretto.RistrettoPoint.«i686-tables».Insts.CoreOpsArithMulAssignSharedAScalar
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for RistrettoPoint`: as `Mul`. -/
recall mul_assign_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (scalar : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end ristretto.RistrettoPoint.«x86_64-no-tables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for RistrettoPoint`: as `Mul`. -/
recall mul_assign_spec (self : ristretto.RistrettoPoint.«i686-no-tables»)
    (scalar : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end ristretto.RistrettoPoint.«i686-no-tables».Insts.CoreOpsArithMulAssignSharedAScalar
end Curve25519Dalek

namespace Curve25519Dalek
namespace «Shared0RistrettoPointx86_64-tables».Insts
namespace «CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables»

/-- `Mul<&Scalar> for &RistrettoPoint`: `scalar • P` (unreduced, `< 2^255`). -/
recall mul_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (scalar : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables»
end «Shared0RistrettoPointx86_64-tables».Insts

namespace «Shared0RistrettoPointi686-tables».Insts
namespace «CoreOpsArithMulSharedAScalarRistrettoPointi686-tables»

/-- `Mul<&Scalar> for &RistrettoPoint`: `scalar • P` (unreduced, `< 2^255`). -/
recall mul_spec (self : ristretto.RistrettoPoint.«i686-tables») (scalar : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAScalarRistrettoPointi686-tables»
end «Shared0RistrettoPointi686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-tables»

/-- `Mul<&Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPointi686-tables»

/-- `Mul<&Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : ristretto.RistrettoPoint.«i686-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarRistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace «SharedARistrettoPointx86_64-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointx86_64-tables»

/-- `Mul<Scalar> for &RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarRistrettoPointx86_64-tables»
end «SharedARistrettoPointx86_64-tables».Insts

namespace «SharedARistrettoPointi686-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointi686-tables»

/-- `Mul<Scalar> for &RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : ristretto.RistrettoPoint.«i686-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarRistrettoPointi686-tables»
end «SharedARistrettoPointi686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointx86_64-tables»

/-- `Mul<Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointi686-tables»

/-- `Mul<Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : ristretto.RistrettoPoint.«i686-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarRistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Mul<&RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (point : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.IsBounded) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

namespace «CoreOpsArithMulSharedARistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Mul<&RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (point : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.IsBounded) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedARistrettoPointi686-tablesRistrettoPointi686-tables»
end Shared0Scalar.Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Mul<&RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

namespace «CoreOpsArithMulSharedBRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Mul<&RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBRistrettoPointi686-tablesRistrettoPointi686-tables»
end scalar.Scalar.Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace SharedAScalar.Insts
namespace «CoreOpsArithMulRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Mul<RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

namespace «CoreOpsArithMulRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Mul<RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulRistrettoPointi686-tablesRistrettoPointi686-tables»
end SharedAScalar.Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Mul<RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

namespace «CoreOpsArithMulRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Mul<RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulRistrettoPointi686-tablesRistrettoPointi686-tables»
end scalar.Scalar.Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace «Shared0RistrettoPointx86_64-no-tables».Insts
namespace «CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables»

/-- `Mul<&Scalar> for &RistrettoPoint`: `scalar • P` (unreduced, `< 2^255`). -/
recall mul_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (scalar : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables»
end «Shared0RistrettoPointx86_64-no-tables».Insts

namespace «Shared0RistrettoPointi686-no-tables».Insts
namespace «CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables»

/-- `Mul<&Scalar> for &RistrettoPoint`: `scalar • P` (unreduced, `< 2^255`). -/
recall mul_spec (self : ristretto.RistrettoPoint.«i686-no-tables») (scalar : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables»
end «Shared0RistrettoPointi686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-no-tables»

/-- `Mul<&Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPointi686-no-tables»

/-- `Mul<&Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : ristretto.RistrettoPoint.«i686-no-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarRistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace «SharedARistrettoPointx86_64-no-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointx86_64-no-tables»

/-- `Mul<Scalar> for &RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarRistrettoPointx86_64-no-tables»
end «SharedARistrettoPointx86_64-no-tables».Insts

namespace «SharedARistrettoPointi686-no-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointi686-no-tables»

/-- `Mul<Scalar> for &RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : ristretto.RistrettoPoint.«i686-no-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarRistrettoPointi686-no-tables»
end «SharedARistrettoPointi686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointx86_64-no-tables»

/-- `Mul<Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointi686-no-tables»

/-- `Mul<Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : ristretto.RistrettoPoint.«i686-no-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulScalarRistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedARistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Mul<&RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (point : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.IsBounded) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedARistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

namespace «CoreOpsArithMulSharedARistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Mul<&RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (point : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.IsBounded) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedARistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end Shared0Scalar.Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulSharedBRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Mul<&RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

namespace «CoreOpsArithMulSharedBRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Mul<&RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end scalar.Scalar.Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace SharedAScalar.Insts
namespace «CoreOpsArithMulRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Mul<RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

namespace «CoreOpsArithMulRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Mul<RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end SharedAScalar.Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Mul<RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

namespace «CoreOpsArithMulRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Mul<RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.IsBounded) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end scalar.Scalar.Insts
end Curve25519Dalek

namespace Curve25519Dalek.ristretto
namespace «RistrettoPointx86_64-tables»

/-- `RistrettoPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`). -/
recall mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = scalar.asNat • basepoint ∧
        r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «RistrettoPointx86_64-tables»

namespace «RistrettoPointi686-tables»

/-- `RistrettoPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`). -/
recall mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = scalar.asNat • basepoint ∧
        r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «RistrettoPointi686-tables»
end Curve25519Dalek.ristretto

namespace Curve25519Dalek.ristretto
namespace «RistrettoPointx86_64-no-tables»

/-- `RistrettoPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`). -/
recall mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = scalar.asNat • basepoint ∧
        r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «RistrettoPointx86_64-no-tables»

namespace «RistrettoPointi686-no-tables»

/-- `RistrettoPoint::mul_base`: `scalar • B` for the basepoint `B` (unreduced, `< 2^255`). -/
recall mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = scalar.asNat • basepoint ∧
        r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

end «RistrettoPointi686-no-tables»
end Curve25519Dalek.ristretto

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for RistrettoPoint`: as `Mul`. -/
recall mul_assign_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end ristretto.RistrettoPoint.«x86_64-tables».Insts.CoreOpsArithMulAssignScalar

namespace ristretto.RistrettoPoint.«i686-tables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for RistrettoPoint`: as `Mul`. -/
recall mul_assign_spec (self : ristretto.RistrettoPoint.«i686-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end ristretto.RistrettoPoint.«i686-tables».Insts.CoreOpsArithMulAssignScalar
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for RistrettoPoint`: as `Mul`. -/
recall mul_assign_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end ristretto.RistrettoPoint.«x86_64-no-tables».Insts.CoreOpsArithMulAssignScalar

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for RistrettoPoint`: as `Mul`. -/
recall mul_assign_spec (self : ristretto.RistrettoPoint.«i686-no-tables») (rhs : scalar.Scalar)
    (hself : self.IsBounded) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end ristretto.RistrettoPoint.«i686-no-tables».Insts.CoreOpsArithMulAssignScalar
end Curve25519Dalek

namespace Curve25519Dalek.ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulRistrettoPointx86_64-tables»

/-- `MultiscalarMul::multiscalar_mul` for `RistrettoPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`). -/
recall multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item ristretto.RistrettoPoint.«x86_64-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List ristretto.RistrettoPoint.«x86_64-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«x86_64-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms multiscalar_mul_spec

end «Curve25519_dalekTraitsMultiscalarMulRistrettoPointx86_64-tables»
end Curve25519Dalek.ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«i686-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulRistrettoPointi686-tables»

/-- `MultiscalarMul::multiscalar_mul` for `RistrettoPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`). -/
recall multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item ristretto.RistrettoPoint.«i686-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List ristretto.RistrettoPoint.«i686-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«i686-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : ristretto.RistrettoPoint.«i686-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms multiscalar_mul_spec

end «Curve25519_dalekTraitsMultiscalarMulRistrettoPointi686-tables»
end Curve25519Dalek.ristretto.RistrettoPoint.«i686-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulRistrettoPointx86_64-no-tables»

/-- `MultiscalarMul::multiscalar_mul` for `RistrettoPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`). -/
recall multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item ristretto.RistrettoPoint.«x86_64-no-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«x86_64-no-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms multiscalar_mul_spec

end «Curve25519_dalekTraitsMultiscalarMulRistrettoPointx86_64-no-tables»
end Curve25519Dalek.ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulRistrettoPointi686-no-tables»

/-- `MultiscalarMul::multiscalar_mul` for `RistrettoPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`). -/
recall multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item ristretto.RistrettoPoint.«i686-no-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List ristretto.RistrettoPoint.«i686-no-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«i686-no-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms multiscalar_mul_spec

end «Curve25519_dalekTraitsMultiscalarMulRistrettoPointi686-no-tables»
end Curve25519Dalek.ristretto.RistrettoPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPointx86_64-tables»

/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `RistrettoPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; unreduced scalars `< 2^255`). -/
recall optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option ristretto.RistrettoPoint.«x86_64-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option ristretto.RistrettoPoint.«x86_64-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.IsBounded)
    (hps_on : ∀ P, some P ∈ ops → P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option ristretto.RistrettoPoint.«x86_64-tables») => (none ∈ ops → r = none) ∧
        ∀ ps, ops = ps.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧
          R.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms optional_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPointx86_64-tables»
end Curve25519Dalek.ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«i686-tables».Insts
namespace «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPointi686-tables»

/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `RistrettoPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; unreduced scalars `< 2^255`). -/
recall optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option ristretto.RistrettoPoint.«i686-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option ristretto.RistrettoPoint.«i686-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.IsBounded)
    (hps_on : ∀ P, some P ∈ ops → P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option ristretto.RistrettoPoint.«i686-tables») => (none ∈ ops → r = none) ∧
        ∀ ps, ops = ps.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧
          R.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms optional_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPointi686-tables»
end Curve25519Dalek.ristretto.RistrettoPoint.«i686-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPointx86_64-no-tables»

/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `RistrettoPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; unreduced scalars `< 2^255`). -/
recall optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option ristretto.RistrettoPoint.«x86_64-no-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option ristretto.RistrettoPoint.«x86_64-no-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.IsBounded)
    (hps_on : ∀ P, some P ∈ ops → P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option ristretto.RistrettoPoint.«x86_64-no-tables») => (none ∈ ops → r = none) ∧
        ∀ ps, ops = ps.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧
          R.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms optional_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPointx86_64-no-tables»
end Curve25519Dalek.ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPointi686-no-tables»

/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `RistrettoPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; unreduced scalars `< 2^255`). -/
recall optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option ristretto.RistrettoPoint.«i686-no-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option ristretto.RistrettoPoint.«i686-no-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.IsBounded)
    (hps_on : ∀ P, some P ∈ ops → P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option ristretto.RistrettoPoint.«i686-no-tables») => (none ∈ ops → r = none) ∧
        ∀ ps, ops = ps.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧
          R.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms optional_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPointi686-no-tables»
end Curve25519Dalek.ristretto.RistrettoPoint.«i686-no-tables».Insts

namespace Curve25519Dalek.ristretto.VartimeRistrettoPrecomputation.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPointx86_64-tables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeRistrettoPrecomputation`: a
precomputation of the points the input yields (through `borrow`). -/
recall new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item ristretto.RistrettoPoint.«x86_64-tables»)
    (static_points : I) (ys : List Clause0_Item)
    (ps : List ristretto.RistrettoPoint.«x86_64-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«x86_64-tables») => P' = P ⦄)
      ys ps)
    (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeRistrettoPrecomputation.«x86_64-tables») =>
        r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms new_spec


/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeRistrettoPrecomputation`: the number of
static points. -/
recall len_spec (self : VartimeRistrettoPrecomputation.«x86_64-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms len_spec


/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeRistrettoPrecomputation`: whether
there are no static points. -/
recall is_empty_spec (self : VartimeRistrettoPrecomputation.«x86_64-tables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_empty_spec


/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeRistrettoPrecomputation` (static points `self.points`): `none` iff some dynamic point is
`none`; otherwise `∑ s_i • P_i + ∑ d_i • Q_i`, missing static scalars counting as `0` (if no point
is `none`, at most `|self.points|` static scalars and as many dynamic scalars as dynamic points). -/
recall optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option ristretto.RistrettoPoint.«x86_64-tables») Clause4_IntoIter)
    (self : VartimeRistrettoPrecomputation.«x86_64-tables») (static_scalars : I)
    (dynamic_scalars : J) (dynamic_points : K)
    (xs : List Clause0_Item) (ss : List scalar.Scalar) (ys : List Clause2_Item)
    (ds : List scalar.Scalar) (qops : List (Option ristretto.RistrettoPoint.«x86_64-tables»))
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
      ⦃ (r : Option ristretto.RistrettoPoint.«x86_64-tables») => (none ∈ qops → r = none) ∧
        ∀ qs, qops = qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds qs).sum ∧
          R.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms optional_mixed_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPointx86_64-tables»
end Curve25519Dalek.ristretto.VartimeRistrettoPrecomputation.«x86_64-tables».Insts

namespace Curve25519Dalek.ristretto.VartimeRistrettoPrecomputation.«i686-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPointi686-tables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeRistrettoPrecomputation`: a
precomputation of the points the input yields (through `borrow`). -/
recall new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item ristretto.RistrettoPoint.«i686-tables»)
    (static_points : I) (ys : List Clause0_Item)
    (ps : List ristretto.RistrettoPoint.«i686-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«i686-tables») => P' = P ⦄)
      ys ps)
    (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeRistrettoPrecomputation.«i686-tables») =>
        r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms new_spec


/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeRistrettoPrecomputation`: the number of
static points. -/
recall len_spec (self : VartimeRistrettoPrecomputation.«i686-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms len_spec


/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeRistrettoPrecomputation`: whether
there are no static points. -/
recall is_empty_spec (self : VartimeRistrettoPrecomputation.«i686-tables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_empty_spec


/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeRistrettoPrecomputation` (static points `self.points`): `none` iff some dynamic point is
`none`; otherwise `∑ s_i • P_i + ∑ d_i • Q_i`, missing static scalars counting as `0` (if no point
is `none`, at most `|self.points|` static scalars and as many dynamic scalars as dynamic points). -/
recall optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option ristretto.RistrettoPoint.«i686-tables») Clause4_IntoIter)
    (self : VartimeRistrettoPrecomputation.«i686-tables») (static_scalars : I)
    (dynamic_scalars : J) (dynamic_points : K)
    (xs : List Clause0_Item) (ss : List scalar.Scalar) (ys : List Clause2_Item)
    (ds : List scalar.Scalar) (qops : List (Option ristretto.RistrettoPoint.«i686-tables»))
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
      ⦃ (r : Option ristretto.RistrettoPoint.«i686-tables») => (none ∈ qops → r = none) ∧
        ∀ qs, qops = qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds qs).sum ∧
          R.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms optional_mixed_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPointi686-tables»
end Curve25519Dalek.ristretto.VartimeRistrettoPrecomputation.«i686-tables».Insts

namespace Curve25519Dalek.ristretto.VartimeRistrettoPrecomputation.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPointx86_64-no-tables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeRistrettoPrecomputation`: a
precomputation of the points the input yields (through `borrow`). -/
recall new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item ristretto.RistrettoPoint.«x86_64-no-tables»)
    (static_points : I) (ys : List Clause0_Item)
    (ps : List ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«x86_64-no-tables») => P' = P ⦄)
      ys ps)
    (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeRistrettoPrecomputation.«x86_64-no-tables») =>
        r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms new_spec


/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeRistrettoPrecomputation`: the number of
static points. -/
recall len_spec (self : VartimeRistrettoPrecomputation.«x86_64-no-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms len_spec


/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeRistrettoPrecomputation`: whether
there are no static points. -/
recall is_empty_spec (self : VartimeRistrettoPrecomputation.«x86_64-no-tables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_empty_spec


/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeRistrettoPrecomputation` (static points `self.points`): `none` iff some dynamic point is
`none`; otherwise `∑ s_i • P_i + ∑ d_i • Q_i`, missing static scalars counting as `0` (if no point
is `none`, at most `|self.points|` static scalars and as many dynamic scalars as dynamic points). -/
recall optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option ristretto.RistrettoPoint.«x86_64-no-tables») Clause4_IntoIter)
    (self : VartimeRistrettoPrecomputation.«x86_64-no-tables») (static_scalars : I)
    (dynamic_scalars : J) (dynamic_points : K)
    (xs : List Clause0_Item) (ss : List scalar.Scalar) (ys : List Clause2_Item)
    (ds : List scalar.Scalar) (qops : List (Option ristretto.RistrettoPoint.«x86_64-no-tables»))
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
      ⦃ (r : Option ristretto.RistrettoPoint.«x86_64-no-tables») => (none ∈ qops → r = none) ∧
        ∀ qs, qops = qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds qs).sum ∧
          R.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms optional_mixed_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPointx86_64-no-tables»
end Curve25519Dalek.ristretto.VartimeRistrettoPrecomputation.«x86_64-no-tables».Insts

namespace Curve25519Dalek.ristretto.VartimeRistrettoPrecomputation.«i686-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPointi686-no-tables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeRistrettoPrecomputation`: a
precomputation of the points the input yields (through `borrow`). -/
recall new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item ristretto.RistrettoPoint.«i686-no-tables»)
    (static_points : I) (ys : List Clause0_Item)
    (ps : List ristretto.RistrettoPoint.«i686-no-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«i686-no-tables») => P' = P ⦄)
      ys ps)
    (hps : ∀ P ∈ ps, P.IsBounded)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeRistrettoPrecomputation.«i686-no-tables») =>
        r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms new_spec


/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeRistrettoPrecomputation`: the number of
static points. -/
recall len_spec (self : VartimeRistrettoPrecomputation.«i686-no-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms len_spec


/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeRistrettoPrecomputation`: whether
there are no static points. -/
recall is_empty_spec (self : VartimeRistrettoPrecomputation.«i686-no-tables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms is_empty_spec


/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeRistrettoPrecomputation` (static points `self.points`): `none` iff some dynamic point is
`none`; otherwise `∑ s_i • P_i + ∑ d_i • Q_i`, missing static scalars counting as `0` (if no point
is `none`, at most `|self.points|` static scalars and as many dynamic scalars as dynamic points). -/
recall optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option ristretto.RistrettoPoint.«i686-no-tables») Clause4_IntoIter)
    (self : VartimeRistrettoPrecomputation.«i686-no-tables») (static_scalars : I)
    (dynamic_scalars : J) (dynamic_points : K)
    (xs : List Clause0_Item) (ss : List scalar.Scalar) (ys : List Clause2_Item)
    (ds : List scalar.Scalar) (qops : List (Option ristretto.RistrettoPoint.«i686-no-tables»))
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
      ⦃ (r : Option ristretto.RistrettoPoint.«i686-no-tables») => (none ∈ qops → r = none) ∧
        ∀ qs, qops = qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds qs).sum ∧
          R.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms optional_mixed_multiscalar_mul_spec

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPointi686-no-tables»
end Curve25519Dalek.ristretto.VartimeRistrettoPrecomputation.«i686-no-tables».Insts

namespace Curve25519Dalek
namespace ristretto.«RistrettoPointx86_64-tables»

/-- `RistrettoPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`). -/
recall vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : ristretto.RistrettoPoint.«x86_64-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.IsBounded) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms vartime_double_scalar_mul_basepoint_spec

end ristretto.«RistrettoPointx86_64-tables»

namespace ristretto.«RistrettoPointi686-tables»

/-- `RistrettoPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`). -/
recall vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : ristretto.RistrettoPoint.«i686-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.IsBounded) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms vartime_double_scalar_mul_basepoint_spec

end ristretto.«RistrettoPointi686-tables»
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.«RistrettoPointx86_64-no-tables»

/-- `RistrettoPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`). -/
recall vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.IsBounded) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms vartime_double_scalar_mul_basepoint_spec

end ristretto.«RistrettoPointx86_64-no-tables»

namespace ristretto.«RistrettoPointi686-no-tables»

/-- `RistrettoPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`). -/
recall vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : ristretto.RistrettoPoint.«i686-no-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.IsBounded) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms vartime_double_scalar_mul_basepoint_spec

end ristretto.«RistrettoPointi686-no-tables»
end Curve25519Dalek

namespace Curve25519Dalek
namespace «Shared0RistrettoBasepointTablex86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-tables»

/-- `Mul<&Scalar> for &RistrettoBasepointTable`: `scalar • self.point` for the table's
point (unreduced, `< 2^255`). -/
recall mul_spec (self : ristretto.RistrettoBasepointTable.«x86_64-tables»)
    (scalar : scalar.Scalar) (hself : self.IsBounded)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-tables»
end «Shared0RistrettoBasepointTablex86_64-tables».Insts

namespace «Shared0RistrettoBasepointTablei686-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPointi686-tables»

/-- `Mul<&Scalar> for &RistrettoBasepointTable`: `scalar • self.point` for the table's
point (unreduced, `< 2^255`). -/
recall mul_spec (self : ristretto.RistrettoBasepointTable.«i686-tables»)
    (scalar : scalar.Scalar) (hself : self.IsBounded)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedBScalarRistrettoPointi686-tables»
end «Shared0RistrettoBasepointTablei686-tables».Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedARistrettoBasepointTablex86_64-tablesRistrettoPointx86_64-tables»

/-- `Mul<&RistrettoBasepointTable> for &Scalar`: as the other order. -/
recall mul_spec (self : scalar.Scalar)
    (basepoint_table : ristretto.RistrettoBasepointTable.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hbasepoint_table : basepoint_table.IsBounded)
    (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedARistrettoBasepointTablex86_64-tablesRistrettoPointx86_64-tables»

namespace «CoreOpsArithMulSharedARistrettoBasepointTablei686-tablesRistrettoPointi686-tables»

/-- `Mul<&RistrettoBasepointTable> for &Scalar`: as the other order. -/
recall mul_spec (self : scalar.Scalar)
    (basepoint_table : ristretto.RistrettoBasepointTable.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hbasepoint_table : basepoint_table.IsBounded)
    (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end «CoreOpsArithMulSharedARistrettoBasepointTablei686-tablesRistrettoPointi686-tables»
end Shared0Scalar.Insts
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.«RistrettoBasepointTablex86_64-tables»

/-- `RistrettoBasepointTable::create`: a table representing `basepoint`. -/
recall create_spec (basepoint : ristretto.RistrettoPoint.«x86_64-tables»)
    (hbasepoint : basepoint.IsBounded) (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : ristretto.RistrettoBasepointTable.«x86_64-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec


/-- `RistrettoBasepointTable::basepoint`: the point the table represents. -/
recall basepoint_spec (self : ristretto.RistrettoBasepointTable.«x86_64-tables»)
    (hself : self.IsBounded) (hP : self.IsTable) :
    basepoint self ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end ristretto.«RistrettoBasepointTablex86_64-tables»

namespace ristretto.«RistrettoBasepointTablei686-tables»

/-- `RistrettoBasepointTable::create`: a table representing `basepoint`. -/
recall create_spec (basepoint : ristretto.RistrettoPoint.«i686-tables»)
    (hbasepoint : basepoint.IsBounded) (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : ristretto.RistrettoBasepointTable.«i686-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms create_spec


/-- `RistrettoBasepointTable::basepoint`: the point the table represents. -/
recall basepoint_spec (self : ristretto.RistrettoBasepointTable.«i686-tables»)
    (hself : self.IsBounded) (hP : self.IsTable) :
    basepoint self ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms basepoint_spec

end ristretto.«RistrettoBasepointTablei686-tables»
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable for RistrettoPoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
recall conditional_select_spec (a b : ristretto.RistrettoPoint.«x86_64-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_select_spec

end ristretto.RistrettoPoint.«x86_64-tables».Insts.SubtleConditionallySelectable

namespace ristretto.RistrettoPoint.«i686-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable for RistrettoPoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
recall conditional_select_spec (a b : ristretto.RistrettoPoint.«i686-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_select_spec

end ristretto.RistrettoPoint.«i686-tables».Insts.SubtleConditionallySelectable
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable for RistrettoPoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
recall conditional_select_spec (a b : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_select_spec

end ristretto.RistrettoPoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable for RistrettoPoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
recall conditional_select_spec (a b : ristretto.RistrettoPoint.«i686-no-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_select_spec

end ristretto.RistrettoPoint.«i686-no-tables».Insts.SubtleConditionallySelectable
end Curve25519Dalek

namespace Curve25519Dalek.ristretto.CompressedRistretto.Insts.ZeroizeZeroize

/-- `Zeroize for CompressedRistretto`: thirty-two zero bytes, the encoding of the neutral
element. -/
recall zeroize_spec (self : CompressedRistretto) :
    zeroize self ⦃ (r : CompressedRistretto) => r.toVector = Ristretto.encodeRep 0 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec

end Curve25519Dalek.ristretto.CompressedRistretto.Insts.ZeroizeZeroize

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-tables».Insts.ZeroizeZeroize

/-- `Zeroize for RistrettoPoint` leaves the neutral element. -/
recall zeroize_spec (self : ristretto.RistrettoPoint.«x86_64-tables») :
    zeroize self ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec

end ristretto.RistrettoPoint.«x86_64-tables».Insts.ZeroizeZeroize

namespace ristretto.RistrettoPoint.«i686-tables».Insts.ZeroizeZeroize

/-- `Zeroize for RistrettoPoint` leaves the neutral element. -/
recall zeroize_spec (self : ristretto.RistrettoPoint.«i686-tables») :
    zeroize self ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec

end ristretto.RistrettoPoint.«i686-tables».Insts.ZeroizeZeroize
end Curve25519Dalek

namespace Curve25519Dalek
namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts.ZeroizeZeroize

/-- `Zeroize for RistrettoPoint` leaves the neutral element. -/
recall zeroize_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») :
    zeroize self ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec

end ristretto.RistrettoPoint.«x86_64-no-tables».Insts.ZeroizeZeroize

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts.ZeroizeZeroize

/-- `Zeroize for RistrettoPoint` leaves the neutral element. -/
recall zeroize_spec (self : ristretto.RistrettoPoint.«i686-no-tables») :
    zeroize self ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec

end ristretto.RistrettoPoint.«i686-no-tables».Insts.ZeroizeZeroize
end Curve25519Dalek

/-! ## `ristretto/elligator.rs` -/

namespace Curve25519Dalek.ristretto.elligator
namespace «RistrettoPointx86_64-tables»

/-- `RistrettoPoint::map_to_curve`: RFC 9496's `MAP` of the 32 bytes (`Ristretto.mapRep`): an even
point (a ristretto255 representative). -/
recall map_to_curve_spec (bytes : Array U8 32#usize) :
    map_to_curve bytes ⦃ (r : RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.mapRep bytes.toVector ∧
        r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms map_to_curve_spec

end «RistrettoPointx86_64-tables»

namespace «RistrettoPointi686-tables»

/-- `RistrettoPoint::map_to_curve`: RFC 9496's `MAP` of the 32 bytes (`Ristretto.mapRep`): an even
point (a ristretto255 representative). -/
recall map_to_curve_spec (bytes : Array U8 32#usize) :
    map_to_curve bytes ⦃ (r : RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.mapRep bytes.toVector ∧
        r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms map_to_curve_spec

end «RistrettoPointi686-tables»
end Curve25519Dalek.ristretto.elligator

namespace Curve25519Dalek.ristretto.elligator
namespace «RistrettoPointx86_64-no-tables»

/-- `RistrettoPoint::map_to_curve`: RFC 9496's `MAP` of the 32 bytes (`Ristretto.mapRep`): an even
point (a ristretto255 representative). -/
recall map_to_curve_spec (bytes : Array U8 32#usize) :
    map_to_curve bytes ⦃ (r : RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.mapRep bytes.toVector ∧
        r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms map_to_curve_spec

end «RistrettoPointx86_64-no-tables»

namespace «RistrettoPointi686-no-tables»

/-- `RistrettoPoint::map_to_curve`: RFC 9496's `MAP` of the 32 bytes (`Ristretto.mapRep`): an even
point (a ristretto255 representative). -/
recall map_to_curve_spec (bytes : Array U8 32#usize) :
    map_to_curve bytes ⦃ (r : RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.mapRep bytes.toVector ∧
        r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms map_to_curve_spec

end «RistrettoPointi686-no-tables»
end Curve25519Dalek.ristretto.elligator
