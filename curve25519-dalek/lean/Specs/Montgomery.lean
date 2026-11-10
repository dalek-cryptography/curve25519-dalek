/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Encoding
public import Curve25519.Montgomery
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import ToAeneas.Iterator
public import Defs.Montgomery
public import Defs.Scalar
public import Subtle
import Proofs.Montgomery.AsBytes
import Proofs.Montgomery.ConditionalSelect
import Proofs.Montgomery.CtEq
import Proofs.Montgomery.Default
import Proofs.Montgomery.Eq
import Proofs.Montgomery.Identity
import Proofs.Montgomery.Mul
import Proofs.Montgomery.MulAssign
import Proofs.Montgomery.MulBase
import Proofs.Montgomery.MulBaseClamped
import Proofs.Montgomery.MulBitsBe
import Proofs.Montgomery.MulClamped
import Proofs.Montgomery.ToBytes
import Proofs.Montgomery.ToEdwards
import Proofs.Montgomery.Zeroize
public section

/-! # Specs of `src/montgomery.rs`

The public items of `montgomery.rs`, in its order, restated with `recall` from `Proofs/Montgomery/`,
with the axioms each proof uses; `to_edwards` has one statement per configuration (`x86_64`/`i686`,
with or without precomputed tables).

A `MontgomeryPoint` is specified through its bytes as a `Vector UInt8 32` (`toVector`), the byte
strings of RFC 7748: inputs through the `u`-coordinate they encode (`decodeUCoordinate`), results
as canonical encodings (`encodeUCoordinate`). The scalar multiplications are RFC 7748's
ladder on curve25519, which computes `u(n • Q)` on the curve or its twist
(`MontgomeryModel.ladder_eq_xMul`).

Definitions used: `Array.toVector` (`ToAeneas/Array.lean`), `Scalar.asNat` (`Defs/Scalar.lean`),
`EdwardsPoint.toPoint`, `OnCurve`, `IsBounded` (`Defs/Edwards.lean`), `Iterator.Yields`
(`ToAeneas/Iterator.lean`), `curve25519.decodeUCoordinate`, `encodeUCoordinate`, `encodeU`,
`X25519` (`Curve25519/X25519.lean`), `encodeLittleEndian` (`Curve25519/Bytes.lean`),
`montgomeryBasepoint` (`Curve25519/Montgomery.lean`), `curve25519.decodeLenient`
(`Curve25519/Edwards/Encoding.lean`), `MontgomeryModel.ladder`, `MontgomeryModel.ladderBits`
(`EllipticCurve/`), `subtle.Choice.IsValid` (`Subtle/`).

Not translated: `Debug`, `Hash`, the `serde` impls. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open MontgomeryModel (XZ)

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreDefaultDefault

/-- `Default for MontgomeryPoint`: thirty-two zero bytes, the encoding of `u = 0`. -/
recall default_spec :
    default ⦃ (r : MontgomeryPoint) => r.toVector = encodeUCoordinate 0 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreDefaultDefault

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.SubtleConstantTimeEq

/-- `ConstantTimeEq for MontgomeryPoint`: equality of the encoded `u`-coordinates (bit `255`
masked, reduced modulo `p`). -/
recall ct_eq_spec (self other : MontgomeryPoint) :
    ct_eq self other ⦃ (r : subtle.Choice) => r.IsValid ∧
      (r = 1#u8 ↔ decodeUCoordinate self.toVector = decodeUCoordinate other.toVector) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.SubtleConstantTimeEq

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable for MontgomeryPoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
recall conditional_select_spec (a b : MontgomeryPoint) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : MontgomeryPoint) =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_select_spec

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint

/-- `PartialEq for MontgomeryPoint`: equality of the encoded `u`-coordinates. -/
recall eq_spec (self other : MontgomeryPoint) :
    eq self other ⦃ (r : Bool) =>
      r = true ↔ decodeUCoordinate self.toVector = decodeUCoordinate other.toVector ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for MontgomeryPoint`: thirty-two zero bytes, the encoding of `u = 0`: the point
`(0, 0)` of order `2`, not the neutral element (`u = 0` is also what `ProjectivePoint::as_affine`
returns for the point at infinity). -/
recall identity_spec :
    identity ⦃ (r : MontgomeryPoint) => r.toVector = encodeUCoordinate 0 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms identity_spec

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.ZeroizeZeroize

/-- `Zeroize for MontgomeryPoint`: thirty-two zero bytes, the encoding of `u = 0`. -/
recall zeroize_spec (self : MontgomeryPoint) :
    zeroize self ⦃ (r : MontgomeryPoint) => r.toVector = encodeUCoordinate 0 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.ZeroizeZeroize

namespace Curve25519Dalek.montgomery.MontgomeryPoint

/-- `MontgomeryPoint::mul_base`: the `u`-coordinate of `scalar • B` on the Montgomery model
(unreduced, `< 2^255`), encoded canonically. -/
recall mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : MontgomeryPoint) =>
      r.toVector = encodeUCoordinate (scalar.asNat • montgomeryBasepoint).u ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec

/-- `MontgomeryPoint::mul_clamped`: RFC 7748 `X25519(bytes, self)`. The properties of `X25519`
(Diffie–Hellman agreement, meaning on the curve, small-subgroup safety) are proved in
`Curve25519/X25519.lean` and `Curve25519/Montgomery.lean`; on `X25519_BASEPOINT` it agrees with
`mul_base_clamped` (`mul_clamped_basepoint`, `Proofs/Montgomery/MulClamped.lean`). -/
recall mul_clamped_spec (self : MontgomeryPoint) (bytes : Array U8 32#usize) :
    mul_clamped self bytes ⦃ (r : MontgomeryPoint) =>
      r.toVector = X25519 bytes.toVector self.toVector ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_clamped_spec

/-- `MontgomeryPoint::mul_base_clamped`: RFC 7748 `X25519(bytes, 9)`. The properties of `X25519`
are proved in `Curve25519/X25519.lean` and `Curve25519/Montgomery.lean`. -/
recall mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (r : MontgomeryPoint) =>
      r.toVector = X25519 bytes.toVector (encodeUCoordinate 9) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_clamped_spec

/-- `MontgomeryPoint::mul_bits_be`: the RFC 7748 ladder over the bits `bs` the iterator yields,
most significant first, encoded canonically. This is scalar multiplication: on the coordinate of
a point `Q` of the curve or of its twist, the result is the coordinate of `n • Q` for the integer
`n` with the bits `bs` (`mul_bits_be_nsmul`, `mul_bits_be_nsmul_twist`,
`Proofs/Montgomery/MulBitsBe.lean`). -/
recall mul_bits_be_spec {T0 : Type} (inst : core.iter.traits.iterator.Iterator T0 Bool)
    (self : MontgomeryPoint) (bits : T0) (bs : List Bool) (hbits : inst.Yields bits bs) :
    mul_bits_be inst self bits ⦃ (r : MontgomeryPoint) =>
      r.toVector = encodeUCoordinate (montgomery.ladderBits bs (decodeUCoordinate self.toVector)) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_bits_be_spec

/-- `MontgomeryPoint::as_bytes`: the 32 bytes themselves. -/
recall as_bytes_spec (self : MontgomeryPoint) :
    as_bytes self ⦃ (r : Array U8 32#usize) => r = self ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms as_bytes_spec

/-- `MontgomeryPoint::to_bytes`: the 32 bytes themselves. -/
recall to_bytes_spec (self : MontgomeryPoint) :
    to_bytes self ⦃ (r : Array U8 32#usize) => r = self ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_bytes_spec

namespace «x86_64-tables»

/-- `MontgomeryPoint::to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of the bytes of `y = (u - 1) / (u + 1)` with
`y_bytes[31] ^= sign << 7`. -/
recall to_edwards_spec (self : MontgomeryPoint) (sign : U8) :
    to_edwards.«x86_64-tables» self sign
      ⦃ (r : Option (edwards.EdwardsPoint.«x86_64-tables»)) =>
        let u := decodeUCoordinate self.toVector
        r.map edwards.EdwardsPoint.«x86_64-tables».toPoint =
          (if u = -1 then none
          else curve25519.decodeLenient
            ((encodeUCoordinate ((u - 1) / (u + 1))).set 31
              ((encodeUCoordinate ((u - 1) / (u + 1)))[31] ^^^
                (UInt8.ofNat sign.val <<< 7)))) ∧
        ∀ q, r = some q → q.OnCurve ∧ q.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_edwards_spec

end «x86_64-tables»

namespace «i686-tables»

/-- `MontgomeryPoint::to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of the bytes of `y = (u - 1) / (u + 1)` with
`y_bytes[31] ^= sign << 7`. -/
recall to_edwards_spec (self : MontgomeryPoint) (sign : U8) :
    to_edwards.«i686-tables» self sign
      ⦃ (r : Option (edwards.EdwardsPoint.«i686-tables»)) =>
        let u := decodeUCoordinate self.toVector
        r.map edwards.EdwardsPoint.«i686-tables».toPoint =
          (if u = -1 then none
          else curve25519.decodeLenient
            ((encodeUCoordinate ((u - 1) / (u + 1))).set 31
              ((encodeUCoordinate ((u - 1) / (u + 1)))[31] ^^^
                (UInt8.ofNat sign.val <<< 7)))) ∧
        ∀ q, r = some q → q.OnCurve ∧ q.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_edwards_spec

end «i686-tables»

namespace «x86_64-no-tables»

/-- `MontgomeryPoint::to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of the bytes of `y = (u - 1) / (u + 1)` with
`y_bytes[31] ^= sign << 7`. -/
recall to_edwards_spec (self : MontgomeryPoint) (sign : U8) :
    to_edwards.«x86_64-no-tables» self sign
      ⦃ (r : Option (edwards.EdwardsPoint.«x86_64-no-tables»)) =>
        let u := decodeUCoordinate self.toVector
        r.map edwards.EdwardsPoint.«x86_64-no-tables».toPoint =
          (if u = -1 then none
          else curve25519.decodeLenient
            ((encodeUCoordinate ((u - 1) / (u + 1))).set 31
              ((encodeUCoordinate ((u - 1) / (u + 1)))[31] ^^^
                (UInt8.ofNat sign.val <<< 7)))) ∧
        ∀ q, r = some q → q.OnCurve ∧ q.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_edwards_spec

end «x86_64-no-tables»

namespace «i686-no-tables»

/-- `MontgomeryPoint::to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of the bytes of `y = (u - 1) / (u + 1)` with
`y_bytes[31] ^= sign << 7`. -/
recall to_edwards_spec (self : MontgomeryPoint) (sign : U8) :
    to_edwards.«i686-no-tables» self sign
      ⦃ (r : Option (edwards.EdwardsPoint.«i686-no-tables»)) =>
        let u := decodeUCoordinate self.toVector
        r.map edwards.EdwardsPoint.«i686-no-tables».toPoint =
          (if u = -1 then none
          else curve25519.decodeLenient
            ((encodeUCoordinate ((u - 1) / (u + 1))).set 31
              ((encodeUCoordinate ((u - 1) / (u + 1)))[31] ^^^
                (UInt8.ofNat sign.val <<< 7)))) ∧
        ∀ q, r = some q → q.OnCurve ∧ q.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_edwards_spec

end «i686-no-tables»

end Curve25519Dalek.montgomery.MontgomeryPoint

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for MontgomeryPoint`: as `&MontgomeryPoint * &Scalar`. -/
recall mul_assign_spec (self : MontgomeryPoint) (rhs : scalar.Scalar) :
    mul_assign self rhs ⦃ (r : MontgomeryPoint) =>
      r.toVector = encodeUCoordinate
          (montgomery.ladder 255 (rhs.asNat % 2 ^ 255) (decodeUCoordinate self.toVector)) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulAssignScalar

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts
namespace CoreOpsArithMulSharedBScalarMontgomeryPoint

/-- `Mul<&Scalar> for MontgomeryPoint`: as `&MontgomeryPoint * &Scalar`. -/
recall mul_spec (self : montgomery.MontgomeryPoint) (rhs : scalar.Scalar) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.toVector = encodeUCoordinate
          (montgomery.ladder 255 (rhs.asNat % 2 ^ 255) (decodeUCoordinate self.toVector)) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end CoreOpsArithMulSharedBScalarMontgomeryPoint
end Curve25519Dalek.montgomery.MontgomeryPoint.Insts

namespace Curve25519Dalek.SharedAMontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint

/-- `Mul<Scalar> for &MontgomeryPoint`: as `&MontgomeryPoint * &Scalar`. -/
recall mul_spec (self : montgomery.MontgomeryPoint) (rhs : scalar.Scalar) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.toVector = encodeUCoordinate
          (montgomery.ladder 255 (rhs.asNat % 2 ^ 255) (decodeUCoordinate self.toVector)) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.SharedAMontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint

/-- `Mul<Scalar> for MontgomeryPoint`: as `&MontgomeryPoint * &Scalar`. -/
recall mul_spec (self : montgomery.MontgomeryPoint) (rhs : scalar.Scalar) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.toVector = encodeUCoordinate
          (montgomery.ladder 255 (rhs.asNat % 2 ^ 255) (decodeUCoordinate self.toVector)) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBMontgomeryPointMontgomeryPoint

/-- `Mul<&MontgomeryPoint> for Scalar`: as `&MontgomeryPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : montgomery.MontgomeryPoint) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.toVector = encodeUCoordinate
          (montgomery.ladder 255 (self.asNat % 2 ^ 255) (decodeUCoordinate rhs.toVector)) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBMontgomeryPointMontgomeryPoint

namespace Curve25519Dalek.SharedAScalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint

/-- `Mul<MontgomeryPoint> for &Scalar`: as `&MontgomeryPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : montgomery.MontgomeryPoint) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.toVector = encodeUCoordinate
          (montgomery.ladder 255 (self.asNat % 2 ^ 255) (decodeUCoordinate rhs.toVector)) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.SharedAScalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint

/-- `Mul<MontgomeryPoint> for Scalar`: as `&MontgomeryPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : montgomery.MontgomeryPoint) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.toVector = encodeUCoordinate
          (montgomery.ladder 255 (self.asNat % 2 ^ 255) (decodeUCoordinate rhs.toVector)) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint

namespace Curve25519Dalek.Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint

/-- `Mul<&Scalar> for &MontgomeryPoint`: the RFC 7748 ladder on the low `255` bits of the
scalar, encoded canonically. The ladder computes `u(n • Q)` on the curve or its twist
(`MontgomeryModel.ladder_eq_xMul`). -/
recall mul_spec (self : montgomery.MontgomeryPoint) (scalar : scalar.Scalar) :
    mul self scalar ⦃ (r : montgomery.MontgomeryPoint) =>
      r.toVector = encodeUCoordinate
          (montgomery.ladder 255 (scalar.asNat % 2 ^ 255) (decodeUCoordinate self.toVector)) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulAssignShared0Scalar

/-- `MulAssign<&Scalar> for MontgomeryPoint`: as `&MontgomeryPoint * &Scalar`. -/
recall mul_assign_spec (self : MontgomeryPoint) (scalar : scalar.Scalar) :
    mul_assign self scalar ⦃ (r : MontgomeryPoint) =>
      r.toVector = encodeUCoordinate
          (montgomery.ladder 255 (scalar.asNat % 2 ^ 255) (decodeUCoordinate self.toVector)) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulAssignShared0Scalar

namespace Curve25519Dalek.Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint

/-- `Mul<&MontgomeryPoint> for &Scalar`: as `&MontgomeryPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (point : montgomery.MontgomeryPoint) :
    mul self point ⦃ (r : montgomery.MontgomeryPoint) =>
      r.toVector = encodeUCoordinate
          (montgomery.ladder 255 (self.asNat % 2 ^ 255) (decodeUCoordinate point.toVector)) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint
