/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Montgomery
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Iterator
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

Spec summary: the items of `montgomery.rs` in the crate's public API with their spec statements,
restated with `recall` from the theorems proved in `Proofs/Montgomery/`, and the axioms they
depend on. `ProjectivePoint` and `differential_add_and_double` are private; their specs are in
the proof files.

A `MontgomeryPoint` is 32 bytes; `u` is the `u`-coordinate they encode (RFC 7748
`decodeUCoordinate`: bit `255` masked, reduced modulo `p`), and results are canonical encodings
`encodeU`. The scalar multiplications are stated with RFC 7748's ladder on curve25519
(`montgomery.ladder`, `montgomery.ladderBits`), which computes `u(n • Q)` on the curve and on its
twist (`MontgomeryModel.ladder_eq_xMul`, `MontgomeryModel.ladderBits_eq_xMul`); `mul_clamped` and
`mul_base_clamped` are RFC 7748's `X25519` byte for byte (`x25519`). `Mul` multiplies by the low
`255` bits of the scalar (the code skips bit `255`). Functions that dispatch on the target are
stated for all four targets.

Definitions used: `MontgomeryPoint.asNat`, `MontgomeryPoint.u` (`Defs/Montgomery.lean`),
`curve25519.decodeU`, `encodeU`, `x25519`, `montgomeryBasepoint`, `MontgomeryModel.ladder`,
`MontgomeryModel.ladderBits` (`Curve25519/`, `EllipticCurve/`), `decodeLenient`,
`EdwardsPoint.toPoint`, `OnCurve`, `LimbsLt` (`Defs/Edwards.lean`), `Iterator.Yields`
(`Defs/Iterator.lean`), `subtle.Choice.IsValid`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open MontgomeryModel (XZ)

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreDefaultDefault

/-- `Default for MontgomeryPoint`: thirty-two zero bytes, the encoding of `u = 0`. -/
recall default_spec :
    default ⦃ (r : MontgomeryPoint) => r.asNat = 0 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreDefaultDefault

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.SubtleConstantTimeEq

/-- `ConstantTimeEq for MontgomeryPoint`: equality of the encoded `u`-coordinates (bit `255`
masked, reduced modulo `p`; x86_64 targets). -/
recall ct_eq_spec (self other : MontgomeryPoint) :
    ct_eq self other ⦃ (c : subtle.Choice) => c.IsValid ∧ (c = 1#u8 ↔ self.u = other.u) ⦄

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

/-- `PartialEq for MontgomeryPoint`: equality of the encoded `u`-coordinates (x86_64 targets). -/
recall eq_spec (self other : MontgomeryPoint) :
    eq self other ⦃ (b : Bool) => b = true ↔ self.u = other.u ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for MontgomeryPoint`: thirty-two zero bytes, the encoding of `u = 0`. -/
recall identity_spec :
    identity ⦃ (r : MontgomeryPoint) => r.asNat = 0 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms identity_spec

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.ZeroizeZeroize

/-- `Zeroize for MontgomeryPoint`: thirty-two zero bytes, the encoding of `u = 0`. -/
recall zeroize_spec_point (self : MontgomeryPoint) :
    zeroize self ⦃ (r : MontgomeryPoint) => r.asNat = 0 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec_point

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.ZeroizeZeroize

namespace Curve25519Dalek.montgomery.MontgomeryPoint

/-- `MontgomeryPoint::mul_base`: the `u`-coordinate of `scalar • B` on the Montgomery model
(unreduced, `< 2^255`), encoded canonically (x86_64 targets). -/
recall mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (scalar.asNat • montgomeryBasepoint).u ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_spec


/-- `MontgomeryPoint::mul_clamped`: RFC 7748 `X25519(bytes, self)`. -/
recall mul_clamped_spec (self : MontgomeryPoint) (bytes : Array U8 32#usize) :
    mul_clamped self bytes ⦃ (r : MontgomeryPoint) =>
      r.asNat = x25519 (bytes.asNat 8) self.asNat ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_clamped_spec


/-- `MontgomeryPoint::mul_base_clamped`: RFC 7748 `X25519(bytes, 9)`. -/
recall mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (r : MontgomeryPoint) =>
      r.asNat = x25519 (bytes.asNat 8) 9 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_base_clamped_spec


/-- `MontgomeryPoint::mul_bits_be`: the RFC 7748 ladder over the bits `bs` the iterator yields,
most significant first, encoded canonically (x86_64 targets). -/
recall mul_bits_be_spec {T0 : Type} (inst : core.iter.traits.iterator.Iterator T0 Bool)
    (self : MontgomeryPoint) (bits : T0) (bs : List Bool) (hbits : inst.Yields bits bs) :
    mul_bits_be inst self bits ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladderBits bs self.u) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle, RustAx.zeroize] -/
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


/-- `MontgomeryPoint::to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of `y = (u - 1) / (u + 1)` with sign bit `sign mod 2`. -/
recall to_edwards.«x86_64-tables_spec» (self : MontgomeryPoint) (sign : U8) :
    to_edwards.«x86_64-tables» self sign ⦃ (r : Option (edwards.EdwardsPoint.«x86_64-tables»)) =>
      (self.u = -1 → r = none) ∧
      (self.u ≠ -1 → r.map edwards.EdwardsPoint.«x86_64-tables».toPoint =
        Curve25519Dalek.edwards.decodeLenient (encodeU ((self.u - 1) / (self.u + 1)) + 2 ^ 255 *
            (sign.val % 2))) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 52 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_edwards.«x86_64-tables_spec»


/-- `MontgomeryPoint::to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of `y = (u - 1) / (u + 1)` with sign bit `sign mod 2`. -/
recall to_edwards.«i686-tables_spec» (self : MontgomeryPoint) (sign : U8) :
    to_edwards.«i686-tables» self sign ⦃ (r : Option (edwards.EdwardsPoint.«i686-tables»)) =>
      (self.u = -1 → r = none) ∧
      (self.u ≠ -1 → r.map edwards.EdwardsPoint.«i686-tables».toPoint =
        Curve25519Dalek.edwards.decodeLenient (encodeU ((self.u - 1) / (self.u + 1)) + 2 ^ 255 *
            (sign.val % 2))) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 26 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms to_edwards.«i686-tables_spec»


/-- `MontgomeryPoint::to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of `y = (u - 1) / (u + 1)` with sign bit `sign mod 2`. -/
recall to_edwards.«x86_64-no-tables_spec» (self : MontgomeryPoint) (sign : U8) :
    to_edwards.«x86_64-no-tables» self sign ⦃ (r : Option (edwards.EdwardsPoint.«x86_64-no-tables»))
        =>
      (self.u = -1 → r = none) ∧
      (self.u ≠ -1 → r.map edwards.EdwardsPoint.«x86_64-no-tables».toPoint =
        Curve25519Dalek.edwards.decodeLenient (encodeU ((self.u - 1) / (self.u + 1)) + 2 ^ 255 *
            (sign.val % 2))) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 52 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms to_edwards.«x86_64-no-tables_spec»


/-- `MontgomeryPoint::to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of `y = (u - 1) / (u + 1)` with sign bit `sign mod 2`. -/
recall to_edwards.«i686-no-tables_spec» (self : MontgomeryPoint) (sign : U8) :
    to_edwards.«i686-no-tables» self sign ⦃ (r : Option (edwards.EdwardsPoint.«i686-no-tables»))
        =>
      (self.u = -1 → r = none) ∧
      (self.u ≠ -1 → r.map edwards.EdwardsPoint.«i686-no-tables».toPoint =
        Curve25519Dalek.edwards.decodeLenient (encodeU ((self.u - 1) / (self.u + 1)) + 2 ^ 255 *
            (sign.val % 2))) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 26 ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms to_edwards.«i686-no-tables_spec»

end Curve25519Dalek.montgomery.MontgomeryPoint

namespace Curve25519Dalek.Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint

/-- `Mul<&Scalar> for &MontgomeryPoint`: the RFC 7748 ladder on the low `255` bits of the
scalar, encoded canonically (x86_64 targets). -/
recall mul_spec (self : montgomery.MontgomeryPoint) (s : scalar.Scalar) :
    mul self s ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (s.asNat % 2 ^ 255) self.u) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulAssignShared0Scalar

/-- `MulAssign<&Scalar> for MontgomeryPoint`: as `&MontgomeryPoint * &Scalar`. -/
recall mul_assign_spec (self : MontgomeryPoint) (scalar : scalar.Scalar) :
    mul_assign self scalar ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (scalar.asNat % 2 ^ 255) self.u) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulAssignShared0Scalar

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts
namespace CoreOpsArithMulSharedBScalarMontgomeryPoint

/-- `Mul<Scalar> for MontgomeryPoint` (by-value forms): as `&MontgomeryPoint * &Scalar`. -/
recall mul_spec (self : montgomery.MontgomeryPoint) (rhs : scalar.Scalar) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (rhs.asNat % 2 ^ 255) self.u) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end CoreOpsArithMulSharedBScalarMontgomeryPoint
end Curve25519Dalek.montgomery.MontgomeryPoint.Insts

namespace Curve25519Dalek.SharedAMontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint

/-- `Mul<Scalar> for MontgomeryPoint` (by-value forms): as `&MontgomeryPoint * &Scalar`. -/
recall mul_spec (self : montgomery.MontgomeryPoint) (rhs : scalar.Scalar) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (rhs.asNat % 2 ^ 255) self.u) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.SharedAMontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint

/-- `Mul<Scalar> for MontgomeryPoint` (by-value forms): as `&MontgomeryPoint * &Scalar`. -/
recall mul_spec (self : montgomery.MontgomeryPoint) (rhs : scalar.Scalar) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (rhs.asNat % 2 ^ 255) self.u) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint

namespace Curve25519Dalek.Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint

/-- `Mul<MontgomeryPoint> for Scalar`: as `&MontgomeryPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (point : montgomery.MontgomeryPoint) :
    mul self point ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (self.asNat % 2 ^ 255) point.u) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBMontgomeryPointMontgomeryPoint

/-- `Mul<MontgomeryPoint> for Scalar`: as `&MontgomeryPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : montgomery.MontgomeryPoint) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (self.asNat % 2 ^ 255) rhs.u) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBMontgomeryPointMontgomeryPoint

namespace Curve25519Dalek.SharedAScalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint

/-- `Mul<MontgomeryPoint> for Scalar`: as `&MontgomeryPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : montgomery.MontgomeryPoint) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (self.asNat % 2 ^ 255) rhs.u) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.SharedAScalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint

/-- `Mul<MontgomeryPoint> for Scalar`: as `&MontgomeryPoint * &Scalar`. -/
recall mul_spec (self : scalar.Scalar) (rhs : montgomery.MontgomeryPoint) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (self.asNat % 2 ^ 255) rhs.u) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for MontgomeryPoint`: as `&MontgomeryPoint * &Scalar`. -/
recall mul_assign_spec (self : MontgomeryPoint) (rhs : scalar.Scalar) :
    mul_assign self rhs ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (rhs.asNat % 2 ^ 255) self.u) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.core, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulAssignScalar
