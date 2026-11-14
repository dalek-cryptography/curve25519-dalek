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
import Proofs.Helpers.Variants
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

The public items of `montgomery.rs`, in its order.

A `MontgomeryPoint` is specified through its bytes as a `Vector UInt8 32` (`toVector`), the byte
strings of RFC 7748: inputs through the `u`-coordinate they encode (`decodeUCoordinate`), results
as canonical encodings (`encodeUCoordinate`). The scalar multiplications are RFC 7748's ladder on
curve25519, which computes `u(n • Q)` on the curve or its twist (`MontgomeryModel.ladder_eq_xMul`).

`to_edwards` depends on the configuration: it is stated at the end, for `x86_64-tables`; the other
configurations' copies are generated in `Specs/Montgomery/`.

Definitions used: `Array.toVector` (`ToAeneas/Array.lean`), `Scalar.asNat` (`Defs/Scalar.lean`),
`EdwardsPoint.toPoint`, `OnCurve`, `IsBounded` (`Defs/Edwards.lean`), `Iterator.Yields`
(`ToAeneas/Iterator.lean`), `curve25519.decodeUCoordinate`, `encodeUCoordinate`, `X25519`
(`Curve25519/X25519.lean`), `montgomeryBasepoint` (`Curve25519/Montgomery.lean`),
`curve25519.decodeLenient` (`Curve25519/Edwards/Encoding.lean`), `montgomery.ladder`,
`montgomery.ladderBits` (`Defs/Montgomery.lean`), `subtle.Choice.IsValid` (`Subtle/`).

Not translated: `Debug`, `Hash`, the `serde` impls. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 Curve25519Dalek
open Curve25519Dalek.montgomery (MontgomeryPoint)
open Curve25519Dalek.scalar (Scalar)

namespace Specs.montgomery.MontgomeryPoint

/-- `Default`: thirty-two zero bytes, the encoding of `u = 0`. -/
theorem default :
    MontgomeryPoint.Insts.CoreDefaultDefault.default ⦃ (r : MontgomeryPoint) =>
      r.toVector = encodeUCoordinate 0 ⦄ :=
  MontgomeryPoint.Insts.CoreDefaultDefault.default_spec

/-- `ConstantTimeEq`: equality of the encoded `u`-coordinates (bit `255` masked, reduced modulo
`p`). -/
theorem ct_eq (P Q : MontgomeryPoint) :
    MontgomeryPoint.Insts.SubtleConstantTimeEq.ct_eq P Q ⦃ (r : subtle.Choice) => r.IsValid ∧
      (r = 1#u8 ↔ decodeUCoordinate P.toVector = decodeUCoordinate Q.toVector) ⦄ :=
  MontgomeryPoint.Insts.SubtleConstantTimeEq.ct_eq_spec P Q

/-- `ConditionallySelectable`: `a` if `choice = 0`, `b` if `choice = 1`. -/
theorem conditional_select (a b : MontgomeryPoint) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_select a b choice
      ⦃ (r : MontgomeryPoint) => (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_select_spec a b choice hchoice

/-- `PartialEq`: equality of the encoded `u`-coordinates. -/
theorem eq (P Q : MontgomeryPoint) :
    MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint.eq P Q ⦃ (r : Bool) =>
      r = true ↔ decodeUCoordinate P.toVector = decodeUCoordinate Q.toVector ⦄ :=
  MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint.eq_spec P Q

/-- `Identity`: thirty-two zero bytes, the encoding of `u = 0`: the point `(0, 0)` of order `2`,
not the neutral element (`u = 0` is also what `ProjectivePoint::as_affine` returns for the point
at infinity). -/
theorem identity :
    MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity.identity ⦃ (r : MontgomeryPoint) =>
      r.toVector = encodeUCoordinate 0 ⦄ :=
  MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity.identity_spec

/-- `Zeroize`: thirty-two zero bytes, the encoding of `u = 0`. -/
theorem zeroize (P : MontgomeryPoint) :
    MontgomeryPoint.Insts.ZeroizeZeroize.zeroize P ⦃ (r : MontgomeryPoint) =>
      r.toVector = encodeUCoordinate 0 ⦄ :=
  MontgomeryPoint.Insts.ZeroizeZeroize.zeroize_spec P

/-- `mul_base`: the `u`-coordinate of `s • B` on the Montgomery model (`s` unreduced, `< 2^255`),
encoded canonically. -/
theorem mul_base (s : Scalar) (hs : s.asNat < 2 ^ 255) :
    MontgomeryPoint.mul_base s ⦃ (r : MontgomeryPoint) =>
      r.toVector = encodeUCoordinate (s.asNat • montgomeryBasepoint).u ⦄ :=
  MontgomeryPoint.mul_base_spec s hs

/-- `mul_clamped`: RFC 7748 `X25519(bytes, P)`. The properties of `X25519` (Diffie–Hellman
agreement, meaning on the curve, small-subgroup safety) are proved in `Curve25519/X25519.lean`
and `Curve25519/Montgomery.lean`; on `X25519_BASEPOINT` it agrees with `mul_base_clamped`
(`mul_clamped_basepoint`, `Proofs/Montgomery/MulClamped.lean`). -/
theorem mul_clamped (P : MontgomeryPoint) (bytes : Array U8 32#usize) :
    MontgomeryPoint.mul_clamped P bytes ⦃ (r : MontgomeryPoint) =>
      r.toVector = X25519 bytes.toVector P.toVector ⦄ :=
  MontgomeryPoint.mul_clamped_spec P bytes

/-- `mul_base_clamped`: RFC 7748 `X25519(bytes, 9)`. -/
theorem mul_base_clamped (bytes : Array U8 32#usize) :
    MontgomeryPoint.mul_base_clamped bytes ⦃ (r : MontgomeryPoint) =>
      r.toVector = X25519 bytes.toVector (encodeUCoordinate 9) ⦄ :=
  MontgomeryPoint.mul_base_clamped_spec bytes

/-- `mul_bits_be`: the RFC 7748 ladder over the bits `bs` the iterator yields, most significant
first, encoded canonically. This is scalar multiplication: on the coordinate of a point `Q` of the
curve or of its twist, the result is the coordinate of `n • Q` for the integer `n` with the bits
`bs` (`mul_bits_be_nsmul`, `mul_bits_be_nsmul_twist`, `Proofs/Montgomery/MulBitsBe.lean`). -/
theorem mul_bits_be {T0 : Type} (inst : core.iter.traits.iterator.Iterator T0 Bool)
    (P : MontgomeryPoint) (bits : T0) (bs : List Bool) (hbits : inst.Yields bits bs) :
    MontgomeryPoint.mul_bits_be inst P bits ⦃ (r : MontgomeryPoint) =>
      r.toVector = encodeUCoordinate (montgomery.ladderBits bs (decodeUCoordinate P.toVector)) ⦄ :=
  MontgomeryPoint.mul_bits_be_spec inst P bits bs hbits

/-- `as_bytes`: the 32 bytes themselves. -/
theorem as_bytes (P : MontgomeryPoint) :
    MontgomeryPoint.as_bytes P ⦃ (r : Array U8 32#usize) => r = P ⦄ :=
  MontgomeryPoint.as_bytes_spec P

/-- `to_bytes`: the 32 bytes themselves. -/
theorem to_bytes (P : MontgomeryPoint) :
    MontgomeryPoint.to_bytes P ⦃ (r : Array U8 32#usize) => r = P ⦄ :=
  MontgomeryPoint.to_bytes_spec P

/-- `Mul<Scalar> for MontgomeryPoint` and `MulAssign<Scalar>`: the RFC 7748 ladder on the low `255`
bits of the scalar, encoded canonically. The ladder computes `u(n • Q)` on the curve or its twist
(`MontgomeryModel.ladder_eq_xMul`). -/
theorem mul (P : MontgomeryPoint) (s : Scalar) :
    ∀ mul ∈ [
        Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint.mul, -- &P * &s
        MontgomeryPoint.Insts.CoreOpsArithMulSharedBScalarMontgomeryPoint.mul, -- P * &s
        SharedAMontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint.mul, -- &P * s
        MontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint.mul, -- P * s
        MontgomeryPoint.Insts.CoreOpsArithMulAssignShared0Scalar.mul_assign, -- P *= &s
        MontgomeryPoint.Insts.CoreOpsArithMulAssignScalar.mul_assign], -- P *= s
      mul P s ⦃ (r : MontgomeryPoint) =>
        r.toVector = encodeUCoordinate
          (montgomery.ladder 255 (s.asNat % 2 ^ 255) (decodeUCoordinate P.toVector)) ⦄ := by
  variants [Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint.mul_spec]

/-- `Mul<MontgomeryPoint> for Scalar`: as `P * s`. -/
theorem mul_left (s : Scalar) (P : MontgomeryPoint) :
    ∀ mul ∈ [
        Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint.mul, -- &s * &P
        Scalar.Insts.CoreOpsArithMulSharedBMontgomeryPointMontgomeryPoint.mul, -- s * &P
        SharedAScalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint.mul, -- &s * P
        Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint.mul], -- s * P
      mul s P ⦃ (r : MontgomeryPoint) =>
        r.toVector = encodeUCoordinate
          (montgomery.ladder 255 (s.asNat % 2 ^ 255) (decodeUCoordinate P.toVector)) ⦄ := by
  variants [Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint.mul_spec]

end Specs.montgomery.MontgomeryPoint

/-! ## Per configuration -/

-- BEGIN PER-CONFIG
namespace Specs.montgomery.«x86_64-tables».MontgomeryPoint

/-- `to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of the bytes of `y = (u - 1) / (u + 1)` with
`y_bytes[31] ^= sign << 7`. -/
theorem to_edwards (P : MontgomeryPoint) (sign : U8) :
    MontgomeryPoint.to_edwards.«x86_64-tables» P sign
      ⦃ (r : Option (edwards.EdwardsPoint.«x86_64-tables»)) =>
        let u := decodeUCoordinate P.toVector
        r.map edwards.EdwardsPoint.«x86_64-tables».toPoint =
          (if u = -1 then none
          else curve25519.decodeLenient
            ((encodeUCoordinate ((u - 1) / (u + 1))).set 31
              ((encodeUCoordinate ((u - 1) / (u + 1)))[31] ^^^
                (UInt8.ofNat sign.val <<< 7)))) ∧
        ∀ q, r = some q → q.OnCurve ∧ q.IsBounded ⦄ :=
  MontgomeryPoint.«x86_64-tables».to_edwards_spec P sign

end Specs.montgomery.«x86_64-tables».MontgomeryPoint
-- END PER-CONFIG
