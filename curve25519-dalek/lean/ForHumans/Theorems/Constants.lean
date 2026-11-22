/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import ForHumans.Specs.Representation.Array
import Proofs -- shake: keep
public import ForHumans.Specs.Edwards
public import ForHumans.Specs.Montgomery
public import ForHumans.Specs.Representation.Edwards
public import ForHumans.Specs.Representation.Montgomery
public import ForHumans.Specs.Ristretto
public import ForHumans.Specs.X25519
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP Curve25519Dalek
open curve25519 (Ristretto.encodeRep X25519 basepoint decodeUCoordinate edwards encode
    encodeUCoordinate montgomery montgomeryBasepoint torsion8)

namespace Theorems.constants

/-- `ED25519_BASEPOINT_COMPRESSED`: RFC 8032's encoding of the basepoint. -/
theorem ED25519_BASEPOINT_COMPRESSED :
    constants.ED25519_BASEPOINT_COMPRESSED.toVector = encode basepoint :=
  constants.ED25519_BASEPOINT_COMPRESSED_spec

/-- `X25519_BASEPOINT`: RFC 7748's encoding of the `u`-coordinate `9` of the Montgomery basepoint.
-/
theorem X25519_BASEPOINT :
    constants.X25519_BASEPOINT.toVector = encodeUCoordinate montgomeryBasepoint.u :=
  constants.X25519_BASEPOINT_spec

/-- `RISTRETTO_BASEPOINT_COMPRESSED`: RFC 9496's encoding of the basepoint. -/
theorem RISTRETTO_BASEPOINT_COMPRESSED :
    constants.RISTRETTO_BASEPOINT_COMPRESSED.toVector = Ristretto.encodeRep basepoint :=
  constants.RISTRETTO_BASEPOINT_COMPRESSED_spec

/-- `X25519_LOW_ORDER_POINTS`: a point is sent to `0` by X25519 for every scalar iff it is equal to
one of the seven points as a `MontgomeryPoint` ("The output of any scalar multiplied by these points
is zero"; true for clamped scalars, which is what X25519 uses; and no other point has this
property). This is equality with `==` (`PartialEq`, which compares the decoded coordinates,
`decodeUCoordinate`), not equality of the bytes: other encodings of the same coordinates are sent to
`0` too. In particular each of the seven points is sent to `0` (take `Q` to be the point). -/
theorem X25519_LOW_ORDER_POINTS (Q : montgomery.MontgomeryPoint) :
    (∀ k : Vector UInt8 32, X25519 k Q.toVector = encodeUCoordinate 0) ↔
      ∃ i : Fin 7, decodeUCoordinate Q.toVector =
        decodeUCoordinate constants.X25519_LOW_ORDER_POINTS[i.val]!.toVector :=
  constants.X25519_LOW_ORDER_POINTS_spec Q

end Theorems.constants

-- BEGIN PER-CONFIG
namespace Theorems.constants.«64bit-tables»

/-- `ED25519_BASEPOINT_POINT` represents the basepoint. -/
theorem ED25519_BASEPOINT_POINT :
    backend.serial.u64.constants.ED25519_BASEPOINT_POINT.«64bit-tables»
      ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
        r.OnCurve ∧ r.toPoint = basepoint ∧ r.IsBounded ⦄ :=
  backend.serial.u64.constants.«64bit-tables».ED25519_BASEPOINT_POINT_spec

/-- `ED25519_BASEPOINT_128_POINT` represents `2^128 • B`. -/
theorem ED25519_BASEPOINT_128_POINT :
    backend.serial.u64.constants.ED25519_BASEPOINT_128_POINT.«64bit-tables»
      ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
        r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint ∧ r.IsBounded ⦄ :=
  backend.serial.u64.constants.«64bit-tables».ED25519_BASEPOINT_128_POINT_spec

/-- `EIGHT_TORSION`: entry `i` represents `i • torsion8`. -/
theorem EIGHT_TORSION :
    backend.serial.u64.constants.EIGHT_TORSION.«64bit-tables»
      ⦃ (r : Array edwards.EdwardsPoint.«64bit-tables» 8#usize) =>
        ∀ i : Fin 8, r[i.val]!.OnCurve ∧ r[i.val]!.toPoint = (i : ℕ) • torsion8 ∧
          r[i.val]!.IsBounded ⦄ :=
  backend.serial.u64.constants.«64bit-tables».EIGHT_TORSION_spec

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative). -/
theorem RISTRETTO_BASEPOINT_POINT :
    constants.RISTRETTO_BASEPOINT_POINT.«64bit-tables»
      ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
        r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.IsBounded ⦄ :=
  constants.«64bit-tables».RISTRETTO_BASEPOINT_POINT_spec

-- BEGIN TABLES-ONLY
/-- `ED25519_BASEPOINT_TABLE`: a table representing the basepoint. -/
theorem ED25519_BASEPOINT_TABLE :
    backend.serial.u64.constants.ED25519_BASEPOINT_TABLE
      ⦃ (r : edwards.EdwardsBasepointTable.«64bit-tables») =>
        r.IsTable ∧ r.point = basepoint ∧ r.IsBounded ⦄ :=
  backend.serial.u64.constants.ED25519_BASEPOINT_TABLE_spec

/-- `RISTRETTO_BASEPOINT_TABLE`: a table representing the basepoint. -/
theorem RISTRETTO_BASEPOINT_TABLE :
    constants.RISTRETTO_BASEPOINT_TABLE.«64bit-tables»
      ⦃ (r : ristretto.RistrettoBasepointTable.«64bit-tables») =>
        r.IsTable ∧ r.point = basepoint ∧ r.IsBounded ⦄ :=
  constants.«64bit-tables».RISTRETTO_BASEPOINT_TABLE_spec
-- END TABLES-ONLY

end Theorems.constants.«64bit-tables»
-- END PER-CONFIG
