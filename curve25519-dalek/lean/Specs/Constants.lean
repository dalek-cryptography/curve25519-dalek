/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519.Edwards.Encoding
public import Curve25519.Edwards.Torsion
public import Curve25519.Montgomery
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Curve25519.Ristretto.Encoding
public import Defs.Montgomery
public import Defs.Ristretto
public import Defs.ScalarMul
import Proofs.Backend.Serial.U64.Constants.Ed25519BasepointPoint
import Proofs.Backend.Serial.U64.Constants.Ed25519Basepoint128Point
import Proofs.Backend.Serial.U64.Constants.Ed25519BasepointTable
import Proofs.Backend.Serial.U64.Constants.EightTorsion
import Proofs.Constants.Ed25519BasepointCompressed
import Proofs.Constants.RistrettoBasepoint
import Proofs.Constants.X25519Basepoint
import Proofs.Constants.X25519LowOrderPoints
import Proofs.Backend.Serial.U32.Constants.Ed25519BasepointPoint
import Proofs.Backend.Serial.U32.Constants.Ed25519Basepoint128Point
import Proofs.Backend.Serial.U32.Constants.Ed25519BasepointTable
import Proofs.Backend.Serial.U32.Constants.EightTorsion
public section

/-! # Specs of `src/constants.rs`

Spec summary: the public point constants of `constants.rs` with their spec statements, restated
with `recall` from the theorems proved in `Proofs/`, and the axioms they depend on. Items appear
in the order of `constants.rs`, starting with the constants it re-exports from the backend
(`backend/serial/u64/constants.rs`, `backend/serial/u32/constants.rs`); those are
per-configuration, so each has four statements.

The tables `ED25519_BASEPOINT_TABLE` and `RISTRETTO_BASEPOINT_TABLE` exist only with precomputed
tables (`x86_64-tables`, `i686-tables`). Not restated here: `BASEPOINT_ORDER` (`pub(crate)`, proved
in `Proofs/Constants/BasepointOrder.lean`).

The tables are stated with `IsTable` (entry `(i, j)` is on the curve and is
`(j + 1) • 2^(8 i) • t.point`, the invariant of the Rust type) and `t.point = basepoint`.

Definitions used: Mathlib's `Even`, `EdwardsPoint.toPoint`, `OnCurve`, `IsBounded`,
the tables' `point`, `IsTable` and `IsBounded` (`Defs/Edwards.lean`), `curve25519.basepoint`
(`Curve25519/Edwards/Basepoint.lean`), `curve25519.encode` (`Curve25519/Edwards/Encoding.lean`),
`curve25519.torsion8` (`Curve25519/Edwards/Torsion.lean`), `curve25519.montgomeryBasepoint`
(`Curve25519/Montgomery.lean`), `curve25519.decodeUCoordinate`, `encodeUCoordinate`, `X25519`
(`Curve25519/X25519.lean`), `Array.toVector` (`ToAeneas/Array.lean`),
`Ristretto.encodeRep` (`Curve25519/Ristretto/`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel

namespace Curve25519Dalek.backend.serial.u64.constants
namespace «x86_64-tables»

/-- `ED25519_BASEPOINT_POINT` represents the basepoint. -/
recall ED25519_BASEPOINT_POINT_spec :
    ED25519_BASEPOINT_POINT.«x86_64-tables» ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_POINT_spec

end «x86_64-tables»

end Curve25519Dalek.backend.serial.u64.constants

namespace Curve25519Dalek.backend.serial.u32.constants
namespace «i686-tables»

/-- `ED25519_BASEPOINT_POINT` represents the basepoint. -/
recall ED25519_BASEPOINT_POINT_spec :
    ED25519_BASEPOINT_POINT.«i686-tables» ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_POINT_spec

end «i686-tables»
end Curve25519Dalek.backend.serial.u32.constants


namespace Curve25519Dalek.backend.serial.u64.constants
namespace «x86_64-no-tables»

/-- `ED25519_BASEPOINT_POINT` represents the basepoint. -/
recall ED25519_BASEPOINT_POINT_spec :
    ED25519_BASEPOINT_POINT.«x86_64-no-tables» ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_POINT_spec

end «x86_64-no-tables»

end Curve25519Dalek.backend.serial.u64.constants

namespace Curve25519Dalek.backend.serial.u32.constants
namespace «i686-no-tables»

/-- `ED25519_BASEPOINT_POINT` represents the basepoint. -/
recall ED25519_BASEPOINT_POINT_spec :
    ED25519_BASEPOINT_POINT.«i686-no-tables» ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_POINT_spec

end «i686-no-tables»
end Curve25519Dalek.backend.serial.u32.constants


namespace Curve25519Dalek.backend.serial.u64.constants
namespace «x86_64-tables»

/-- `ED25519_BASEPOINT_128_POINT` represents `2^128 • basepoint`. -/
recall ED25519_BASEPOINT_128_POINT_spec :
    ED25519_BASEPOINT_128_POINT.«x86_64-tables»
      ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
        r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_128_POINT_spec

end «x86_64-tables»
end Curve25519Dalek.backend.serial.u64.constants

namespace Curve25519Dalek.backend.serial.u32.constants
namespace «i686-tables»

/-- `ED25519_BASEPOINT_128_POINT` represents `2^128 • basepoint`. -/
recall ED25519_BASEPOINT_128_POINT_spec :
    ED25519_BASEPOINT_128_POINT.«i686-tables»
      ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
        r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_128_POINT_spec

end «i686-tables»
end Curve25519Dalek.backend.serial.u32.constants

namespace Curve25519Dalek.backend.serial.u64.constants
namespace «x86_64-no-tables»

/-- `ED25519_BASEPOINT_128_POINT` represents `2^128 • basepoint`. -/
recall ED25519_BASEPOINT_128_POINT_spec :
    ED25519_BASEPOINT_128_POINT.«x86_64-no-tables»
      ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
        r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_128_POINT_spec

end «x86_64-no-tables»
end Curve25519Dalek.backend.serial.u64.constants

namespace Curve25519Dalek.backend.serial.u32.constants
namespace «i686-no-tables»

/-- `ED25519_BASEPOINT_128_POINT` represents `2^128 • basepoint`. -/
recall ED25519_BASEPOINT_128_POINT_spec :
    ED25519_BASEPOINT_128_POINT.«i686-no-tables»
      ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
        r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_128_POINT_spec

end «i686-no-tables»
end Curve25519Dalek.backend.serial.u32.constants

namespace Curve25519Dalek.backend.serial.u64.constants
namespace «x86_64-tables»

/-- `EIGHT_TORSION`: entry `i` represents `i • torsion8`. -/
recall EIGHT_TORSION_spec :
    EIGHT_TORSION.«x86_64-tables»
      ⦃ (r : Array edwards.EdwardsPoint.«x86_64-tables» 8#usize) =>
      ∀ i : Fin 8, r[i.val]!.OnCurve ∧ r[i.val]!.toPoint = (i : ℕ) • torsion8 ∧
        r[i.val]!.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms EIGHT_TORSION_spec

end «x86_64-tables»

end Curve25519Dalek.backend.serial.u64.constants

namespace Curve25519Dalek.backend.serial.u32.constants
namespace «i686-tables»

/-- `EIGHT_TORSION`: entry `i` represents `i • torsion8`. -/
recall EIGHT_TORSION_spec :
    EIGHT_TORSION.«i686-tables»
      ⦃ (r : Array edwards.EdwardsPoint.«i686-tables» 8#usize) =>
      ∀ i : Fin 8, r[i.val]!.OnCurve ∧ r[i.val]!.toPoint = (i : ℕ) • torsion8 ∧
        r[i.val]!.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms EIGHT_TORSION_spec

end «i686-tables»
end Curve25519Dalek.backend.serial.u32.constants


namespace Curve25519Dalek.backend.serial.u64.constants
namespace «x86_64-no-tables»

/-- `EIGHT_TORSION`: entry `i` represents `i • torsion8`. -/
recall EIGHT_TORSION_spec :
    EIGHT_TORSION.«x86_64-no-tables»
      ⦃ (r : Array edwards.EdwardsPoint.«x86_64-no-tables» 8#usize) =>
      ∀ i : Fin 8, r[i.val]!.OnCurve ∧ r[i.val]!.toPoint = (i : ℕ) • torsion8 ∧
        r[i.val]!.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms EIGHT_TORSION_spec

end «x86_64-no-tables»

end Curve25519Dalek.backend.serial.u64.constants

namespace Curve25519Dalek.backend.serial.u32.constants
namespace «i686-no-tables»

/-- `EIGHT_TORSION`: entry `i` represents `i • torsion8`. -/
recall EIGHT_TORSION_spec :
    EIGHT_TORSION.«i686-no-tables»
      ⦃ (r : Array edwards.EdwardsPoint.«i686-no-tables» 8#usize) =>
      ∀ i : Fin 8, r[i.val]!.OnCurve ∧ r[i.val]!.toPoint = (i : ℕ) • torsion8 ∧
        r[i.val]!.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms EIGHT_TORSION_spec

end «i686-no-tables»
end Curve25519Dalek.backend.serial.u32.constants


namespace Curve25519Dalek.backend.serial.u64.constants

/-- `ED25519_BASEPOINT_TABLE`: a table representing the basepoint. -/
recall ED25519_BASEPOINT_TABLE_spec :
    ED25519_BASEPOINT_TABLE ⦃ (r : edwards.EdwardsBasepointTable.«x86_64-tables») =>
      r.IsTable ∧ r.point = basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ED25519_BASEPOINT_TABLE_spec

end Curve25519Dalek.backend.serial.u64.constants

namespace Curve25519Dalek.backend.serial.u32.constants

/-- `ED25519_BASEPOINT_TABLE`: a table representing the basepoint. -/
recall ED25519_BASEPOINT_TABLE_spec :
    ED25519_BASEPOINT_TABLE ⦃ (r : edwards.EdwardsBasepointTable.«i686-tables») =>
      r.IsTable ∧ r.point = basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ED25519_BASEPOINT_TABLE_spec

end Curve25519Dalek.backend.serial.u32.constants

namespace Curve25519Dalek.constants

/-- `ED25519_BASEPOINT_COMPRESSED`: RFC 8032's encoding of the basepoint. -/
recall ED25519_BASEPOINT_COMPRESSED_spec :
    ED25519_BASEPOINT_COMPRESSED.toVector = curve25519.encode curve25519.basepoint

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_COMPRESSED_spec

end Curve25519Dalek.constants

namespace Curve25519Dalek.constants

/-- `X25519_BASEPOINT`: RFC 7748's encoding of the `u`-coordinate `9` of the Montgomery
basepoint. -/
recall X25519_BASEPOINT_spec :
    X25519_BASEPOINT.toVector = curve25519.encodeUCoordinate curve25519.montgomeryBasepoint.u

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms X25519_BASEPOINT_spec

end Curve25519Dalek.constants

namespace Curve25519Dalek.constants

/-- `RISTRETTO_BASEPOINT_COMPRESSED`: RFC 9496's encoding of the basepoint. -/
recall RISTRETTO_BASEPOINT_COMPRESSED_spec :
    RISTRETTO_BASEPOINT_COMPRESSED.toVector = Ristretto.encodeRep basepoint

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms RISTRETTO_BASEPOINT_COMPRESSED_spec

namespace «x86_64-tables»

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative). -/
recall RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT.«x86_64-tables» ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms RISTRETTO_BASEPOINT_POINT_spec

end «x86_64-tables»

namespace «i686-tables»

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative). -/
recall RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT.«i686-tables» ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms RISTRETTO_BASEPOINT_POINT_spec

end «i686-tables»

namespace «x86_64-no-tables»

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative). -/
recall RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT.«x86_64-no-tables»
      ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
        r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms RISTRETTO_BASEPOINT_POINT_spec

end «x86_64-no-tables»

namespace «i686-no-tables»

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative). -/
recall RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT.«i686-no-tables»
      ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
        r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms RISTRETTO_BASEPOINT_POINT_spec

end «i686-no-tables»

namespace «x86_64-tables»

/-- `RISTRETTO_BASEPOINT_TABLE`: a table representing the basepoint. -/
recall RISTRETTO_BASEPOINT_TABLE_spec :
    RISTRETTO_BASEPOINT_TABLE.«x86_64-tables»
      ⦃ (r : ristretto.RistrettoBasepointTable.«x86_64-tables») =>
        r.IsTable ∧ r.point = basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms RISTRETTO_BASEPOINT_TABLE_spec

end «x86_64-tables»

namespace «i686-tables»

/-- `RISTRETTO_BASEPOINT_TABLE`: a table representing the basepoint. -/
recall RISTRETTO_BASEPOINT_TABLE_spec :
    RISTRETTO_BASEPOINT_TABLE.«i686-tables»
      ⦃ (r : ristretto.RistrettoBasepointTable.«i686-tables») =>
        r.IsTable ∧ r.point = basepoint ∧ r.IsBounded ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms RISTRETTO_BASEPOINT_TABLE_spec

end «i686-tables»

/-- `X25519_LOW_ORDER_POINTS`: a point is sent to `0` by X25519 for every scalar iff it is equal
to one of the seven points as a `MontgomeryPoint` ("The output of any scalar multiplied by these
points is zero"; true for clamped scalars, which is what X25519 uses; and no other point has this
property). This is equality with `==` (`PartialEq`, which compares the decoded coordinates,
`decodeUCoordinate`), not equality of the bytes: other encodings of the same coordinates are sent
to `0` too. In particular each of the seven points is sent to `0` (take `Q` to be the point). -/
recall X25519_LOW_ORDER_POINTS_spec (Q : montgomery.MontgomeryPoint) :
    (∀ k : Vector UInt8 32, X25519 k Q.toVector = encodeUCoordinate 0) ↔
      ∃ i : Fin 7, decodeUCoordinate Q.toVector =
        decodeUCoordinate X25519_LOW_ORDER_POINTS[i.val]!.toVector

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms X25519_LOW_ORDER_POINTS_spec

end Curve25519Dalek.constants
