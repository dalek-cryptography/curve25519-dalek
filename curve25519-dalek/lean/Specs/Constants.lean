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

Definitions used: Mathlib's `Even`, `EdwardsPoint.toPoint`, `OnCurve`, `LimbsLt`,
`CompressedEdwardsY.asNat` (`Defs/Edwards.lean`), `MontgomeryPoint.asNat` (`Defs/Montgomery.lean`),
`curve25519.basepoint` (`Curve25519/Edwards/Basepoint.lean`), `curve25519.encode`
(`Curve25519/Edwards/Encoding.lean`), `curve25519.eightTorsion` (`Curve25519/Edwards/Torsion.lean`),
`curve25519.montgomeryBasepoint` (`Curve25519/Montgomery.lean`), `curve25519.encodeU`,
`curve25519.x25519` (`Curve25519/X25519.lean`), the tables' `Represents` (`Defs/Edwards.lean`),
`CompressedRistretto.asNat` (`Defs/Ristretto.lean`), `Ristretto.encodeRep`
(`Curve25519/Ristretto/`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel

namespace Curve25519Dalek.backend.serial.u64.constants
namespace «x86_64-tables»

/-- `ED25519_BASEPOINT_POINT` represents the basepoint. -/
recall ED25519_BASEPOINT_POINT_spec_point :
    ED25519_BASEPOINT_POINT.«x86_64-tables» ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = basepoint ∧ r.LimbsLt 52 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_POINT_spec_point

end «x86_64-tables»

end Curve25519Dalek.backend.serial.u64.constants

namespace Curve25519Dalek.backend.serial.u32.constants
namespace «i686-tables»

/-- `ED25519_BASEPOINT_POINT` represents the basepoint. -/
recall ED25519_BASEPOINT_POINT_spec_point :
    ED25519_BASEPOINT_POINT.«i686-tables» ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = basepoint ∧ r.LimbsLt 26 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_POINT_spec_point

end «i686-tables»
end Curve25519Dalek.backend.serial.u32.constants


namespace Curve25519Dalek.backend.serial.u64.constants
namespace «x86_64-no-tables»

/-- `ED25519_BASEPOINT_POINT` represents the basepoint. -/
recall ED25519_BASEPOINT_POINT_spec_point :
    ED25519_BASEPOINT_POINT.«x86_64-no-tables» ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = basepoint ∧ r.LimbsLt 52 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_POINT_spec_point

end «x86_64-no-tables»

end Curve25519Dalek.backend.serial.u64.constants

namespace Curve25519Dalek.backend.serial.u32.constants
namespace «i686-no-tables»

/-- `ED25519_BASEPOINT_POINT` represents the basepoint. -/
recall ED25519_BASEPOINT_POINT_spec_point :
    ED25519_BASEPOINT_POINT.«i686-no-tables» ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = basepoint ∧ r.LimbsLt 26 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_POINT_spec_point

end «i686-no-tables»
end Curve25519Dalek.backend.serial.u32.constants


namespace Curve25519Dalek.backend.serial.u64.constants
namespace «x86_64-tables»

/-- `ED25519_BASEPOINT_128_POINT` represents `2^128 • basepoint`. -/
recall ED25519_BASEPOINT_128_POINT_spec :
    ED25519_BASEPOINT_128_POINT.«x86_64-tables»
      ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
        r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint ∧ r.LimbsLt 52 ⦄

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
        r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint ∧ r.LimbsLt 26 ⦄

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
        r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint ∧ r.LimbsLt 52 ⦄

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
        r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint ∧ r.LimbsLt 26 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_128_POINT_spec

end «i686-no-tables»
end Curve25519Dalek.backend.serial.u32.constants

namespace Curve25519Dalek.backend.serial.u64.constants
namespace «x86_64-tables»

/-- `EIGHT_TORSION`: entry `i` represents `eightTorsion i = i • torsion8`. -/
recall EIGHT_TORSION_spec_point :
    EIGHT_TORSION.«x86_64-tables»
      ⦃ (r : Array edwards.EdwardsPoint.«x86_64-tables» 8#usize) =>
      ∀ i : Fin 8, r[i.val]!.OnCurve ∧ r[i.val]!.toPoint = eightTorsion i ∧ r[i.val]!.LimbsLt 52 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms EIGHT_TORSION_spec_point

end «x86_64-tables»

end Curve25519Dalek.backend.serial.u64.constants

namespace Curve25519Dalek.backend.serial.u32.constants
namespace «i686-tables»

/-- `EIGHT_TORSION`: entry `i` represents `eightTorsion i = i • torsion8`. -/
recall EIGHT_TORSION_spec_point :
    EIGHT_TORSION.«i686-tables»
      ⦃ (r : Array edwards.EdwardsPoint.«i686-tables» 8#usize) =>
      ∀ i : Fin 8, r[i.val]!.OnCurve ∧ r[i.val]!.toPoint = eightTorsion i ∧ r[i.val]!.LimbsLt 26 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms EIGHT_TORSION_spec_point

end «i686-tables»
end Curve25519Dalek.backend.serial.u32.constants


namespace Curve25519Dalek.backend.serial.u64.constants
namespace «x86_64-no-tables»

/-- `EIGHT_TORSION`: entry `i` represents `eightTorsion i = i • torsion8`. -/
recall EIGHT_TORSION_spec_point :
    EIGHT_TORSION.«x86_64-no-tables»
      ⦃ (r : Array edwards.EdwardsPoint.«x86_64-no-tables» 8#usize) =>
      ∀ i : Fin 8, r[i.val]!.OnCurve ∧ r[i.val]!.toPoint = eightTorsion i ∧ r[i.val]!.LimbsLt 52 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms EIGHT_TORSION_spec_point

end «x86_64-no-tables»

end Curve25519Dalek.backend.serial.u64.constants

namespace Curve25519Dalek.backend.serial.u32.constants
namespace «i686-no-tables»

/-- `EIGHT_TORSION`: entry `i` represents `eightTorsion i = i • torsion8`. -/
recall EIGHT_TORSION_spec_point :
    EIGHT_TORSION.«i686-no-tables»
      ⦃ (r : Array edwards.EdwardsPoint.«i686-no-tables» 8#usize) =>
      ∀ i : Fin 8, r[i.val]!.OnCurve ∧ r[i.val]!.toPoint = eightTorsion i ∧ r[i.val]!.LimbsLt 26 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms EIGHT_TORSION_spec_point

end «i686-no-tables»
end Curve25519Dalek.backend.serial.u32.constants


namespace Curve25519Dalek.backend.serial.u64.constants

/-- `ED25519_BASEPOINT_TABLE`: a table representing the basepoint; limbs `< 2^54`. -/
recall ED25519_BASEPOINT_TABLE_spec :
    ED25519_BASEPOINT_TABLE ⦃ (r : edwards.EdwardsBasepointTable.«x86_64-tables») =>
      r.Represents basepoint ∧ r.LimbsLt 54 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ED25519_BASEPOINT_TABLE_spec

end Curve25519Dalek.backend.serial.u64.constants

namespace Curve25519Dalek.constants

/-- `ED25519_BASEPOINT_COMPRESSED`: RFC 8032's encoding of the basepoint. -/
recall ED25519_BASEPOINT_COMPRESSED_spec :
    ED25519_BASEPOINT_COMPRESSED.asNat = curve25519.encode curve25519.basepoint

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms ED25519_BASEPOINT_COMPRESSED_spec

end Curve25519Dalek.constants

namespace Curve25519Dalek.constants

/-- `X25519_BASEPOINT`: RFC 7748's encoding of the `u`-coordinate `9` of the Montgomery
basepoint. -/
recall X25519_BASEPOINT_spec :
    X25519_BASEPOINT.asNat = curve25519.encodeU curve25519.montgomeryBasepoint.u

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms X25519_BASEPOINT_spec

end Curve25519Dalek.constants

namespace Curve25519Dalek.constants

/-- `RISTRETTO_BASEPOINT_COMPRESSED`: RFC 9496's encoding of the basepoint. -/
recall RISTRETTO_BASEPOINT_COMPRESSED_spec :
    RISTRETTO_BASEPOINT_COMPRESSED.asNat = Ristretto.encodeRep basepoint

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in
#print axioms RISTRETTO_BASEPOINT_COMPRESSED_spec

namespace «x86_64-tables»

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative);
limbs `< 2^52`. -/
recall RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT.«x86_64-tables» ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.LimbsLt 52 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms RISTRETTO_BASEPOINT_POINT_spec

end «x86_64-tables»

namespace «i686-tables»

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative);
limbs `< 2^26`. -/
recall RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT.«i686-tables» ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.LimbsLt 26 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms RISTRETTO_BASEPOINT_POINT_spec

end «i686-tables»

namespace «x86_64-no-tables»

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative);
limbs `< 2^52`. -/
recall RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT.«x86_64-no-tables»
      ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
        r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.LimbsLt 52 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms RISTRETTO_BASEPOINT_POINT_spec

end «x86_64-no-tables»

namespace «i686-no-tables»

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative);
limbs `< 2^26`. -/
recall RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT.«i686-no-tables»
      ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
        r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.LimbsLt 26 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms RISTRETTO_BASEPOINT_POINT_spec

end «i686-no-tables»

namespace «x86_64-tables»

/-- `RISTRETTO_BASEPOINT_TABLE`: a table representing the basepoint; limbs `< 2^54`. -/
recall RISTRETTO_BASEPOINT_TABLE_spec :
    RISTRETTO_BASEPOINT_TABLE.«x86_64-tables»
      ⦃ (r : ristretto.RistrettoBasepointTable.«x86_64-tables») =>
        r.Represents basepoint ∧ r.LimbsLt 54 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms RISTRETTO_BASEPOINT_TABLE_spec

end «x86_64-tables»

namespace «i686-tables»

/-- `RISTRETTO_BASEPOINT_TABLE`: a table representing the basepoint; limbs `< 2^27`. -/
recall RISTRETTO_BASEPOINT_TABLE_spec :
    RISTRETTO_BASEPOINT_TABLE.«i686-tables»
      ⦃ (r : ristretto.RistrettoBasepointTable.«i686-tables») =>
        r.Represents basepoint ∧ r.LimbsLt 27 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms RISTRETTO_BASEPOINT_TABLE_spec

end «i686-tables»

/-- `X25519_LOW_ORDER_POINTS`: X25519 sends each of the seven points to `0`, whatever the
scalar ("The output of any scalar multiplied by these points is zero"; true for clamped
scalars, which is what X25519 uses). -/
recall X25519_LOW_ORDER_POINTS_spec :
    ∀ P ∈ X25519_LOW_ORDER_POINTS.val, ∀ k : ℕ, x25519 k P.asNat = 0

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms X25519_LOW_ORDER_POINTS_spec

end Curve25519Dalek.constants
