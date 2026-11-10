/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Types
public import Defs.Array
public import ToAeneas.Array
public section

/-! # `ristretto.rs`: the compressed form (audited)

`RistrettoPoint` is `EdwardsPoint` (a type alias in the translation); a representative is valid
when `self.OnCurve ∧ Even self.toPoint` (Mathlib's `Even`), with the Edwards `LimbsLt` bound as its
limb bounds: nothing new is defined for it. The encoding is in `curve25519.Ristretto`
(`Curve25519/Ristretto/*`): a `decompress` spec reads `r.map toPoint = Ristretto.decodeRep
self.toVector`, `compress` reads `r.toVector = Ristretto.encodeRep self.toPoint`, `ct_eq` reads
`c = 1 ↔ curve25519.edwards.Rel self.toPoint other.toPoint`.

`CompressedRistretto` is 32 bytes; `toVector` gives them as a `Vector UInt8 32`, the byte string
of RFC 9496. -/

namespace Curve25519Dalek.ristretto

end Curve25519Dalek.ristretto
