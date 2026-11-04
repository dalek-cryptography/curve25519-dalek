/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Types
public import Defs.Array
public section

/-! # `ristretto.rs`: the compressed form (audited)

`RistrettoPoint` is `EdwardsPoint` (a type alias in the translation); a representative is valid
when `self.OnCurve ∧ Even self.toPoint` (Mathlib's `Even`), with the Edwards `LimbsLt` bound as its
limb bounds: nothing new is defined for it. The encoding is in `curve25519.Ristretto`
(`Curve25519/Ristretto/*`): a `decompress` spec reads `r.map toPoint =
Ristretto.decodeRep bytes.asNat`, `compress` reads `r.asNat = Ristretto.encodeRep self.toPoint`,
`ct_eq` reads `c = 1 ↔ curve25519.edwards.Rel self.toPoint other.toPoint`.

`CompressedRistretto` is 32 bytes; `asNat` is their little-endian value. -/

namespace Curve25519Dalek.ristretto

/-- The little-endian value of the 32 bytes. -/
def CompressedRistretto.asNat (self : CompressedRistretto) : ℕ :=
  Aeneas.Std.Array.asNat 8 self

theorem CompressedRistretto.asNat_def (self : CompressedRistretto) :
    self.asNat = Aeneas.Std.Array.asNat 8 self := by
  unfold CompressedRistretto.asNat
  rfl

end Curve25519Dalek.ristretto
