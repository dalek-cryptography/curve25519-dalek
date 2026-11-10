/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Ristretto
public import Curve25519.Ristretto.Encoding
import Proofs.Ristretto.CompressedIdentity
import Zeroize.Instances
public import Proofs.Helpers.ByteValues
public section

/-! # `Zeroize for CompressedRistretto` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.ristretto.CompressedRistretto.Insts.ZeroizeZeroize

/-- `Zeroize for CompressedRistretto`: thirty-two zero bytes, the encoding of the neutral
element. -/
theorem zeroize_spec (self : CompressedRistretto) :
    zeroize self ⦃ (r : CompressedRistretto) => r.toVector = Ristretto.encodeRep 0 ⦄ := by
  simp only [Curve25519Dalek.ristretto.CompressedRistretto.toVector_eq_encodeRep_iff]
  exact spec_mono (zeroize_eq self) fun r hr => by
    rw [hr, CompressedRistretto.asNat_repeat_zero, Ristretto.encodeRepNat_zero]

end Curve25519Dalek.ristretto.CompressedRistretto.Insts.ZeroizeZeroize
