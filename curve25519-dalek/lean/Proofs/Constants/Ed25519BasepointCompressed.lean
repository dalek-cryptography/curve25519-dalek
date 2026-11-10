/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Encoding
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Proofs.Helpers.ByteValues
public section

open Aeneas Aeneas.Std

namespace Curve25519Dalek.constants

/-- `ED25519_BASEPOINT_COMPRESSED`: RFC 8032's encoding of the basepoint. -/
theorem ED25519_BASEPOINT_COMPRESSED_spec :
    ED25519_BASEPOINT_COMPRESSED.toVector = curve25519.encode curve25519.basepoint := by
  simp only [Curve25519Dalek.edwards.CompressedEdwardsY.toVector_eq_encode_iff]
  unfold ED25519_BASEPOINT_COMPRESSED
  rw [edwards.CompressedEdwardsY.asNat_def, Array.asNat_def, Array.make_val,
    curve25519.encodeNat_basepoint]
  decide

end Curve25519Dalek.constants
