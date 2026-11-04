/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Montgomery
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Montgomery
public section

open Aeneas Aeneas.Std

namespace Curve25519Dalek.constants

/-- `X25519_BASEPOINT`: RFC 7748's encoding of the `u`-coordinate `9` of the Montgomery
basepoint. -/
theorem X25519_BASEPOINT_spec :
    X25519_BASEPOINT.asNat = curve25519.encodeU curve25519.montgomeryBasepoint.u := by
  unfold X25519_BASEPOINT
  rw [montgomery.MontgomeryPoint.asNat_def, Array.asNat_def, Array.make_val,
    curve25519.u_montgomeryBasepoint, curve25519.encodeU,
    ZMod.val_ofNat_of_lt (by rw [curve25519.p_eq_numeral]; decide)]
  decide

end Curve25519Dalek.constants
