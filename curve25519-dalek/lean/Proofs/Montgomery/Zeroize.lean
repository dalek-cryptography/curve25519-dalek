/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Montgomery
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
import Zeroize.Instances
public import Proofs.Helpers.ByteValues
public section

/-! # `Zeroize for MontgomeryPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.ZeroizeZeroize

/-- `Zeroize for MontgomeryPoint`: thirty-two zero bytes, the encoding of `u = 0`. -/
theorem zeroize_spec (self : MontgomeryPoint) :
    zeroize self ⦃ (r : MontgomeryPoint) => r.toVector = encodeUCoordinate 0 ⦄ := by
  simp only
      [Curve25519Dalek.montgomery.MontgomeryPoint.toVector_eq_encodeUCoordinate_iff,
      curve25519.encodeU_zero]
  exact spec_mono (zeroize_eq self) fun r hr => by
    rw [hr, MontgomeryPoint.asNat_def, Array.asNat_eq_sum]
    exact Finset.sum_eq_zero fun i hi => by
      rw [Array.getElem!_repeat 0#u8 (by simpa using Finset.mem_range.mp hi)]
      rfl

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.ZeroizeZeroize
