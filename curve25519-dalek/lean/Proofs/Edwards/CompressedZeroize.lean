/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Curve25519.Edwards.Encoding
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
import Zeroize.Instances
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts.ZeroizeZeroize

/-- `Zeroize for CompressedEdwardsY`: reset to the identity `[1, 0, …, 0]`, value `1`. -/
@[step]
theorem zeroize_spec (self : CompressedEdwardsY) :
    zeroize self ⦃ (r : CompressedEdwardsY) => r.asNat = 1 ⦄ := by
  unfold zeroize
  step as ⟨a, ha⟩
  step as ⟨a1, ha1⟩
  subst ha ha1
  have h0 : (Array.repeat 32#usize 0#u8).asNat 8 = 0 := by
    rw [Array.asNat_eq_sum]
    exact Finset.sum_eq_zero fun i hi => by
      rw [Array.getElem!_repeat 0#u8 (by simpa using Finset.mem_range.mp hi)]
      rfl
  have h := Array.asNat_set_add 8 (Array.repeat 32#usize 0#u8) 0#usize 1#u8 (by decide)
  rw [CompressedEdwardsY.asNat_def]
  simpa [h0, Array.getElem!_repeat 0#u8 (show 0 < (32#usize).val by decide)] using h

/-- `Zeroize for CompressedEdwardsY` leaves the encoding of the neutral element. -/
theorem zeroize_spec_point (self : CompressedEdwardsY) :
    zeroize self ⦃ (r : CompressedEdwardsY) => r.asNat = encode 0 ⦄ :=
  spec_mono (zeroize_spec self) fun r hr => by rw [hr, encode_zero]

end Curve25519Dalek.edwards.CompressedEdwardsY.Insts.ZeroizeZeroize
