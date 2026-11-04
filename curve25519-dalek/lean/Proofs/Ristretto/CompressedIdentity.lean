/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Ristretto
public import Curve25519.Ristretto.Encoding
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
public section

/-! # `Identity` and `Default` for `CompressedRistretto` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.ristretto.CompressedRistretto

/-- Thirty-two zero bytes have value `0`. -/
theorem asNat_repeat_zero : CompressedRistretto.asNat (Array.repeat 32#usize 0#u8) = 0 := by
  rw [CompressedRistretto.asNat_def, Array.asNat_eq_sum]
  exact Finset.sum_eq_zero fun i hi => by
    rw [Array.getElem!_repeat 0#u8 (by simpa using Finset.mem_range.mp hi)]
    rfl

namespace Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for CompressedRistretto`: thirty-two zero bytes, value `0`. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : CompressedRistretto) => r.asNat = 0 ⦄ := by
  unfold identity
  step*
  exact asNat_repeat_zero

/-- `Identity for CompressedRistretto` is the encoding of the neutral element. -/
theorem identity_spec_point :
    identity ⦃ (r : CompressedRistretto) => r.asNat = Ristretto.encodeRep 0 ⦄ :=
  spec_mono identity_spec fun r hr => by rw [hr, Ristretto.encodeRep_zero]

end Insts.Curve25519_dalekTraitsIdentity

namespace Insts.CoreDefaultDefault

/-- `Default for CompressedRistretto`: the identity, value `0`. -/
@[step]
theorem default_spec :
    default ⦃ (r : CompressedRistretto) => r.asNat = 0 ⦄ := by
  unfold default
  step*

/-- `Default for CompressedRistretto` is the encoding of the neutral element. -/
theorem default_spec_point :
    default ⦃ (r : CompressedRistretto) => r.asNat = Ristretto.encodeRep 0 ⦄ :=
  spec_mono default_spec fun r hr => by rw [hr, Ristretto.encodeRep_zero]

end Insts.CoreDefaultDefault

end Curve25519Dalek.ristretto.CompressedRistretto
