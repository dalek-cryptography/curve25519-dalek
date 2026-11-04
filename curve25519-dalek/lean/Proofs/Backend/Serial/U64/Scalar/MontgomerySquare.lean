/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar52
import Proofs.Backend.Serial.U64.Scalar.MontgomeryReduce
import Proofs.Backend.Serial.U64.Scalar.SquareInternal
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

@[step]
theorem montgomery_square_spec (self : Scalar52) (hself : self.LimbsLt 52)
    (hself' : self.asNat ^ 2 < montgomeryRadix * L) :
    montgomery_square self ⦃ (r : Scalar52) =>
      r.asNat * montgomeryRadix % L = self.asNat ^ 2 % L ∧ r.asNat < L ∧
      r.LimbsLt 52 ⦄ := by
  unfold montgomery_square
  step with square_internal_spec self hself as ⟨aa, haa_eq, haa_lt⟩
  step with montgomery_reduce_spec aa (fun i hi => (haa_lt i hi).trans (by decide))
    (haa_eq ▸ hself') as ⟨r, hr, hrL, hr_lt⟩
  exact ⟨haa_eq ▸ hr, hrL, hr_lt⟩

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52
