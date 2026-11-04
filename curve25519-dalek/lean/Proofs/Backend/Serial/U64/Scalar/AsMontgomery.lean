/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Oliver Butterley, Theo Ehrenborg
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar52
import Proofs.Backend.Serial.U64.Constants.RR
import Proofs.Helpers.Scalar52
import Proofs.Backend.Serial.U64.Scalar.MontgomeryMul
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

@[step]
theorem as_montgomery_spec (self : Scalar52) (hself : self.LimbsLt 52) :
    as_montgomery self ⦃ (r : Scalar52) =>
      r.asNat = self.asNat * montgomeryRadix % L ∧ r.LimbsLt 52 ⦄ := by
  unfold as_montgomery
  obtain ⟨hRR, hRR_lt⟩ := constants.RR_spec
  generalize hR2 : montgomeryRadix ^ 2 % L = R2 at hRR
  have hR2L : R2 < L := hR2 ▸ Nat.mod_lt _ L_pos
  have hself_lt : self.asNat < montgomeryRadix := Scalar52.asNat_lt self hself
  step with montgomery_mul_spec self constants.RR hself hRR_lt
    (Nat.mul_lt_mul'' hself_lt (hRR ▸ hR2L)) as ⟨r, hr, hrL, hr_lt⟩
  refine ⟨?_, hr_lt⟩
  rw [hRR, ← hR2] at hr
  rw [← Nat.mod_eq_of_lt hrL]
  exact mod_L_of_mul_montgomeryRadix_eq_mul_RR hr

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52
