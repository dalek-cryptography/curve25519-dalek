/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinxing Lim
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar29
import Proofs.Backend.Serial.U32.Constants.RR
import Proofs.Helpers.Scalar29
import Proofs.Backend.Serial.U32.Scalar.MontgomeryReduce
import Proofs.Backend.Serial.U32.Scalar.MulInternal
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29)

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

@[step]
theorem mul_spec (a b : Scalar29) (ha : a.LimbsLt 29)
    (hb : b.LimbsLt 29) (hab : a.asNat * b.asNat < montgomeryRadix * L) :
    mul a b ⦃ (r : Scalar29) =>
      r.asNat = a.asNat * b.asNat % L ∧ r.LimbsLt 29 ⦄ := by
  unfold mul
  obtain ⟨hRR, hRR_lt⟩ := constants.RR_spec
  generalize hR2 : montgomeryRadix ^ 2 % L = R2 at hRR
  have hR2L : R2 < L := hR2 ▸ Nat.mod_lt _ L_pos
  step with mul_internal_spec a b ha hb as ⟨ab, hab_eq, hab_lt⟩
  step with montgomery_reduce_spec ab (fun i hi => (hab_lt i hi).trans (by decide))
    (hab_eq ▸ hab) as ⟨t, ht, htL, ht_lt⟩
  have htRR : t.asNat * constants.RR.asNat < montgomeryRadix * L :=
    Nat.mul_lt_mul'' (htL.trans L_lt_montgomeryRadix) (hRR ▸ hR2L)
  step with mul_internal_spec t constants.RR ht_lt hRR_lt as ⟨tRR, htRR_eq, htRR_lt⟩
  step with montgomery_reduce_spec tRR (fun i hi => (htRR_lt i hi).trans (by decide))
    (htRR_eq ▸ htRR) as ⟨r, hr, hrL, hr_lt⟩
  refine ⟨?_, hr_lt⟩
  rw [htRR_eq, hRR, ← hR2] at hr
  have h := mod_L_of_mul_montgomeryRadix_eq_mul_RR hr
  rw [Nat.mod_eq_of_lt hrL] at h
  rw [h, ht, hab_eq]

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29
