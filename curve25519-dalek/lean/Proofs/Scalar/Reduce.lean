/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander, Hoang Le Truong
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar29
import Proofs.Backend.Serial.U64.Constants.R
import Proofs.Backend.Serial.U64.Scalar.MontgomeryReduce
import Proofs.Backend.Serial.U64.Scalar.MulInternal
import Proofs.Helpers.Scalar
import Proofs.Helpers.Scalar52
import Proofs.Helpers.Target
import Proofs.Scalar.Scalar52Pack
import Proofs.Scalar.Unpack
import Proofs.Backend.Serial.U32.Constants.R
import Proofs.Backend.Serial.U32.Scalar.MontgomeryReduce
import Proofs.Backend.Serial.U32.Scalar.MulInternal
import Proofs.Helpers.Scalar29
import Proofs.Scalar.Scalar29Pack
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem reduce.«x86_64-tables_spec» (self : Scalar) :
    reduce.«x86_64-tables» self ⦃ (r : Scalar) =>
      r.asNat = self.asNat % L ⦄ := by
  unfold reduce.«x86_64-tables»
  obtain ⟨hR, hRb⟩ := backend.serial.u64.constants.R_spec
  step as ⟨x, hx, hxb⟩
  step with backend.serial.u64.scalar.Scalar52.mul_internal_spec x _ hxb hRb as ⟨xR, hxR, hxRb⟩
  have hlt : xR.asNat 52 < montgomeryRadix * L := by
    rw [hxR, hR]
    exact Nat.mul_lt_mul'' (backend.serial.u64.scalar.Scalar52.asNat_lt x hxb)
      (Nat.mod_lt _ L_pos)
  step with backend.serial.u64.scalar.Scalar52.montgomery_reduce_spec xR
    (fun i hi => (hxRb i hi).trans (by decide)) hlt as ⟨m, hm, hmL, hmb⟩
  have hm' : m.asNat = self.asNat % L := by
    rw [← hx, ← Nat.mod_eq_of_lt hmL]
    apply backend.serial.u64.scalar.mod_L_of_mul_montgomeryRadix
    rw [hm, hxR, hR, Nat.mul_mod_mod]
  step with Scalar52.pack_spec m hmb (lt_two_pow_256_of_lt_L hmL) as ⟨r, hr⟩
  rw [hr, hm']

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem reduce.«x86_64-no-tables_spec» (self : Scalar) :
    reduce.«x86_64-no-tables» self ⦃ (r : Scalar) =>
      r.asNat = self.asNat % L ⦄ :=
  reduce.«x86_64-tables_spec» self

end Curve25519Dalek.scalar.Scalar


namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem reduce.«i686-tables_spec» (self : Scalar) :
    reduce.«i686-tables» self ⦃ (r : Scalar) =>
      r.asNat = self.asNat % L ⦄ := by
  unfold reduce.«i686-tables»
  obtain ⟨hR, hRb⟩ := backend.serial.u32.constants.R_spec
  step as ⟨x, hx, hxb⟩
  step with backend.serial.u32.scalar.Scalar29.mul_internal_spec x _ hxb hRb as ⟨xR, hxR, hxRb⟩
  have hlt : xR.asNat 29 < backend.serial.u32.scalar.montgomeryRadix * L := by
    rw [hxR, hR]
    exact Nat.mul_lt_mul'' (backend.serial.u32.scalar.Scalar29.asNat_lt x hxb)
      (Nat.mod_lt _ L_pos)
  step with backend.serial.u32.scalar.Scalar29.montgomery_reduce_spec xR
    (fun i hi => (hxRb i hi).trans (by decide)) hlt as ⟨m, hm, hmL, hmb⟩
  have hm' : m.asNat = self.asNat % L := by
    rw [← hx, ← Nat.mod_eq_of_lt hmL]
    apply backend.serial.u32.scalar.mod_L_of_mul_montgomeryRadix
    rw [hm, hxR, hR, Nat.mul_mod_mod]
  step with Scalar29.pack_spec m hmb (lt_two_pow_256_of_lt_L hmL) as ⟨r, hr⟩
  rw [hr, hm']

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem reduce.«i686-no-tables_spec» (self : Scalar) :
    reduce.«i686-no-tables» self ⦃ (r : Scalar) =>
      r.asNat = self.asNat % L ⦄ :=
  reduce.«i686-tables_spec» self

end Curve25519Dalek.scalar.Scalar
namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem reduce_spec (self : Scalar) :
    reduce self ⦃ (r : Scalar) =>
      r.asNat = self.asNat % L ⦄ := by
  unfold reduce
  exact dispatch_all_spec
    (reduce.«x86_64-tables_spec» self)
    (reduce.«x86_64-no-tables_spec» self)
    (reduce.«i686-tables_spec» self)
    (reduce.«i686-no-tables_spec» self)

end Curve25519Dalek.scalar.Scalar
