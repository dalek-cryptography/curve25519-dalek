/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar29
import Proofs.Backend.Serial.U64.Constants.R
import Proofs.Backend.Serial.U64.Scalar.MontgomeryReduce
import Proofs.Backend.Serial.U64.Scalar.MulInternal
import Proofs.Backend.Serial.U64.Scalar.Sub
import Proofs.Backend.Serial.U64.Scalar.Zero
import Proofs.Helpers.Scalar
import Proofs.Helpers.Scalar52
import Proofs.Helpers.Target
import Proofs.Scalar.Scalar52Pack
import Proofs.Scalar.Unpack
import Proofs.Backend.Serial.U32.Constants.R
import Proofs.Backend.Serial.U32.Scalar.MontgomeryReduce
import Proofs.Backend.Serial.U32.Scalar.MulInternal
import Proofs.Backend.Serial.U32.Scalar.Sub
import Proofs.Backend.Serial.U32.Scalar.Zero
import Proofs.Helpers.Scalar29
import Proofs.Scalar.Scalar29Pack
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.NegShared0ScalarScalar

@[step]
theorem neg.«x86_64-tables_spec» (self : Scalar) :
    neg.«x86_64-tables» self ⦃ (r : Scalar) =>
      (r.asNat + self.asNat) % L = 0 ∧ r.asNat < L ⦄ := by
  unfold neg.«x86_64-tables»
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
  obtain ⟨hZ, hZb⟩ := backend.serial.u64.scalar.Scalar52.ZERO_spec
  step with backend.serial.u64.scalar.Scalar52.sub_spec _ m hZb hmb
    (hZ ▸ Nat.add_pos_right _ L_pos) hmL.le as ⟨c, hc, hcL, hcb⟩
  step with Scalar52.pack_spec c hcb (lt_two_pow_256_of_lt_L hcL) as ⟨r, hr⟩
  rw [hm', Nat.add_mod_mod, hZ, Nat.zero_mod] at hc
  exact hr ▸ ⟨hc, hcL⟩

end Curve25519Dalek.scalar.NegShared0ScalarScalar

namespace Curve25519Dalek.scalar.NegShared0ScalarScalar

@[step]
theorem neg.«x86_64-no-tables_spec» (self : Scalar) :
    neg.«x86_64-no-tables» self ⦃ (r : Scalar) =>
      (r.asNat + self.asNat) % L = 0 ∧ r.asNat < L ⦄ :=
  neg.«x86_64-tables_spec» self

end Curve25519Dalek.scalar.NegShared0ScalarScalar


namespace Curve25519Dalek.scalar.NegShared0ScalarScalar

@[step]
theorem neg.«i686-tables_spec» (self : Scalar) :
    neg.«i686-tables» self ⦃ (r : Scalar) =>
      (r.asNat + self.asNat) % L = 0 ∧ r.asNat < L ⦄ := by
  unfold neg.«i686-tables»
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
  obtain ⟨hZ, hZb⟩ := backend.serial.u32.scalar.Scalar29.ZERO_spec
  step with backend.serial.u32.scalar.Scalar29.sub_spec _ m hZb hmb
    (hZ ▸ Nat.add_pos_right _ L_pos) hmL.le as ⟨c, hc, hcL, hcb⟩
  step with Scalar29.pack_spec c hcb (lt_two_pow_256_of_lt_L hcL) as ⟨r, hr⟩
  rw [hm', Nat.add_mod_mod, hZ, Nat.zero_mod] at hc
  exact hr ▸ ⟨hc, hcL⟩

end Curve25519Dalek.scalar.NegShared0ScalarScalar

namespace Curve25519Dalek.scalar.NegShared0ScalarScalar

@[step]
theorem neg.«i686-no-tables_spec» (self : Scalar) :
    neg.«i686-no-tables» self ⦃ (r : Scalar) =>
      (r.asNat + self.asNat) % L = 0 ∧ r.asNat < L ⦄ :=
  neg.«i686-tables_spec» self

end Curve25519Dalek.scalar.NegShared0ScalarScalar
namespace Curve25519Dalek.Shared0Scalar.Insts.CoreOpsArithNegScalar

@[step]
theorem neg_spec (self : Scalar) :
    neg self ⦃ (r : Scalar) =>
      (r.asNat + self.asNat) % L = 0 ∧ r.asNat < L ⦄ := by
  unfold neg
  exact dispatch_all_spec
    (scalar.NegShared0ScalarScalar.neg.«x86_64-tables_spec» self)
    (scalar.NegShared0ScalarScalar.neg.«x86_64-no-tables_spec» self)
    (scalar.NegShared0ScalarScalar.neg.«i686-tables_spec» self)
    (scalar.NegShared0ScalarScalar.neg.«i686-no-tables_spec» self)

end Curve25519Dalek.Shared0Scalar.Insts.CoreOpsArithNegScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithNegScalar

@[step]
theorem neg_spec (self : Scalar) :
    neg self ⦃ (r : Scalar) =>
      (r.asNat + self.asNat) % L = 0 ∧ r.asNat < L ⦄ := by
  unfold neg
  step*

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithNegScalar
