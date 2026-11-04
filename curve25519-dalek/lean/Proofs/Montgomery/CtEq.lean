/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Montgomery
public import Subtle.Contract
import Proofs.Backend.Serial.U64.Field.FromBytes
import Proofs.Field.CtEq
import Proofs.Helpers.Target
import Proofs.Backend.Serial.U32.Field.FromBytes
public section

/-! # `ConstantTimeEq for MontgomeryPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.montgomery.ConstantTimeEqMontgomeryPoint

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `ConstantTimeEq for MontgomeryPoint`: equality of the encoded `u`-coordinates (bit `255`
masked, reduced modulo `p`). -/
@[step]
theorem ct_eq.«x86_64-tables_spec» (self other : MontgomeryPoint) :
    ct_eq.«x86_64-tables» self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.u = other.u) ⦄ := by
  unfold ct_eq.«x86_64-tables»
  step as ⟨a, ha, ha_lt⟩
  step as ⟨b, hb, hb_lt⟩
  step as ⟨c, hcv, hc1, hc0⟩
  have hu : self.u = other.u ↔ a.asNat % p = b.asNat % p := by
    rw [MontgomeryPoint.u_def, MontgomeryPoint.u_def, decodeU, decodeU, ha, hb,
      ZMod.natCast_eq_natCast_iff', MontgomeryPoint.asNat_def, MontgomeryPoint.asNat_def]
  rw [hu]
  refine ⟨hcv, fun h => ?_, hc1⟩
  by_contra hne
  rw [hc0 hne] at h
  exact absurd h (by decide)

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- `ConstantTimeEq for MontgomeryPoint`: equality of the encoded `u`-coordinates (bit `255`
masked, reduced modulo `p`). -/
@[step]
theorem ct_eq.«i686-tables_spec» (self other : MontgomeryPoint) :
    ct_eq.«i686-tables» self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.u = other.u) ⦄ := by
  unfold ct_eq.«i686-tables»
  step as ⟨a, ha, ha_lt⟩
  step as ⟨b, hb, hb_lt⟩
  step as ⟨c, hcv, hc1, hc0⟩
  have hu : self.u = other.u ↔ a.asNat % p = b.asNat % p := by
    rw [MontgomeryPoint.u_def, MontgomeryPoint.u_def, decodeU, decodeU, ha, hb,
      ZMod.natCast_eq_natCast_iff', MontgomeryPoint.asNat_def, MontgomeryPoint.asNat_def]
  rw [hu]
  refine ⟨hcv, fun h => ?_, hc1⟩
  by_contra hne
  rw [hc0 hne] at h
  exact absurd h (by decide)

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `ConstantTimeEq for MontgomeryPoint`: equality of the encoded `u`-coordinates (bit `255`
masked, reduced modulo `p`). -/
@[step]
theorem ct_eq.«x86_64-no-tables_spec» (self other : MontgomeryPoint) :
    ct_eq.«x86_64-no-tables» self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.u = other.u) ⦄ := by
  unfold ct_eq.«x86_64-no-tables»
  step as ⟨a, ha, ha_lt⟩
  step as ⟨b, hb, hb_lt⟩
  step as ⟨c, hcv, hc1, hc0⟩
  have hu : self.u = other.u ↔ a.asNat % p = b.asNat % p := by
    rw [MontgomeryPoint.u_def, MontgomeryPoint.u_def, decodeU, decodeU, ha, hb,
      ZMod.natCast_eq_natCast_iff', MontgomeryPoint.asNat_def, MontgomeryPoint.asNat_def]
  rw [hu]
  refine ⟨hcv, fun h => ?_, hc1⟩
  by_contra hne
  rw [hc0 hne] at h
  exact absurd h (by decide)

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- `ConstantTimeEq for MontgomeryPoint`: equality of the encoded `u`-coordinates (bit `255`
masked, reduced modulo `p`). -/
@[step]
theorem ct_eq.«i686-no-tables_spec» (self other : MontgomeryPoint) :
    ct_eq.«i686-no-tables» self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (c = 1#u8 ↔ self.u = other.u) ⦄ := by
  unfold ct_eq.«i686-no-tables»
  step as ⟨a, ha, ha_lt⟩
  step as ⟨b, hb, hb_lt⟩
  step as ⟨c, hcv, hc1, hc0⟩
  have hu : self.u = other.u ↔ a.asNat % p = b.asNat % p := by
    rw [MontgomeryPoint.u_def, MontgomeryPoint.u_def, decodeU, decodeU, ha, hb,
      ZMod.natCast_eq_natCast_iff', MontgomeryPoint.asNat_def, MontgomeryPoint.asNat_def]
  rw [hu]
  refine ⟨hcv, fun h => ?_, hc1⟩
  by_contra hne
  rw [hc0 hne] at h
  exact absurd h (by decide)

end Curve25519Dalek.montgomery.ConstantTimeEqMontgomeryPoint

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.SubtleConstantTimeEq

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `ConstantTimeEq for MontgomeryPoint`: equality of the encoded `u`-coordinates (bit `255`
masked, reduced modulo `p`; x86_64 targets). -/
@[step]
theorem ct_eq_spec (self other : MontgomeryPoint) :
    ct_eq self other ⦃ (c : subtle.Choice) => c.IsValid ∧ (c = 1#u8 ↔ self.u = other.u) ⦄ := by
  unfold ct_eq
  exact dispatch_all_spec
    (ConstantTimeEqMontgomeryPoint.ct_eq.«x86_64-tables_spec» self other)
    (ConstantTimeEqMontgomeryPoint.ct_eq.«x86_64-no-tables_spec» self other)
    (ConstantTimeEqMontgomeryPoint.ct_eq.«i686-tables_spec» self other)
    (ConstantTimeEqMontgomeryPoint.ct_eq.«i686-no-tables_spec» self other)

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.SubtleConstantTimeEq
