/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar29
import Proofs.Backend.Serial.U64.Scalar.ConditionalAddL
import Proofs.Backend.Serial.U64.Scalar.Shr1Assign
import Proofs.Helpers.AsNat
import Proofs.Helpers.Montgomery
import Proofs.Helpers.Scalar
import Proofs.Helpers.Scalar29
import Proofs.Helpers.Target
import Proofs.Scalar.AsBytes
import Proofs.Scalar.Scalar52Pack
import Proofs.Scalar.Unpack
import Proofs.Backend.Serial.U32.Scalar.ConditionalAddL
import Proofs.Backend.Serial.U32.Scalar.Shr1Assign
import Proofs.Scalar.Scalar29Pack
import Subtle.Lemmas
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar

/-- Halving modulo `L`: add `L` when odd, then shift right by one bit. -/
private theorem half_mod_L {s u1 u2 c : ℕ} (hs : s < L)
    (hu1 : u1 = if s % 2 = 0 then s else s + L) (h : 2 * u2 + c = u1) (hc : c < 2) :
    c = 0 ∧ 2 * u2 % L = s ∧ u2 < L := by
  have hL := L_mod_two
  split_ifs at hu1 with hpar
  · have hc0 : c = 0 := by omega
    refine ⟨hc0, ?_, by omega⟩
    rw [show 2 * u2 = s by omega]
    exact Nat.mod_eq_of_lt hs
  · have hc0 : c = 0 := by omega
    refine ⟨hc0, ?_, by omega⟩
    rw [show 2 * u2 = s + L by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt hs

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem div_by_2.«x86_64-tables_spec» (self : Scalar) (hself : self.asNat < L) :
    div_by_2.«x86_64-tables» self ⦃ (r : Scalar) =>
      2 * r.asNat % L = self.asNat ∧ r.asNat < L ⦄ := by
  unfold div_by_2.«x86_64-tables»
  step as ⟨a, ha⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1, hi1bv⟩
  have hpar : i1.val = self.asNat % 2 := by
    rw [hi1, UScalar.val_and]
    change i.val &&& 1 = _
    rw [Nat.and_one_is_mod, hi, ha]
    simpa [Array.getElem!_Nat_eq, Scalar.asNat_def] using
      (Array.asNat_mod_of_dvd 8 (m := 2) (by norm_num) self.bytes (by simp)).symm
  have hvalid : i1 = 0#u8 ∨ i1 = 1#u8 := (subtle.Choice.isValid_iff i1).mpr (by scalar_tac)
  step as ⟨c, hcv, hc⟩
  step as ⟨u, hu, hub⟩
  step with backend.serial.u64.scalar.Scalar52.conditional_add_l_spec u c hub hcv
    as ⟨cc, u1, hu10, hu11, hu1b⟩
  step as ⟨carry, u2, hu2, hcarry, hu2b⟩
  have hu1 : u1.asNat = if self.asNat % 2 = 0 then self.asNat else self.asNat + L := by
    rcases hvalid with h0 | h1
    · have hp : self.asNat % 2 = 0 := by rw [← hpar, h0]; rfl
      rw [ite_eq_left hp, hu10 (hc.trans h0), hu]
    · have hp : self.asNat % 2 ≠ 0 := by rw [← hpar, h1]; decide
      rw [ite_eq_right hp, hu11 (hc.trans h1), hu]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_right hself L)
        (by rw [← Nat.two_mul]; exact backend.serial.u64.scalar.two_mul_L_lt_montgomeryRadix.le))
  obtain ⟨hcarry0, hr2, hrL⟩ := half_mod_L hself hu1 hu2 hcarry
  step
  step with Scalar52.pack_spec u2 hu2b (lt_two_pow_256_of_lt_L hrL) as ⟨r, hr⟩
  rw [hr]
  exact ⟨hr2, hrL⟩

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem div_by_2.«x86_64-no-tables_spec» (self : Scalar) (hself : self.asNat < L) :
    div_by_2.«x86_64-no-tables» self ⦃ (r : Scalar) =>
      2 * r.asNat % L = self.asNat ∧ r.asNat < L ⦄ :=
  div_by_2.«x86_64-tables_spec» self hself

end Curve25519Dalek.scalar.Scalar


namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem div_by_2.«i686-tables_spec» (self : Scalar) (hself : self.asNat < L) :
    div_by_2.«i686-tables» self ⦃ (r : Scalar) =>
      2 * r.asNat % L = self.asNat ∧ r.asNat < L ⦄ := by
  unfold div_by_2.«i686-tables»
  step as ⟨a, ha⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1, hi1bv⟩
  have hpar : i1.val = self.asNat % 2 := by
    rw [hi1, UScalar.val_and]
    change i.val &&& 1 = _
    rw [Nat.and_one_is_mod, hi, ha]
    simpa [Array.getElem!_Nat_eq, Scalar.asNat_def] using
      (Array.asNat_mod_of_dvd 8 (m := 2) (by norm_num) self.bytes (by simp)).symm
  have hvalid : i1 = 0#u8 ∨ i1 = 1#u8 := (subtle.Choice.isValid_iff i1).mpr (by scalar_tac)
  step as ⟨c, hcv, hc⟩
  step as ⟨u, hu, hub⟩
  step with backend.serial.u32.scalar.Scalar29.conditional_add_l_spec u c hub hcv
    as ⟨cc, u1, hu10, hu11, hu1b⟩
  step as ⟨carry, u2, hu2, hcarry, hu2b⟩
  have hu1 : u1.asNat = if self.asNat % 2 = 0 then self.asNat else self.asNat + L := by
    rcases hvalid with h0 | h1
    · have hp : self.asNat % 2 = 0 := by rw [← hpar, h0]; rfl
      rw [ite_eq_left hp, hu10 (hc.trans h0), hu]
    · have hp : self.asNat % 2 ≠ 0 := by rw [← hpar, h1]; decide
      rw [ite_eq_right hp, hu11 (hc.trans h1), hu]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_right hself L)
        (by rw [← Nat.two_mul]; exact backend.serial.u32.scalar.two_mul_L_lt_montgomeryRadix.le))
  obtain ⟨hcarry0, hr2, hrL⟩ := half_mod_L hself hu1 hu2 hcarry
  step
  step with Scalar29.pack_spec u2 hu2b (lt_two_pow_256_of_lt_L hrL) as ⟨r, hr⟩
  rw [hr]
  exact ⟨hr2, hrL⟩

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem div_by_2.«i686-no-tables_spec» (self : Scalar) (hself : self.asNat < L) :
    div_by_2.«i686-no-tables» self ⦃ (r : Scalar) =>
      2 * r.asNat % L = self.asNat ∧ r.asNat < L ⦄ :=
  div_by_2.«i686-tables_spec» self hself

end Curve25519Dalek.scalar.Scalar
namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem div_by_2_spec (self : Scalar) (hself : self.asNat < L) :
    div_by_2 self ⦃ (r : Scalar) =>
      2 * r.asNat % L = self.asNat ∧ r.asNat < L ⦄ := by
  unfold div_by_2
  exact dispatch_all_spec
    (div_by_2.«x86_64-tables_spec» self hself)
    (div_by_2.«x86_64-no-tables_spec» self hself)
    (div_by_2.«i686-tables_spec» self hself)
    (div_by_2.«i686-no-tables_spec» self hself)

end Curve25519Dalek.scalar.Scalar
