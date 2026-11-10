/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Helpers.Field
public import Proofs.Field.SqrtRatioI
import Proofs.Backend.Serial.U32.Field.One
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.field.FieldElement51

@[step]
theorem invsqrt_spec (self : FieldElement51) (hself : self.LimbsLt 54) :
    invsqrt self ⦃ (c : subtle.Choice) (r : FieldElement51) =>
      c.IsValid ∧ (self.asNat % p = 0 → c = 0#u8 ∧ r.asNat % p = 0) ∧
      (self.asNat % p ≠ 0 → (∃ x : ℕ, x ^ 2 * self.asNat % p = 1) →
        c = 1#u8 ∧ r.asNat ^ 2 * self.asNat % p = 1) ∧
      (self.asNat % p ≠ 0 → (¬∃ x : ℕ, x ^ 2 * self.asNat % p = 1) →
        c = 0#u8 ∧ r.asNat ^ 2 * self.asNat % p = sqrtM1) ∧
      r.asNat % p % 2 = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold invsqrt
  step as ⟨one, hone, honeb⟩
  have h1 : one.asNat % p = 1 := by
    rw [hone, one_mod_p]
  step as ⟨c, r, hcv, hu0, hv0, hsq, hnsq, hpar, hrb⟩
  rw [h1] at hv0 hsq hnsq
  refine ⟨hcv, fun h => hv0 one_ne_zero h, hsq, fun h hx => ?_, hpar, hrb⟩
  obtain ⟨hc, hr⟩ := hnsq h hx
  rw [hr, hone, mul_one, Nat.mod_eq_of_lt sqrtM1_lt_p]
  exact ⟨hc, rfl⟩

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement2625

@[step]
theorem invsqrt_spec (self : FieldElement2625) (hself : self.LimbsLt 27) :
    invsqrt self ⦃ (c : subtle.Choice) (r : FieldElement2625) =>
      c.IsValid ∧ (self.asNat % p = 0 → c = 0#u8 ∧ r.asNat % p = 0) ∧
      (self.asNat % p ≠ 0 → (∃ x : ℕ, x ^ 2 * self.asNat % p = 1) →
        c = 1#u8 ∧ r.asNat ^ 2 * self.asNat % p = 1) ∧
      (self.asNat % p ≠ 0 → (¬∃ x : ℕ, x ^ 2 * self.asNat % p = 1) →
        c = 0#u8 ∧ r.asNat ^ 2 * self.asNat % p = sqrtM1) ∧
      r.asNat % p % 2 = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold invsqrt
  step as ⟨one, hone, honeb⟩
  have h1 : one.asNat % p = 1 := by
    rw [hone, one_mod_p]
  step as ⟨c, r, hcv, hu0, hv0, hsq, hnsq, hpar, hrb⟩
  rw [h1] at hv0 hsq hnsq
  refine ⟨hcv, fun h => hv0 one_ne_zero h, hsq, fun h hx => ?_, hpar, hrb⟩
  obtain ⟨hc, hr⟩ := hnsq h hx
  rw [hr, hone, mul_one, Nat.mod_eq_of_lt sqrtM1_lt_p]
  exact ⟨hc, rfl⟩

end Curve25519Dalek.field.FieldElement2625

namespace Curve25519Dalek.Backend

variable (B : Backend)

/-- `FieldElement::invsqrt` over a backend. -/
@[expose] def invsqrtBody (x : B.F) : Result (subtle.Choice × B.F) := do
  let fe ← B.constOne
  B.sqrtRatioI fe x

/-- `invsqrtBody` is RFC 9496's `SQRT_RATIO_M1(1, x)`. -/
theorem invsqrtBody_spec (hone : B.OneSpec) (hsr : B.SqrtRatioISpec) (x : B.F)
    (hx : B.SqIn x) :
    B.invsqrtBody x ⦃ (c : subtle.Choice) (r : B.F) =>
      sqrtRatioM1 1 (B.toField x) = (decide (c = 1#u8), B.toField r) ∧ c.IsValid ∧ B.Red r ⦄ := by
  unfold invsqrtBody
  apply spec_bind hone
  rintro one ⟨One, honeb⟩
  apply spec_mono (hsr one x (B.red_sqIn honeb) hx)
  rintro ⟨c, r⟩ ⟨hv, h0, h1, h2, h3, hpar, hrb⟩
  rw [One] at h0 h1 h2 h3
  exact ⟨sqrtRatioM1_eq h0 h1 h2 h3 hpar, hv, hrb⟩

theorem U64.invsqrt_spec : U64.InvsqrtSpec := invsqrtBody_spec U64 U64.one_spec U64.sqrtRatioI_spec

theorem U32.invsqrt_spec : U32.InvsqrtSpec := invsqrtBody_spec U32 U32.one_spec U32.sqrtRatioI_spec

end Curve25519Dalek.Backend
