/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Defs.FieldElement51
public import Proofs.Helpers.Backend.U32
public import Proofs.Helpers.Backend.U64
public import Curve25519.Basic
public section

/-! # `FieldElement::pow22501`

The addition chain for `x ^ (2^250 - 1)` (and `x ^ 11` on the way), proved once over a
`Backend` in `ZMod p`; the specs of both backends follow. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.Backend

variable (B : Backend)

/-- `FieldElement::pow22501` over a backend. -/
@[expose] def pow22501Body (x : B.F) : Result (B.F × B.F) := do
  let t0 ← B.square x
  let fe ← B.square t0
  let t1 ← B.square fe
  let t2 ← B.mul x t1
  let t3 ← B.mul t0 t2
  let t4 ← B.square t3
  let t5 ← B.mul t2 t4
  let t6 ← B.pow2k t5 5#u32
  let t7 ← B.mul t6 t5
  let t8 ← B.pow2k t7 10#u32
  let t9 ← B.mul t8 t7
  let t10 ← B.pow2k t9 20#u32
  let t11 ← B.mul t10 t9
  let t12 ← B.pow2k t11 10#u32
  let t13 ← B.mul t12 t7
  let t14 ← B.pow2k t13 50#u32
  let t15 ← B.mul t14 t13
  let t16 ← B.pow2k t15 100#u32
  let t17 ← B.mul t16 t15
  let t18 ← B.pow2k t17 50#u32
  let t19 ← B.mul t18 t13
  ok (t19, t3)

private theorem two_pow_sub_one_mul_add (a b : ℕ) :
    (2 ^ a - 1) * 2 ^ b + (2 ^ b - 1) = 2 ^ (a + b) - 1 := by
  have ha : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hb : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hab : 1 ≤ 2 ^ (a + b) := Nat.one_le_two_pow
  zify [ha, hb, hab]
  ring

/-- One step of the addition chain: from `x ^ (2^a - 1)` and `x ^ (2^b - 1)` to
`x ^ (2^(a+b) - 1)`, via `b` squarings and a multiplication. -/
private theorem pow_step {x y z u w : ZMod p} (a b c : ℕ) (hc : a + b = c)
    (hy : y = x ^ (2 ^ a - 1)) (hz : z = y ^ 2 ^ b) (hu : u = x ^ (2 ^ b - 1)) (hw : w = z * u) :
    w = x ^ (2 ^ c - 1) := by
  rw [hw, hz, hu, hy, ← pow_mul, ← pow_add, two_pow_sub_one_mul_add, hc]

/-- `pow22501Body` computes `(x ^ (2^250 - 1), x ^ 11)`. -/
theorem pow22501Body_spec (hsq : B.SquareSpec) (hmul : B.MulSpec) (hp2k : B.Pow2kSpec)
    (x : B.F) (hx : B.SqIn x) :
    B.pow22501Body x ⦃ (t19 t3 : B.F) =>
      B.toField t19 = B.toField x ^ (2 ^ 250 - 1) ∧ B.toField t3 = B.toField x ^ 11 ∧
        B.Red t19 ∧ B.Red t3 ⦄ := by
  unfold pow22501Body
  step with hsq x hx as ⟨t0, ht0, ht0'⟩
  step with hsq t0 (B.red_sqIn ht0') as ⟨fe, hfe, hfe'⟩
  step with hsq fe (B.red_sqIn hfe') as ⟨t1, ht1, ht1'⟩
  step with hmul x t1 (B.sqIn_mulIn hx) (B.red_mulIn ht1') as ⟨t2, ht2, ht2'⟩
  step with hmul t0 t2 (B.red_mulIn ht0') (B.red_mulIn ht2') as ⟨t3, ht3, ht3'⟩
  step with hsq t3 (B.red_sqIn ht3') as ⟨t4, ht4, ht4'⟩
  step with hmul t2 t4 (B.red_mulIn ht2') (B.red_mulIn ht4') as ⟨t5, ht5, ht5'⟩
  step with hp2k t5 5#u32 (by decide) (B.red_sqIn ht5') as ⟨t6, ht6, ht6'⟩
  step with hmul t6 t5 (B.red_mulIn ht6') (B.red_mulIn ht5') as ⟨t7, ht7, ht7'⟩
  step with hp2k t7 10#u32 (by decide) (B.red_sqIn ht7') as ⟨t8, ht8, ht8'⟩
  step with hmul t8 t7 (B.red_mulIn ht8') (B.red_mulIn ht7') as ⟨t9, ht9, ht9'⟩
  step with hp2k t9 20#u32 (by decide) (B.red_sqIn ht9') as ⟨t10, ht10, ht10'⟩
  step with hmul t10 t9 (B.red_mulIn ht10') (B.red_mulIn ht9') as ⟨t11, ht11, ht11'⟩
  step with hp2k t11 10#u32 (by decide) (B.red_sqIn ht11') as ⟨t12, ht12, ht12'⟩
  step with hmul t12 t7 (B.red_mulIn ht12') (B.red_mulIn ht7') as ⟨t13, ht13, ht13'⟩
  step with hp2k t13 50#u32 (by decide) (B.red_sqIn ht13') as ⟨t14, ht14, ht14'⟩
  step with hmul t14 t13 (B.red_mulIn ht14') (B.red_mulIn ht13') as ⟨t15, ht15, ht15'⟩
  step with hp2k t15 100#u32 (by decide) (B.red_sqIn ht15') as ⟨t16, ht16, ht16'⟩
  step with hmul t16 t15 (B.red_mulIn ht16') (B.red_mulIn ht15') as ⟨t17, ht17, ht17'⟩
  step with hp2k t17 50#u32 (by decide) (B.red_sqIn ht17') as ⟨t18, ht18, ht18'⟩
  step with hmul t18 t13 (B.red_mulIn ht18') (B.red_mulIn ht13') as ⟨t19, ht19, ht19'⟩
  set X := B.toField x
  have h2 : B.toField t2 = X ^ 9 := by rw [ht2, ht1, hfe, ht0]; ring
  have h3 : B.toField t3 = X ^ 11 := by rw [ht3, h2, ht0]; ring
  have h5 : B.toField t5 = X ^ (2 ^ 5 - 1) := by rw [ht5, ht4, h3, h2]; ring
  have h7 := pow_step 5 5 10 rfl h5 ht6 h5 ht7
  have h9 := pow_step 10 10 20 rfl h7 ht8 h7 ht9
  have h11 := pow_step 20 20 40 rfl h9 ht10 h9 ht11
  have h13 := pow_step 40 10 50 rfl h11 ht12 h7 ht13
  have h15 := pow_step 50 50 100 rfl h13 ht14 h13 ht15
  have h17 := pow_step 100 100 200 rfl h15 ht16 h15 ht17
  exact ⟨pow_step 200 50 250 rfl h17 ht18 h13 ht19, h3, ht19', ht3'⟩

end Curve25519Dalek.Backend

namespace Curve25519Dalek.field.FieldElement51

theorem pow22501_eq : pow22501 = Backend.pow22501Body Backend.U64 := rfl

@[step]
theorem pow22501_spec (self : FieldElement51) (hself : self.LimbsLt 54) :
    pow22501 self ⦃ (t19 t3 : FieldElement51) =>
      t19.asNat % p = self.asNat ^ (2 ^ 250 - 1) % p ∧ t3.asNat % p = self.asNat ^ 11 % p ∧
      t19.LimbsLt 52 ∧ t3.LimbsLt 52 ⦄ := by
  rw [pow22501_eq]
  apply spec_mono (Backend.pow22501Body_spec Backend.U64 Backend.U64.square_spec
    Backend.U64.mul_spec Backend.U64.pow2k_spec self hself)
  rintro ⟨t19, t3⟩ ⟨h19, h3, b19, b3⟩
  exact ⟨Backend.mod_eq_of_toField_eq_pow h19, Backend.mod_eq_of_toField_eq_pow h3, b19, b3⟩

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement2625

theorem pow22501_eq : pow22501 = Backend.pow22501Body Backend.U32 := rfl

@[step]
theorem pow22501_spec (self : FieldElement2625) (hself : self.LimbsLt 27) :
    pow22501 self ⦃ (t19 t3 : FieldElement2625) =>
      t19.asNat % p = self.asNat ^ (2 ^ 250 - 1) % p ∧ t3.asNat % p = self.asNat ^ 11 % p ∧
      t19.LimbsLt 26 ∧ t3.LimbsLt 26 ⦄ := by
  rw [pow22501_eq]
  apply spec_mono (Backend.pow22501Body_spec Backend.U32 Backend.U32.square_spec
    Backend.U32.mul_spec Backend.U32.pow2k_spec self hself)
  rintro ⟨t19, t3⟩ ⟨h19, h3, b19, b3⟩
  exact ⟨Backend.mod_eq_of_toField_eq_pow h19, Backend.mod_eq_of_toField_eq_pow h3, b19, b3⟩

end Curve25519Dalek.field.FieldElement2625

namespace Curve25519Dalek.Backend

theorem U64.pow22501_spec : U64.Pow22501Spec :=
  pow22501Body_spec U64 U64.square_spec U64.mul_spec U64.pow2k_spec

theorem U32.pow22501_spec : U32.Pow22501Spec :=
  pow22501Body_spec U32 U32.square_spec U32.mul_spec U32.pow2k_spec

end Curve25519Dalek.Backend
