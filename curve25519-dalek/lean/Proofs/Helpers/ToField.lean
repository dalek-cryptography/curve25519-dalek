/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Ristretto.Encoding.Defs
public import Curve25519.X25519
public import Defs.FieldElement51
public import Subtle.Contract
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
import Proofs.Helpers.ZMod
public section

/-! # From the field specs to `toField`

The field specs state their results on `asNat` modulo `p` (`r.asNat % p = a.asNat * b.asNat % p`,
`(r.asNat + b.asNat) % p = a.asNat % p`, `c.val = a.asNat % p % 2`, …); the point specs are
stated on `toField : FieldElement51 → ZMod p`. One bridge lemma per spec shape: `toField_mul_of_mod`
for `mul`, `toField_sq_of_mod` for `square`, `toField_two_mul_sq_of_mod` for `square2`,
`toField_pow_of_mod` for `pow2k`, `toField_add_of_limbs` for `add`, `toField_sub_of_mod` for
`sub`, `toField_neg_of_mod` for `neg`/`negate`, `toField_inv_of_mod` for `invert`,
`toField_eq_of_mod_eq` for `reduce`, `toField_repeat_zero` for `zeroize`,
`toField_eq_decodeU_of_asNat_eq` for `from_bytes`, `toField_val` for `to_bytes`,
`eq_one_iff_isNeg_toField` for `is_negative`,
`eq_one_iff_toField_eq_zero` for `is_zero`, `eq_one_iff_toField_eq` for `ct_eq`,
`exists_sq_mul_mod_iff_isSquare_div` for the square-root tests, and `sqrtRatioM1_eq_of_spec`,
`sqrtRatioM1_one_eq_of_spec`: `sqrt_ratio_i` and `invsqrt` compute RFC 9496's `sqrtRatioM1`. -/

open Aeneas Aeneas.Std curve25519

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-! ### Casting the specs' congruences -/

/-- The specs' form `a % p = b % p` as an equality in `ZMod p`. -/
theorem natCast_eq_natCast_of_mod_eq {a b : ℕ} (h : a % p = b % p) : (a : ZMod p) = b :=
  (ZMod.natCast_eq_natCast_iff' a b p).mpr h

theorem one_mod_p : 1 % p = 1 :=
  Nat.mod_eq_of_lt (by have := two_lt_p; omega)

theorem toField_val (a : FieldElement51) : a.toField.val = a.asNat % p := by
  rw [toField_def, ZMod.val_natCast]

theorem toField_eq_toField_iff {a b : FieldElement51} :
    a.toField = b.toField ↔ a.asNat % p = b.asNat % p := by
  rw [toField_def, toField_def, ZMod.natCast_eq_natCast_iff']

theorem toField_eq_of_mod_eq {a b : FieldElement51} (h : a.asNat % p = b.asNat % p) :
    a.toField = b.toField :=
  toField_eq_toField_iff.mpr h

theorem toField_eq_natCast_iff {a : FieldElement51} {n : ℕ} :
    a.toField = n ↔ a.asNat % p = n % p := by
  rw [toField_def, ZMod.natCast_eq_natCast_iff']

theorem toField_eq_natCast_of_mod_eq {a : FieldElement51} {n : ℕ} (h : a.asNat % p = n) :
    a.toField = n := by
  subst h
  rw [toField_def, ZMod.natCast_mod]

theorem toField_eq_zero_iff {a : FieldElement51} : a.toField = 0 ↔ a.asNat % p = 0 := by
  rw [toField_def, ZMod.natCast_eq_zero_iff_mod]

theorem toField_ne_zero_iff {a : FieldElement51} : a.toField ≠ 0 ↔ a.asNat % p ≠ 0 :=
  toField_eq_zero_iff.not

theorem toField_eq_one_iff {a : FieldElement51} : a.toField = 1 ↔ a.asNat % p = 1 := by
  rw [← Nat.cast_one, toField_eq_natCast_iff, one_mod_p]

/-! ### Arithmetic -/

theorem toField_mul_of_mod {r a b : FieldElement51} (h : r.asNat % p = a.asNat * b.asNat % p) :
    r.toField = a.toField * b.toField := by
  have h' := natCast_eq_natCast_of_mod_eq h
  push_cast at h'
  rw [toField_def, toField_def, toField_def, h']

theorem toField_sq_of_mod {r a : FieldElement51} (h : r.asNat % p = a.asNat ^ 2 % p) :
    r.toField = a.toField ^ 2 := by
  have h' := natCast_eq_natCast_of_mod_eq h
  push_cast at h'
  rw [toField_def, toField_def, h']

theorem toField_two_mul_sq_of_mod {r a : FieldElement51} (h : r.asNat % p = 2 * a.asNat ^ 2 % p) :
    r.toField = 2 * a.toField ^ 2 := by
  have h' := natCast_eq_natCast_of_mod_eq h
  push_cast at h'
  rw [toField_def, toField_def, h']

theorem toField_pow_of_mod {r a : FieldElement51} {k : ℕ} (h : r.asNat % p = a.asNat ^ k % p) :
    r.toField = a.toField ^ k := by
  have h' := natCast_eq_natCast_of_mod_eq h
  push_cast at h'
  rw [toField_def, toField_def, h']

/-- The shape of `add_spec`: limbs add without reduction. -/
theorem toField_add_of_limbs {r a b : FieldElement51}
    (h : ∀ i : ℕ, i < 5 → r[i]!.val = a[i]!.val + b[i]!.val) :
    r.toField = a.toField + b.toField := by
  have h' := Array.asNat_add_eq 51 a b r fun i hi => (h i (by simpa using hi)).symm
  rw [toField_def, toField_def, toField_def, asNat_def, asNat_def, asNat_def, ← h']
  push_cast
  rfl

theorem toField_sub_of_mod {r a b : FieldElement51} (h : (r.asNat + b.asNat) % p = a.asNat % p) :
    r.toField = a.toField - b.toField := by
  have h' := natCast_eq_natCast_of_mod_eq h
  push_cast at h'
  rw [toField_def, toField_def, toField_def, ← h', add_sub_cancel_right]

theorem toField_neg_of_mod {r a : FieldElement51} (h : (r.asNat + a.asNat) % p = 0) :
    r.toField = -a.toField := by
  have h' : ((r.asNat + a.asNat : ℕ) : ZMod p) = 0 := ZMod.natCast_eq_zero_iff_mod.mpr h
  push_cast at h'
  rw [toField_def, toField_def]
  exact eq_neg_of_add_eq_zero_left h'

/-- The shape of `invert_spec`: the inverse, `0` at `0` (Lean's `0⁻¹ = 0`). -/
theorem toField_inv_of_mod {r a : FieldElement51} (h1 : a.asNat % p ≠ 0 → r.asNat * a.asNat % p = 1)
    (h0 : a.asNat % p = 0 → r.asNat % p = 0) : r.toField = a.toField⁻¹ := by
  by_cases ha : a.asNat % p = 0
  · rw [toField_eq_zero_iff.mpr (h0 ha), toField_eq_zero_iff.mpr ha, inv_zero]
  · have h' := natCast_eq_natCast_of_mod_eq ((h1 ha).trans one_mod_p.symm)
    push_cast at h'
    rw [toField_def, toField_def]
    exact eq_inv_of_mul_eq_one_left h'

/-- The shape of `invert_batch_spec` (entry by entry): the inverse, with zeros left in place, so
`0⁻¹ = 0`; limbs `< 2^52` in, `< 2^52` out. -/
theorem toField_inv_of_batch {r a : FieldElement51} (h0 : a.asNat % p = 0 → r = a)
    (h1 : a.asNat % p ≠ 0 → r.asNat * a.asNat % p = 1 ∧ r.LimbsLt 52)
    (ha : a.LimbsLt 52) :
    r.toField = a.toField⁻¹ ∧ r.LimbsLt 52 := by
  by_cases hz : a.asNat % p = 0
  · rw [h0 hz, toField_eq_zero_iff.mpr hz, inv_zero]
    exact ⟨rfl, ha⟩
  · obtain ⟨hm, hb⟩ := h1 hz
    exact ⟨toField_inv_of_mod (fun _ => hm) (fun h => absurd h hz), hb⟩

/-! ### Bytes -/

/-- The shape of `from_bytes_spec`: the value of the low `255` bits, i.e. RFC 7748's
`decodeUCoordinate`. -/
theorem toField_eq_decodeU_of_asNat_eq {r : FieldElement51} {n : ℕ} (h : r.asNat = n % 2 ^ 255) :
    r.toField = decodeU n := by
  rw [toField_def, h]
  rfl

/-- The shape of `to_bytes_spec`: the canonical representative. -/
theorem asNat_eq_val_of_mod {s : Array U8 32#usize} {a : FieldElement51}
    (h : s.asNat 8 = a.asNat % p) : s.asNat 8 = a.toField.val := by
  rw [toField_val, h]

/-! ### Limb bounds -/

theorem limbs_lt_of_le {a : FieldElement51} {k l : ℕ} (hkl : k ≤ l)
    (h : a.LimbsLt k) : a.LimbsLt l :=
  fun i hi => (h i hi).trans_le (Nat.pow_le_pow_right two_pos hkl)

/-- The limbs of `add_spec`'s output: one bit more than its inputs. -/
theorem limbs_add_lt {r a b : FieldElement51} {k : ℕ}
    (h : ∀ i : ℕ, i < 5 → r[i]!.val = a[i]!.val + b[i]!.val) (ha : a.LimbsLt k)
    (hb : b.LimbsLt k) : r.LimbsLt (k + 1) := fun i hi => by
  rw [h i hi, pow_succ]
  have := ha i hi
  have := hb i hi
  scalar_tac

/-- The constants `ZERO`, `ONE` and `EDWARDS_D` as field elements. -/
theorem toField_eq_zero_of_asNat {a : FieldElement51} (h : a.asNat = 0) : a.toField = 0 := by
  rw [toField_def, h, Nat.cast_zero]

theorem toField_eq_one_of_asNat {a : FieldElement51} (h : a.asNat = 1) : a.toField = 1 := by
  rw [toField_def, h, Nat.cast_one]

/-- A field element whose limbs have a numeral value `n ≥ 2` (the curve constants). -/
theorem toField_eq_ofNat_of_asNat {a : FieldElement51} {n : ℕ} [n.AtLeastTwo] (h : a.asNat = n) :
    a.toField = (OfNat.ofNat n : ZMod p) := by
  rw [toField_def, h]
  rfl

theorem toField_eq_d_of_asNat {a : FieldElement51} (h : a.asNat = d.val) : a.toField = d := by
  rw [toField_def, h, ZMod.natCast_zmod_val]

theorem toField_eq_two_mul_d_of_asNat {a : FieldElement51} (h : a.asNat = (2 * d).val) :
    a.toField = 2 * d := by
  rw [toField_def, h, ZMod.natCast_zmod_val]

/-- The zeroized field element `[0, 0, 0, 0, 0]`. -/
theorem asNat_repeat_zero : FieldElement51.asNat (Array.repeat 5#usize 0#u64) = 0 := by
  rw [asNat_def, Array.asNat_eq_sum]
  exact Finset.sum_eq_zero fun i hi => by
    rw [Array.getElem!_repeat 0#u64 (by simpa using Finset.mem_range.mp hi)]
    rfl

theorem toField_repeat_zero : FieldElement51.toField (Array.repeat 5#usize 0#u64) = 0 :=
  toField_eq_zero_of_asNat asNat_repeat_zero

theorem limbs_repeat_zero_lt (k : ℕ) : FieldElement51.LimbsLt k (Array.repeat 5#usize 0#u64) :=
  fun i hi => by
    rw [Array.getElem!_repeat 0#u64 (by simpa using hi)]
    exact Nat.two_pow_pos k

/-! ### Choices -/

/-- The shape of `is_negative_spec`. -/
theorem eq_one_iff_isNeg_toField {c : subtle.Choice} {a : FieldElement51}
    (h : c.val = a.asNat % p % 2) : c = 1#u8 ↔ a.toField.IsNeg := by
  rw [ZMod.isNeg_iff, toField_val, ← h]
  constructor
  · rintro rfl
    rfl
  · intro h1
    exact UScalar.eq_of_val_eq h1

theorem eq_zero_iff_not_isNeg_toField {c : subtle.Choice} {a : FieldElement51} (hc : c.IsValid)
    (h : c.val = a.asNat % p % 2) : c = 0#u8 ↔ ¬ a.toField.IsNeg := by
  rw [← eq_one_iff_isNeg_toField h]
  rcases hc with rfl | rfl <;> simp

/-- A choice that is `1` exactly when `P` holds selects between two values (the shape of
`conditional_assign`/`conditional_negate` results). -/
theorem eq_ite_of_choice {c : subtle.Choice} {P : Prop} [Decidable P] {α : Type} {r a b : α}
    (hc : c.IsValid) (hP : c = 1#u8 ↔ P) (h0 : c = 0#u8 → r = a) (h1 : c = 1#u8 → r = b) :
    r = if P then b else a := by
  rcases hc with rfl | rfl
  · rw [ite_eq_right (fun h => absurd (hP.mpr h) (by decide)), h0 rfl]
  · rw [ite_eq_left (hP.mp rfl), h1 rfl]

/-- The shape of `is_zero_spec`. -/
theorem eq_one_iff_toField_eq_zero {c : subtle.Choice} {a : FieldElement51}
    (h1 : a.asNat % p = 0 → c = 1#u8) (h0 : a.asNat % p ≠ 0 → c = 0#u8) :
    c = 1#u8 ↔ a.toField = 0 := by
  rw [toField_eq_zero_iff]
  refine ⟨fun hc => ?_, h1⟩
  by_contra ha
  rw [h0 ha] at hc
  exact absurd hc (by decide)

/-- The shape of `ct_eq_spec`. -/
theorem eq_one_iff_toField_eq {c : subtle.Choice} {a b : FieldElement51}
    (h1 : a.asNat % p = b.asNat % p → c = 1#u8) (h0 : a.asNat % p ≠ b.asNat % p → c = 0#u8) :
    c = 1#u8 ↔ a.toField = b.toField := by
  rw [toField_eq_toField_iff]
  refine ⟨fun hc => ?_, h1⟩
  by_contra hab
  rw [h0 hab] at hc
  exact absurd hc (by decide)

/-! ### Square roots -/

/-- The specs' square-root test `∃ x : ℕ, x² v ≡ u` is `IsSquare (u / v)` (for `v ≢ 0`). -/
theorem exists_sq_mul_mod_iff_isSquare_div' {u v : ℕ} (hv : v % p ≠ 0) :
    (∃ x : ℕ, x ^ 2 * v % p = u % p) ↔ IsSquare ((u : ZMod p) / v) := by
  have hv' : (v : ZMod p) ≠ 0 := fun h => hv (ZMod.natCast_eq_zero_iff_mod.mp h)
  constructor
  · rintro ⟨x, hx⟩
    have h' := natCast_eq_natCast_of_mod_eq hx
    push_cast at h'
    exact ⟨(x : ZMod p), by rw [← h', ← sq, mul_div_assoc, div_self hv', mul_one]⟩
  · rintro ⟨r, hr⟩
    refine ⟨r.val, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    rw [ZMod.natCast_zmod_val, sq, ← hr, div_mul_cancel₀ _ hv']

theorem exists_sq_mul_mod_iff_isSquare_div {u v : FieldElement51} (hv : v.asNat % p ≠ 0) :
    (∃ x : ℕ, x ^ 2 * v.asNat % p = u.asNat % p) ↔ IsSquare (u.toField / v.toField) := by
  rw [toField_def, toField_def]
  exact exists_sq_mul_mod_iff_isSquare_div' hv

theorem toField_sq_mul_of_mod {r v u : FieldElement51}
    (h : r.asNat ^ 2 * v.asNat % p = u.asNat % p) : r.toField ^ 2 * v.toField = u.toField := by
  have h' := natCast_eq_natCast_of_mod_eq h
  push_cast at h'
  rw [toField_def, toField_def, toField_def, h']

theorem toField_sq_mul_of_mod_sqrtM1 {r v u : FieldElement51}
    (h : r.asNat ^ 2 * v.asNat % p = sqrtM1 * u.asNat % p) :
    r.toField ^ 2 * v.toField = sqrtM1 * u.toField := by
  have h' := natCast_eq_natCast_of_mod_eq h
  push_cast at h'
  rw [toField_def, toField_def, toField_def, h']

theorem not_isNeg_toField_of_mod {r : FieldElement51} (h : r.asNat % p % 2 = 0) :
    ¬ r.toField.IsNeg := by
  rw [ZMod.not_isNeg_iff, toField_val]
  exact h

/-- **`sqrt_ratio_i` computes `sqrtRatioM1`**: from the conjuncts of `sqrt_ratio_i_spec`. -/
theorem sqrtRatioM1_eq_of_spec {u v r : FieldElement51} {c : subtle.Choice}
    (h0 : u.asNat % p = 0 → c = 1#u8 ∧ r.asNat % p = 0)
    (h1 : u.asNat % p ≠ 0 → v.asNat % p = 0 → c = 0#u8 ∧ r.asNat % p = 0)
    (h2 : v.asNat % p ≠ 0 → (∃ x : ℕ, x ^ 2 * v.asNat % p = u.asNat % p) →
      c = 1#u8 ∧ r.asNat ^ 2 * v.asNat % p = u.asNat % p)
    (h3 : v.asNat % p ≠ 0 → (¬∃ x : ℕ, x ^ 2 * v.asNat % p = u.asNat % p) →
      c = 0#u8 ∧ r.asNat ^ 2 * v.asNat % p = sqrtM1 * u.asNat % p)
    (hpar : r.asNat % p % 2 = 0) :
    sqrtRatioM1 u.toField v.toField = (decide (c = 1#u8), r.toField) := by
  have hneg := not_isNeg_toField_of_mod hpar
  by_cases hu : u.asNat % p = 0
  · obtain ⟨rfl, hr⟩ := h0 hu
    rw [toField_eq_zero_iff.mpr hu, toField_eq_zero_iff.mpr hr, sqrtRatioM1_zero_left,
      decide_eq_true rfl]
  by_cases hv : v.asNat % p = 0
  · obtain ⟨rfl, hr⟩ := h1 hu hv
    rw [toField_eq_zero_iff.mpr hv, toField_eq_zero_iff.mpr hr,
      sqrtRatioM1_zero_right (toField_ne_zero_iff.mpr hu), decide_eq_false (by decide)]
  have hv' := toField_ne_zero_iff.mpr hv
  by_cases hsq : ∃ x : ℕ, x ^ 2 * v.asNat % p = u.asNat % p
  · obtain ⟨rfl, hr⟩ := h2 hv hsq
    rw [sqrtRatioM1_eq_of_mul_sq_eq hv' (by rw [mul_comm]; exact toField_sq_mul_of_mod hr) hneg,
      decide_eq_true rfl]
  · obtain ⟨rfl, hr⟩ := h3 hv hsq
    rw [sqrtRatioM1_eq_of_mul_sq_eq_sqrtM1_mul (toField_ne_zero_iff.mpr hu) hv'
      (by rw [mul_comm]; exact toField_sq_mul_of_mod_sqrtM1 hr) hneg, decide_eq_false (by decide)]

/-- **`invsqrt` computes `sqrtRatioM1 1`**: from the conjuncts of `invsqrt_spec`. -/
theorem sqrtRatioM1_one_eq_of_spec {v r : FieldElement51} {c : subtle.Choice}
    (h0 : v.asNat % p = 0 → c = 0#u8 ∧ r.asNat % p = 0)
    (h1 : v.asNat % p ≠ 0 → (∃ x : ℕ, x ^ 2 * v.asNat % p = 1) →
      c = 1#u8 ∧ r.asNat ^ 2 * v.asNat % p = 1)
    (h2 : v.asNat % p ≠ 0 → (¬∃ x : ℕ, x ^ 2 * v.asNat % p = 1) →
      c = 0#u8 ∧ r.asNat ^ 2 * v.asNat % p = sqrtM1)
    (hpar : r.asNat % p % 2 = 0) :
    sqrtRatioM1 1 v.toField = (decide (c = 1#u8), r.toField) := by
  have hneg := not_isNeg_toField_of_mod hpar
  by_cases hv : v.asNat % p = 0
  · obtain ⟨rfl, hr⟩ := h0 hv
    rw [toField_eq_zero_iff.mpr hv, toField_eq_zero_iff.mpr hr, sqrtRatioM1_one_zero,
      decide_eq_false (by decide)]
  have hv' := toField_ne_zero_iff.mpr hv
  have hsq : (∃ x : ℕ, x ^ 2 * v.asNat % p = 1) ↔ IsSquare (1 / v.toField) := by
    have h := exists_sq_mul_mod_iff_isSquare_div' (u := 1) hv
    rw [one_mod_p, Nat.cast_one] at h
    rw [toField_def]
    exact h
  by_cases hs : ∃ x : ℕ, x ^ 2 * v.asNat % p = 1
  · obtain ⟨rfl, hr⟩ := h1 hv hs
    have h' := natCast_eq_natCast_of_mod_eq (hr.trans one_mod_p.symm)
    push_cast at h'
    rw [sqrtRatioM1_eq_of_mul_sq_eq hv' (by rw [mul_comm, toField_def, toField_def]; exact h')
      hneg, decide_eq_true rfl]
  · obtain ⟨rfl, hr⟩ := h2 hv hs
    have h' := natCast_eq_natCast_of_mod_eq (hr.trans (Nat.mod_eq_of_lt sqrtM1_lt_p).symm)
    push_cast at h'
    rw [sqrtRatioM1_eq_of_mul_sq_eq_sqrtM1_mul one_ne_zero hv'
      (by rw [mul_comm, toField_def, toField_def, mul_one]; exact h') hneg,
      decide_eq_false (by decide)]

end Curve25519Dalek.backend.serial.u64.field.FieldElement51
