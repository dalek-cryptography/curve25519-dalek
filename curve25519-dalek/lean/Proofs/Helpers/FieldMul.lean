/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong, Oliver Butterley
-/
module
public import Curve25519.Basic
public import Defs.Array
public import Defs.FieldElement51
public import Aeneas.Std.Scalar.Bitwise
public import Aeneas.Std.Scalar.Casts
public import Aeneas.Std.Scalar.Notations
public import Aeneas.Std.Scalar.Ops.Mul
public import Mathlib.Tactic.LinearCombination
import Proofs.Helpers.AsNat
public import Aeneas
public import Mathlib.Tactic.IntervalCases
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Array
import Proofs.Helpers.Bitwise
import Aeneas.Tactic.Conv.Zify
import Aeneas.Tactic.Step.StepStar
public section

/-! # Lemmas for the multiplication and squaring of `FieldElement51`

Shared by `mul` and `square_limbs`: the schoolbook product of two radix-`2^51` numbers with the
part above `2^255` folded back by `19` (`mul_coeffs_mod_p`), and the carry chain that brings the
five 128-bit coefficients back to limbs `< 2^52` (`carryChain`, `carryChain_spec`). -/

open Aeneas Aeneas.Std Aeneas.Std.WP curve25519

namespace Curve25519Dalek.backend.serial.u64.field

open scoped Helpers.MaskStep

/-- Truncating cast from `u128` to `u64`. -/
@[local step]
private theorem cast_u64_spec (x : U128) :
    lift (UScalar.cast .U64 x) ⦃ (y : U64) => y.val = x.val % 2 ^ 64 ⦄ := by
  simp only [lift, WP.spec_ok, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]

/-- Widening cast from `u64` to `u128`. -/
@[local step]
private theorem cast_u128_spec (x : U64) :
    lift (UScalar.cast .U128 x) ⦃ (y : U128) => y.val = x.val ⦄ := by
  simp only [lift, WP.spec_ok, UScalar.cast_val_eq, UScalarTy.U128_numBits_eq]
  scalar_tac

/-- The schoolbook product of two radix-`2^51` numbers, with the part above `2^255` folded back
with weight `19` (as `2^255 ≡ 19 [MOD p]`). -/
theorem mul_coeffs_mod_p {a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 : ℕ}
    (hc0 : c0 = a0 * b0 + 19 * (a4 * b1 + a3 * b2 + a2 * b3 + a1 * b4))
    (hc1 : c1 = a1 * b0 + a0 * b1 + 19 * (a4 * b2 + a3 * b3 + a2 * b4))
    (hc2 : c2 = a2 * b0 + a1 * b1 + a0 * b2 + 19 * (a4 * b3 + a3 * b4))
    (hc3 : c3 = a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3 + 19 * (a4 * b4))
    (hc4 : c4 = a4 * b0 + a3 * b1 + a2 * b2 + a1 * b3 + a0 * b4) :
    (c0 + 2 ^ 51 * c1 + 2 ^ 102 * c2 + 2 ^ 153 * c3 + 2 ^ 204 * c4) % p =
      (a0 + 2 ^ 51 * a1 + 2 ^ 102 * a2 + 2 ^ 153 * a3 + 2 ^ 204 * a4) *
        (b0 + 2 ^ 51 * b1 + 2 ^ 102 * b2 + 2 ^ 153 * b3 + 2 ^ 204 * b4) % p := by
  subst hc0 hc1 hc2 hc3 hc4
  rw [← ZMod.natCast_eq_natCast_iff']
  push_cast
  linear_combination (-(a4 * b1 + a3 * b2 + a2 * b3 + a1 * b4 : ZMod p)
    - 2 ^ 51 * (a4 * b2 + a3 * b3 + a2 * b4) - 2 ^ 102 * (a4 * b3 + a3 * b4)
    - 2 ^ 153 * (a4 * b4)) * two_pow_255_eq_nineteen

/-- One pass of the carry chain: if the coefficients `c_i` are split as
`c_i + q_{i-1} = l_i + 2^51 q_i` and the top carry `q_4` is folded back with weight `19` into
`r_0 + 2^51 r_1`, the represented value is unchanged modulo `p`. -/
private theorem carry_mod_p {c0 c1 c2 c3 c4 l0 l1 l2 l3 l4 q0 q1 q2 q3 q4 r0 r1 : ℕ}
    (h0 : c0 = l0 + 2 ^ 51 * q0) (h1 : c1 + q0 = l1 + 2 ^ 51 * q1)
    (h2 : c2 + q1 = l2 + 2 ^ 51 * q2) (h3 : c3 + q2 = l3 + 2 ^ 51 * q3)
    (h4 : c4 + q3 = l4 + 2 ^ 51 * q4) (hr : r0 + 2 ^ 51 * r1 = l0 + 19 * q4 + 2 ^ 51 * l1) :
    (r0 + 2 ^ 51 * r1 + 2 ^ 102 * l2 + 2 ^ 153 * l3 + 2 ^ 204 * l4) % p =
      (c0 + 2 ^ 51 * c1 + 2 ^ 102 * c2 + 2 ^ 153 * c3 + 2 ^ 204 * c4) % p := by
  rw [← ZMod.natCast_eq_natCast_iff']
  have h255 := two_pow_255_eq_nineteen
  push_cast
  apply_fun ((↑) : ℕ → ZMod p) at h0 h1 h2 h3 h4 hr
  push_cast at h0 h1 h2 h3 h4 hr
  linear_combination hr - h0 - 2 ^ 51 * h1 - 2 ^ 102 * h2 - 2 ^ 153 * h3 - 2 ^ 204 * h4
    - (q4 : ZMod p) * h255

/-- The carry chain of `mul` and `square_limbs` in closed form: the coefficients `c_i` are carried
into 51-bit limbs `r_2, r_3, r_4`, and the final carry is folded back with weight `19` into
`r_0 + 2^51 r_1`. The represented value is unchanged modulo `p`. -/
private theorem carryChain_mod_p (c0 c1 c2 c3 c4 : ℕ) {r0 r1 r2 r3 r4 : ℕ}
    (hr2 : r2 = (c2 + (c1 + c0 / 2 ^ 51) / 2 ^ 51) % 2 ^ 51)
    (hr3 : r3 = (c3 + (c2 + (c1 + c0 / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51)
    (hr4 : r4 = (c4 + (c3 + (c2 + (c1 + c0 / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51)
    (hr : r0 + 2 ^ 51 * r1 = c0 % 2 ^ 51 + 2 ^ 51 * ((c1 + c0 / 2 ^ 51) % 2 ^ 51) +
      19 * ((c4 + (c3 + (c2 + (c1 + c0 / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51)) :
    (r0 + 2 ^ 51 * r1 + 2 ^ 102 * r2 + 2 ^ 153 * r3 + 2 ^ 204 * r4) % p =
      (c0 + 2 ^ 51 * c1 + 2 ^ 102 * c2 + 2 ^ 153 * c3 + 2 ^ 204 * c4) % p := by
  subst hr2 hr3 hr4
  set t1 := c1 + c0 / 2 ^ 51
  set t2 := c2 + t1 / 2 ^ 51
  set t3 := c3 + t2 / 2 ^ 51
  set t4 := c4 + t3 / 2 ^ 51
  exact carry_mod_p (Nat.mod_add_div c0 _).symm (Nat.mod_add_div t1 _).symm
    (Nat.mod_add_div t2 _).symm (Nat.mod_add_div t3 _).symm (Nat.mod_add_div t4 _).symm
    (by rw [hr]; ring)

/-! ## The carry chain

The carry chains of `mul` and `square_limbs` are the same computation, written into a different
initial array and with their own constant `LOW_51_BIT_MASK`. `carryChain` is this computation,
with the mask computation as a parameter; it is assembled from the repeated steps `carryAdd`,
`lowLimb`, `carryOut` and the final `carryFold`. -/

/-- `y + ((x >> 51) as u64) as u128`: propagate the carry of `x` into `y`. -/
@[expose]
def carryAdd (y x : U128) : Result U128 := do
  let i ← x >>> 51#i32
  let i1 ← lift (UScalar.cast .U64 i)
  let i2 ← lift (UScalar.cast .U128 i1)
  y + i2

/-- `(x as u64) & mask`: the low limb of `x`. -/
@[expose]
def lowLimb (mask : U64) (x : U128) : Result U64 := do
  let i ← lift (UScalar.cast .U64 x)
  lift (i &&& mask)

/-- `(x >> 51) as u64`: the carry out of `x`. -/
@[expose]
def carryOut (x : U128) : Result U64 := do
  let i ← x >>> 51#i32
  lift (UScalar.cast .U64 i)

/-- Fold the top carry back into limb 0 with weight `19`, then carry limb 0 into limb 1. -/
@[expose]
def carryFold (mask carry : U64) (a : Array U64 5#usize) :
    Result (Array U64 5#usize) := do
  let i ← carry * 19#u64
  let i1 ← a.index_usize 0#usize
  let i2 ← i1 + i
  let a1 ← a.update 0#usize i2
  let i3 ← a1.index_usize 0#usize
  let i4 ← i3 >>> 51#i32
  let i5 ← a1.index_usize 1#usize
  let i6 ← i5 + i4
  let a2 ← a1.update 1#usize i6
  let i7 ← a2.index_usize 0#usize
  let i8 ← lift (i7 &&& mask)
  a2.update 0#usize i8

/-- The carry chain of `mul` and `square_limbs`: reduce the coefficients `c_i` to limbs, written
into `a`. -/
@[expose]
def carryChain (low_51_bit_mask : Result U64) (a : Array U64 5#usize)
    (c0 c1 c2 c3 c4 : U128) : Result (Array U64 5#usize) := do
  let c1' ← carryAdd c1 c0
  let c0' ← lift (UScalar.cast .U64 c0)
  let mask ← low_51_bit_mask
  let l0 ← lift (c0' &&& mask)
  let a1 ← a.update 0#usize l0
  let c2' ← carryAdd c2 c1'
  let l1 ← lowLimb mask c1'
  let a2 ← a1.update 1#usize l1
  let c3' ← carryAdd c3 c2'
  let l2 ← lowLimb mask c2'
  let a3 ← a2.update 2#usize l2
  let c4' ← carryAdd c4 c3'
  let l3 ← lowLimb mask c3'
  let a4 ← a3.update 3#usize l3
  let carry ← carryOut c4'
  let l4 ← lowLimb mask c4'
  let a5 ← a4.update 4#usize l4
  carryFold mask carry a5

@[local step]
private theorem carry_add_spec (y x : U128) (hy : y.val < 2 ^ 127) (hx : x.val < 2 ^ 115) :
    carryAdd y x ⦃ (r : U128) => r.val = y.val + x.val / 2 ^ 51 ⦄ := by
  unfold carryAdd
  step*

@[local step]
private theorem low_limb_spec (mask : U64) (x : U128) (hmask : mask.val = 2 ^ 51 - 1) :
    lowLimb mask x ⦃ (r : U64) => r.val = x.val % 2 ^ 51 ⦄ := by
  unfold lowLimb
  step*

@[local step]
private theorem carry_out_spec (x : U128) (hx : x.val < 2 ^ 115) :
    carryOut x ⦃ (r : U64) => r.val = x.val / 2 ^ 51 ⦄ := by
  unfold carryOut
  step*

/-- Limb 1 after folding a carry `c` into limb 0 stays below `2^52`. -/
private theorem fold_lt {a0 a1 c : ℕ} (ha0 : a0 < 2 ^ 51) (ha1 : a1 < 2 ^ 51)
    (hc : c < 3 * 2 ^ 58) :
    a1 + (a0 + c * 19) / 2 ^ 51 < 2 ^ 52 := by
  omega

open scoped Helpers.IndexStep Helpers.UpdateStep in
@[local step]
private theorem carry_fold_spec (mask carry : U64) (a : Array U64 5#usize)
    (hmask : mask.val = 2 ^ 51 - 1) (hcarry : carry.val < 3 * 2 ^ 58)
    (ha0 : a[0]!.val < 2 ^ 51) (ha1 : a[1]!.val < 2 ^ 51) :
    carryFold mask carry a ⦃ (r : Array U64 5#usize) =>
      r[0]!.val = (a[0]!.val + carry.val * 19) % 2 ^ 51 ∧
      r[1]!.val = a[1]!.val + (a[0]!.val + carry.val * 19) / 2 ^ 51 ∧
      r[2]! = a[2]! ∧ r[3]! = a[3]! ∧ r[4]! = a[4]! ⦄ := by
  unfold carryFold
  step*

/-- Folding the top carry `q` into limb 0 and carrying limb 0 into limb 1. -/
private theorem fold_eq (x y q : ℕ) :
    (x % 2 ^ 64 % 2 ^ 51 + q * 19) % 2 ^ 51 + 2 ^ 51 * (y % 2 ^ 51 + (x % 2 ^ 64 % 2 ^ 51 + q * 19)
      / 2 ^ 51) = x % 2 ^ 51 + 2 ^ 51 * (y % 2 ^ 51) + 19 * q := by
  rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 51 ∣ 2 ^ 64)]
  omega

/-- The top carry of the carry chain. -/
private theorem carry_lt {c0 c1 c2 c3 c4 : ℕ} (hc0 : c0 < 77 * 2 ^ 108) (hc1 : c1 < 77 * 2 ^ 108)
    (hc2 : c2 < 77 * 2 ^ 108) (hc3 : c3 < 77 * 2 ^ 108) (hc4 : c4 < 5 * 2 ^ 108) :
    (c4 + (c3 + (c2 + (c1 + c0 / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51 < 3 * 2 ^ 58 := by
  omega

/-- The carry chain keeps the value modulo `p` and gives limbs `< 2^52`, provided the
coefficients are small enough for the carries to fit in `u64`. -/
theorem carryChain_spec (low_51_bit_mask : Result U64) (a : Array U64 5#usize)
    (c0 c1 c2 c3 c4 : U128) (hmask : low_51_bit_mask ⦃ (m : U64) => m.val = 2 ^ 51 - 1 ⦄)
    (hc0 : c0.val < 77 * 2 ^ 108) (hc1 : c1.val < 77 * 2 ^ 108) (hc2 : c2.val < 77 * 2 ^ 108)
    (hc3 : c3.val < 77 * 2 ^ 108) (hc4 : c4.val < 5 * 2 ^ 108) :
    carryChain low_51_bit_mask a c0 c1 c2 c3 c4 ⦃ (r : Array U64 5#usize) =>
      Array.asNat 51 r % p =
        (c0.val + 2 ^ 51 * c1.val + 2 ^ 102 * c2.val + 2 ^ 153 * c3.val + 2 ^ 204 * c4.val) % p ∧
      FieldElement51.LimbsLt 52 r ⦄ := by
  unfold carryChain
  step
  step
  step with hmask
  step*
  · simp (disch := simp) only [*, Array.getElem!_Nat_set_ne, Array.getElem!_Nat_set_eq]
    exact Nat.mod_lt _ (by norm_num)
  · simp (disch := simp) only [*, Array.getElem!_Nat_set_ne, Array.getElem!_Nat_set_eq]
    exact Nat.mod_lt _ (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [Array.asNat_five]
    simp (disch := simp) only [*, Array.getElem!_Nat_set_ne, Array.getElem!_Nat_set_eq]
    exact carryChain_mod_p _ _ _ _ _ rfl rfl rfl (fold_eq _ _ _)
  · unfold FieldElement51.LimbsLt
    rw [Nat.forall_lt_five]
    simp (disch := simp) only [*, Array.getElem!_Nat_set_ne, Array.getElem!_Nat_set_eq]
    have hlt : ∀ x : ℕ, x % 2 ^ 51 < 2 ^ 52 := fun x => (Nat.mod_lt _ (by norm_num)).trans
      (by norm_num)
    exact ⟨hlt _, fold_lt (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
      (carry_lt hc0 hc1 hc2 hc3 hc4), hlt _, hlt _, hlt _⟩

end Curve25519Dalek.backend.serial.u64.field
