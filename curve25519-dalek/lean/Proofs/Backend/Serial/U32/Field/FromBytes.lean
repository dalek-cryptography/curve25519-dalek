/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Defs.Array
import Proofs.Helpers.FieldElement2625
import Proofs.Helpers.AsNat
import Proofs.Backend.Serial.U32.Field.Reduce
public section

/-!
# Spec theorem for `from_bytes`

`from_bytes data` decodes 32 little-endian bytes into a `FieldElement2625`. Each of the ten limbs is
read from three or four consecutive bytes and shifted left by the gap between that byte's bit
position and the limb's weight in the alternating `2^26/2^25` radix, so that the limbs tile bits 0
to 254. The top limb is masked to 23 bits, discarding bit 255, and `reduce` then carries the ten
oversized limbs back into range. The value represented is therefore the input modulo `2 ^ 255`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 404:4-432:5
-/


open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

@[step]
theorem from_bytes.LOW_23_BITS_spec :
    from_bytes.LOW_23_BITS ⦃ (result : U64) => result.val = 2 ^ 23 - 1 ⦄ := by
  unfold from_bytes.LOW_23_BITS
  step*


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625



open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP Finset
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

@[step]
theorem from_bytes.load3_at_spec (b : Slice U8) (i : Usize)
    (hi : i.val + 3 ≤ b.length) :
    from_bytes.load3_at b i ⦃ (r : U64) =>
      r.val = b[i.val]!.val + 2 ^ 8 * b[i.val + 1]!.val + 2 ^ 16 * b[i.val + 2]!.val ∧
      /- Redundant: it follows from the other conjunct. -/
      r.val < 2 ^ 24 ⦄ := by
  unfold from_bytes.load3_at
  step*
  refine (and_iff_left_of_imp (fun h => ?_)).mpr ?_
  --Showing that the first statement implies the second
  · rw [h]; scalar_tac
  --Proving the first statement
  · rewrite [UScalar.val_or]
    conv in _ ||| _ => simp only [*]
    rewrite [UScalar.val_or]
    simp (disch := scalar_tac) only [*, U8.cast_U64_val_eq, Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    nth_rewrite 2 3 [Nat.or_mul_two_pow_eq_add_of_lt (by scalar_tac)]
    rewrite [Nat.or_mul_two_pow_eq_add_of_lt (by scalar_tac)]
    simp (disch := scalar_tac) only [Slice.getElem!_Nat_eq, getElem!_pos]
    ring


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625



open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP Finset
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

@[step]
theorem from_bytes.load4_at_spec (b : Slice U8) (i : Usize)
    (hi : i.val + 4 ≤ b.length) :
    from_bytes.load4_at b i ⦃ (r : U64) =>
      r.val = b[i.val]!.val + 2 ^ 8 * b[i.val + 1]!.val +
      2 ^ 16 * b[i.val + 2]!.val + 2 ^ 24 * b[i.val + 3]!.val ∧
      /- Redundant: it follows from the other conjunct. -/
      r.val < 2 ^ 32 ⦄ := by
  unfold from_bytes.load4_at
  step*
  refine (and_iff_left_of_imp (fun h => ?_)).mpr ?_
  --Showing that the first statement implies the second
  · rw [h]; scalar_tac
  --Proving the first statement
  · iterate 2
      rewrite [UScalar.val_or]
      conv in _ ||| _ => simp only [*]
    rewrite [UScalar.val_or]
    simp (disch := scalar_tac) only [*, U8.cast_U64_val_eq, Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    nth_rewrite 3 4 [Nat.or_mul_two_pow_eq_add_of_lt (by scalar_tac)]
    nth_rewrite 2 3 [Nat.or_mul_two_pow_eq_add_of_lt (by scalar_tac)]
    rewrite [Nat.or_mul_two_pow_eq_add_of_lt (by scalar_tac)]
    simp (disch := scalar_tac) only [Slice.getElem!_Nat_eq, getElem!_pos]
    ring


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625


open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP Finset
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625


/-- If all 10 elements of a 10-long array are bounded by `2 ^ 32` and we update an element by a
value `x` of the form `x = y <<< m % U64.size`, where `y < 2 ^ n` and `n + m ≤ 32`, then each term
of the resulting array is still bounded by 2 ^ 32. -/
private theorem set_bound {a a' : Array U64 10#usize} {x y : U64} {k : Usize} {n m : Nat}
    (heq : (a' = a.set k x)) (ha : ∀ j : ℕ, j < 10 → a[j]!.val < 2 ^ 32)
    (hx : x.val = y.val <<< m % U64.size) (hy : y.val < 2 ^ n) (hexp : n + m ≤ 32) :
    ∀ j : ℕ, j < 10 → a'[j]!.val < 2 ^ 32 := by
  intro j hj; subst a'; by_cases j = k.val
  --The non-trivial case when a'[j] is a[j] replaced by x:
  · simp_lists
    rewrite [hx, Nat.shiftLeft_eq]
    have hmul := Nat.mul_lt_mul_of_pos_right (k := 2 ^ m) hy (by exact Nat.two_pow_pos m)
    rewrite [← Nat.pow_add] at hmul
    rewrite [U64.size_def, U64.numBits_eq, Nat.mod_eq_of_lt (by
    --Closing the intermediate goal coming from rewriting the mod:
      exact Nat.lt_of_lt_of_le (k := 2 ^ 64) hmul (by
        exact Nat.pow_le_pow_of_le (by decide) (by exact Nat.le_trans (k := 64) hexp (by decide))
        )
      )]
    exact Nat.lt_of_lt_of_le (k := 2 ^ 32) hmul (by exact Nat.pow_le_pow_of_le (by decide) hexp )
  --The simple case when a'[j] = a[j]:
  · have h := ha j hj; simp_lists at h ⊢; exact h


/-- If all 10 elements of a 10-long array are bounded by `2 ^ 32` and we update an element by a
value `x`, where `x < 2 ^ 32`, then each term of the resulting array is still bounded by 2 ^ 32. -/
private theorem set_bound' {a a' : Array U64 10#usize} {x : U64} {k : Usize}
    (heq : (a' = a.set k x)) (ha : ∀ j : ℕ, j < 10 → a[j]!.val < 2 ^ 32)
    (hx : x.val < 2 ^ 32) :
    ∀ j : ℕ, j < 10 → a'[j]!.val < 2 ^ 32 := by
  --This can be viewed as a special case of set_bound
  have h : x.val = x.val <<< 0 % U64.size := by scalar_tac
  exact set_bound heq ha h hx (by decide)


/-- If we update a limb from `0` to `x` in an `Array U64 10#usize` representation of a
`FieldElement2625`, then the Nat value of the element increases by `x` times the limb's weight. -/
private theorem set_zero_to_x {a a' : Array U64 10#usize} {k : Usize} {x : U64} {n : Nat}
    (heq : (a' = a.set k x)) (hindex : k.val < 10) (hzero : a[k.val]!.val = 0)
    (hold_sum : a.asNat2625 = n) :
    a'.asNat2625 = n + limbWeight k.val * (↑x) := by
  rewrite [heq, ← hold_sum, Array.asNat2625_eq_sum, Array.asNat2625_eq_sum]
  exact sum_eq_sum_add_of_subset
    (d := limbWeight k.val * x.val) (t := {k.val})
    (by simp only [singleton_subset_iff, mem_range]; exact hindex)
    (by intro j hj1 hj2; rewrite [mem_singleton, ← ne_eq] at hj2
        rw [Array.getElem!_Nat_set_ne]; exact hj2.symm)
    (by simp only [sum_singleton, hzero, Nat.mul_zero]
        rw [Array.getElem!_Nat_set_eq _ _ _ _ (by agrind), Nat.zero_add])


/-- If we shift `n` by `k` digits to the left, where `n < 2 ^ m` and `m + k < 64`, then the bitshift
modulo `U64.size` is just multiplication by `2 ^ k`. -/
private theorem shiftLeft_mod_size_eq_of_lt {n m k : Nat}
    (hn : n < 2 ^ m) (hexp : m + k < 64) :
    n <<< k % U64.size = 2 ^ k * n := by
  rw [Nat.mul_comm, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by
    rewrite [U64.size_def, U64.numBits_eq]
    exact Nat.lt_trans (k := 2 ^ 64)
      (Nat.mul_lt_mul_of_pos_right (k := 2 ^ _) ‹_› (by exact Nat.two_pow_pos _))
      (by rewrite [← Nat.pow_add]; exact Nat.pow_lt_pow_right (by decide) hexp))]


@[step]
theorem from_bytes_spec (data : Array U8 32#usize) :
    from_bytes data ⦃ (r : FieldElement2625) =>
      r.asNat % p = data.asNat 8 % 2 ^ 255 % p ∧ r.LimbsLt 26 ⦄ := by
  unfold from_bytes
  have hlen : data.to_slice.length = 32 := by simp
  --Initializing
  have hinit_bound : ∀ j : ℕ, j < 10 → (Array.repeat 10#usize 0#u64)[j]!.val < 2^32 := by
    simp_lists [Array.repeat_val]; decide
  have hinit_toNat : Array.asNat2625 (Array.repeat 10#usize 0#u64) = 0 := by
    rw [Array.asNat2625_expand]
    simp [Array.getElem!_Nat_eq, Array.repeat_val]
  step* 3
  --Propagating
  have h_bound := set_bound' ‹_› hinit_bound ‹_›
  have h_toNat := set_zero_to_x ‹_› (by decide) (by simp) hinit_toNat
  --Clean-up:
  clear hinit_bound hinit_toNat
  --Rename to be able to propagate:
  rename' h_bound => hinit_bound, h_toNat => hinit_toNat
  iterate 4
    step* 4
    have h_bound := set_bound ‹_› hinit_bound ‹_› ‹_› (by decide)
    have h_toNat := set_zero_to_x ‹_› (by decide) (by simp [*]) hinit_toNat
    have hmod_kill := ‹_ = _ <<< _ % U64.size›
    rewrite [hmod_kill, shiftLeft_mod_size_eq_of_lt ‹_› (by decide)] at h_toNat
    --Clean-up:
    clear hinit_bound hinit_toNat hmod_kill
    --Rename to be able to propagate:
    rename' h_bound => hinit_bound, h_toNat => hinit_toNat
  step* 3
  have h_bound := set_bound' ‹_› hinit_bound ‹_›
  have h_toNat := set_zero_to_x ‹_› (by decide) (by simp [*]) hinit_toNat
  --Clean-up:
  clear hinit_bound hinit_toNat
  --Rename to be able to propagate:
  rename' h_bound => hinit_bound, h_toNat => hinit_toNat
  iterate 3
    step* 4
    have h_bound := set_bound ‹_› hinit_bound ‹_› ‹_› (by decide)
    have h_toNat := set_zero_to_x ‹_› (by decide) (by simp [*]) hinit_toNat
    have hmod_kill := ‹_ = _ <<< _ % U64.size›
    rewrite [hmod_kill, shiftLeft_mod_size_eq_of_lt ‹_› (by decide)] at h_toNat
    --Clean-up:
    clear hinit_bound hinit_toNat hmod_kill
    --Rename to be able to propagate:
    rename' h_bound => hinit_bound, h_toNat => hinit_toNat
  step* 6
  --Propagating the uniform bound and accumulated value one last time
  --Top limb needs proof of a mask bound
  have h_bound := set_bound (n := 23) ‹_› hinit_bound ‹_›
    (by conv => lhs; simp only [*]; rewrite [UScalar.val_and]
        conv => lhs; arg 2; simp only [*]
        rewrite [Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by decide)) (by decide)
  have h_toNat := set_zero_to_x ‹_› (by decide) (by simp [*]) hinit_toNat
  have hmod_kill := ‹_ = _ <<< _ % U64.size›
  rewrite [hmod_kill, shiftLeft_mod_size_eq_of_lt
    (by conv => lhs; simp only [*]; rewrite [UScalar.val_and]
        conv => lhs; arg 2; simp only [*]
        rewrite [Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by decide)) (by decide)] at h_toNat
  step
  --Discharging the precondition of `reduce`
  · intro i hi
    exact Nat.le_trans (Nat.le_of_lt (h_bound i hi)) (by decide)
  --The limb bound comes straight from `reduce_spec`; the value is the main goal
  · refine ⟨?_, by assumption⟩
    conv => lhs; simp only [‹_ = _ % p ›, h_toNat]
    simp only [limbWeight, ← Nat.mul_assoc, ← Nat.pow_add]
    simp only [UScalar.ofNatCore_val_eq, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul]
    have htop := ‹(_ : Nat) = (_ &&& _)›
    conv at htop => arg 2; simp only [UScalar.bv_toNat, *]; rewrite [Nat.and_two_pow_sub_one_eq_mod]
    rewrite [htop, ← Nat.mul_mod_mul_left]
    rewrite [← Nat.add_mul_mod_mul_left_of_lt (by scalar_tac)]
    rw [Array.asNat_eq_sum]
    simp only [*, Nat.left_distrib, ← Nat.mul_assoc, ← Nat.pow_add, Nat.reduceAdd, ← Nat.add_assoc]
    simp only [Slice.getElem!_Nat_eq, Array.val_to_slice]
    simp only [Array.getElem!_Nat_eq]
    simp only [UScalar.ofNatCore_val_eq, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.zero_add, Nat.reduceMul, Nat.mul_zero, pow_zero, Nat.one_mul]


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625
