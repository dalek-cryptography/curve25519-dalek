/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Proofs.Helpers.FieldElement2625
public section

/-!
# Spec theorem for `reduce`

`reduce z` takes an `Array U64 10#usize` and returns a `FieldElement2625`, i.e. ten `u32`
limbs, that represent the same value as `z` modulo `p` in the alternating `2^26/2^25` radix. It runs
a carry chain over the limbs, folds the overflow of limb `9` back into limb `0` scaled by `19`
(using that `2^255 ≡ 19 [MOD p]`), carries once more out of limb `0` and casts the limbs to `u32`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 336:4-390:5
-/


open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

@[step]
theorem reduce.LOW_25_BITS_spec :
    reduce.LOW_25_BITS ⦃ (result : U64) => result.val = 2 ^ 25 - 1 ⦄ := by
  unfold reduce.LOW_25_BITS
  step*


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625



open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

@[step]
theorem reduce.LOW_26_BITS_spec :
    reduce.LOW_26_BITS ⦃ (result : U64) => result.val = 2 ^ 26 - 1 ⦄ := by
  unfold reduce.LOW_26_BITS
  step*


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625



open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP Finset
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625


/-Helper theorem: proves the value preserving property assuming the consequences of a carry step on
the limbs. -/
private theorem carry_preserves_toNat (z z' : Array U64 10#usize) (k : Nat) (hk : k < 9)
    (hmask : z'[k]!.val = z[k]!.val % limbRadix k)
    (hcarry : z'[k + 1]!.val = z[k + 1]!.val + z[k]!.val / limbRadix k)
    (hrest : ∀ j : ℕ, j < 10 → j ≠ k → j ≠ k + 1 → z'[j]!.val = z[j]!.val) :
    Array.asNat2625 z' = Array.asNat2625 z := by
  rw [Array.asNat2625_eq_sum, Array.asNat2625_eq_sum]
  exact sum_eq_sum_add_of_subset (d := 0) (t := {k, k + 1}) (s := range 10)
    (f := fun i => limbWeight i * z'[i]!.val)
    (g := fun i => limbWeight i * z[i]!.val)
    (by simp only [insert_subset_iff, singleton_subset_iff, mem_range]; scalar_tac)
    (by intro j hj1 hj2; rewrite [mem_range] at hj1
        simp only [mem_insert, mem_singleton, not_or] at hj2
        rewrite [Nat.mul_left_cancel_iff (by exact Nat.two_pow_pos _)]
        exact hrest j hj1 hj2.1 hj2.2)
    (by rewrite [sum_pair (by exact Nat.ne_add_one k), sum_pair (by exact Nat.ne_add_one k)]
        rewrite [hmask, hcarry, Nat.left_distrib, Nat.add_comm, limbWeight_succ]
        simp only [Nat.add_zero]
        conv_rhs => rw [← Nat.div_add_mod' (↑z[k]!) (limbRadix k)]
        ring)


@[step]
theorem reduce.carry_spec (z : Array U64 10#usize) (i : Usize)
    (hi : i.val < 9)
    (hover : z[i.val + 1]!.val + z[i.val]!.val / limbRadix i.val < 2 ^ 64) :
    reduce.carry z i ⦃ (z' : Array U64 10#usize) =>
      --Redundant: it follows from the 3 other postconditions as shown above
      Array.asNat2625 z' = Array.asNat2625 z ∧
      --Independent postconditions
      z'[i.val]!.val = z[i.val]!.val % limbRadix i.val ∧
      z'[i.val + 1]!.val = z[i.val + 1]!.val + z[i.val]!.val / limbRadix i.val ∧
      (∀ j : ℕ, j < 10 → j ≠ i.val → j ≠ i.val + 1 → z'[j]!.val = z[j]!.val) ⦄ := by
  unfold reduce.carry
  --Covering the odd and even cases with the same code
  cases Nat.mod_two_eq_zero_or_one i.val
  case inl | inr =>
    step*
    · simp only [*, Nat.shiftRight_eq_div_pow, U64.max_def, U64.numBits_eq]
      simp only [limbRadix, ‹↑i % 2 = _›, Array.getElem!_Nat_eq,
        ← List.Inhabited_getElem_eq_getElem! z.val i.val (by scalar_tac),
        ← List.Inhabited_getElem_eq_getElem! z.val (i.val + 1) (by scalar_tac)] at hover
      exact Nat.le_sub_one_of_lt hover
    --Proving the redundant statement from the independent ones
    · refine (and_iff_right_of_imp (fun h => ?_)).mpr ?_
      · obtain ⟨h1, h2, h3⟩ := h
        exact carry_preserves_toNat z z' i.val hi h1 h2 h3
    --Proving the independent postconditions
      split_conjs
      --Masking
      · simp only [*, Array.getElem!_Nat_set_eq (z.set _ _) i i.val _ (by scalar_tac)]
        simp_lists
        rewrite [UScalar.val_and]
        simp only [limbRadix, *, Nat.and_two_pow_sub_one_eq_mod]
      --Carrying
      · simp only [limbRadix, *,
          Array.getElem!_Nat_set_ne (z.set _ _) i (i.val + 1) _ (by scalar_tac),
          Array.getElem!_Nat_set_eq z _ (i.val + 1) _ (by exact ⟨by assumption, by scalar_tac⟩),
          Array.getElem!_Nat_eq,
          ← List.Inhabited_getElem_eq_getElem! z.val i.val (by scalar_tac),
          ← List.Inhabited_getElem_eq_getElem! z.val (i.val + 1) (by scalar_tac)]
        rw [Nat.shiftRight_eq_div_pow]
      --Invariance of the rest
      · intro j hj hji hji1
        simp only [*]; simp_lists


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625


open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP Finset
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/- `reduce` splits into four phases:
1. interleaved carry chain,
2. `× 19` fold-in,
3. final carry
4. cast packing
-/

set_option linter.hashCommand false in
#decompose reduce reduce_decomp
  letRange 0 10 => reduceCarryChain
  letRange 1 10 => reduceFoldIn
  letRange 3 21 => reduceCasts

/-- Interleaved carry chain of `reduce`: carries limbs `0` to `8` into their successors following
the order (0,4,1,5,2,6,3,7,4,8). -/
add_decl_doc reduceCarryChain

/-- `× 19` fold-in of `reduce`: adds `19` times the carry out of limb `9` to limb `0`. -/
add_decl_doc reduceFoldIn

/-- Cast packing of `reduce`: casts the ten `u64` limbs to `u32` into a `FieldElement2625`. -/
add_decl_doc reduceCasts


/-Helper theorem that keeps track of the bounds that hold for the limbs of an array after a carry.-/
private theorem carry_bounds {s1 s2 : Finset Nat} (z z' : Array U64 10#usize) (i : Nat)
  (hsub1 : s1 ⊆ range 10) (hsub2 : s2 ⊆ range 10)
  --`s1` is the set of indices that underwent masking and haven't been touched since
  (hs1 : ∀ j, j ∈ s1 → z[j]!.val < limbRadix j)
  --`s2` is the set of indices for which the initial bound holds, i.e. they can receive a carry
  (hs2 : ∀ j, j ∈ s2 → z[j]!.val ≤ 2 ^ 64 - 2 ^ 39)
  --Postconditions from reduce.carry
  (hmask : z'[i]!.val = z[i]!.val % limbRadix i)
--  (hcarry : z'[i + 1]!.val = z[i + 1]!.val + z[i]!.val / limbRadix i)
  (hrest : ∀ j : ℕ, j < 10 → j ≠ i → j ≠ i + 1 → z'[j]!.val = z[j]!.val)
  --Bound on the index
  (hi : i < 10) :
  --After a carry at `i` the masking bound holds for limb `i`, but we cannot guarantee it for `i+1`
    (∀ j, j ∈ s1 \ {i + 1} ∪ {i} → z'[j]!.val < limbRadix j) ∧
  --After a carry at `i` the initial bound holds for limb `i`, but we cannot guarantee it for `i+1`
    (∀ j, j ∈ s2 \ {i + 1} ∪ {i} → z'[j]!.val ≤ 2 ^ 64 - 2 ^ 39) ∧
  --After a carry at `i` we cannot guarantee that `i+1` can be carried without overflow
    (∀ j, j + 1 ∈ s2 \ {i} → z'[j + 1]!.val + z'[j]!.val / limbRadix j < 2 ^ 64) ∧
    (s1 \ {i + 1} ∪ {i} ⊆ range 10) ∧
    (s2 \ {i + 1} ∪ {i} ⊆ range 10) := by
  split_conjs
  · intro j hj
    by_cases hij : j = i
    · rewrite [hij, hmask]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · rewrite [hrest j (by rewrite [← mem_range]; grind) hij (by grind)]; exact hs1 j (by grind)
  · intro j hj
    by_cases hij : j = i
    · rewrite [hij, hmask]
      exact Nat.le_of_lt (
        Nat.lt_of_lt_of_le
          (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.le_trans (m := 2 ^ 26)
            (by rewrite [limbRadix, Nat.pow_le_pow_iff_right (by decide)]; exact Nat.sub_le _ _ )
            (by decide)))
    · rewrite [hrest j (by rewrite [← mem_range]; grind) hij (by grind)]; exact hs2 j (by grind)
  · intro j hj
    by_cases hij : j = i
    · rewrite [hij, hmask]
      rewrite [limbRadix, Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))]
      agrind
    · have h1 := hs2 (j + 1) (by rewrite [mem_sdiff] at hj; exact hj.1)
      rewrite [hrest (j + 1) (by grind) (by grind) (by rw [Nat.add_one_ne_add_one_iff]; exact hij)]
      calc
        _ ≤ 2 ^ 64 - 2 ^ 39 + (2 ^ 64 - 1) / limbRadix j :=
          Nat.add_le_add h1 (Nat.div_le_div_right (by scalar_tac))
        _ ≤ 2 ^ 64 - 2 ^ 39 + (2 ^ 64 - 1) / 2 ^ 25 :=
          Nat.add_le_add_left (Nat.div_le_div_left
            (Nat.pow_le_pow_right (by decide) (by scalar_tac)) (Nat.two_pow_pos _)) _
        _ < 2 ^ 64 := by decide
  · grind
  · grind


/-- Spec theorem for the interleaved carry chain that shrinks limbs 0 to 8 below the radix, except
for a bit of a leeway for limb 5, while keeping the represented value unchanged. The proof works by
propagating the available bounds one monadic step at a time, using `carry_bounds`. -/
@[local step]
private theorem reduceCarryChain_spec (z : Array U64 10#usize)
    (hz : ∀ i : ℕ, i < 10 → z[i]!.val ≤ 2 ^ 64 - 2 ^ 39) :
    reduceCarryChain z ⦃ (z10 : Array U64 10#usize) =>
      --The first bound is redundant, but helps step* discharging goals later
      (∀ j : ℕ, j < 9 → z10[j]!.val < 2 ^ 26) ∧
      (∀ j : ℕ, j < 9 → j ≠ 5 → z10[j]!.val < limbRadix j) ∧
      z10[5]!.val < limbRadix 5 + 2 ^ 14 ∧
      z10.asNat2625 = z.asNat2625 ⦄ := by
  unfold reduceCarryChain
  step
  --Initializing the helper `carry_bounds`
  have hz' := hz
  conv at hz' in _ < 10 => rewrite [← mem_range]
  have hb := carry_bounds (s1 := ∅) z ‹_› _ (empty_subset _)
    (by decide) (by grind) hz' ‹_› ‹_› (by decide)
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  step
  --Proving the preconditions for the next 5 carries
  iterate 5
    have hb := carry_bounds _ ‹_› _ hb4 hb5 hb1 hb2 ‹_› ‹_› (by decide)
    clear hb1 hb2 hb3 hb4 hb5
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
    step
    · exact hb3 _ (by decide)
  --Need to break the iteration to introduce a hypothesis for later use
  have hz6 := hb1 4 (by decide)
  --Proceeding with the iteration, proving the preconditions for 2 more carries
  iterate 2
    have hb := carry_bounds _ ‹_› _ hb4 hb5 hb1 hb2 ‹_› ‹_› (by decide)
    clear hb1 hb2 hb3 hb4 hb5
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
    step
    · exact hb3 _ (by decide)
  --Need to break the iteration to introduce a hypothesis for later use
  have hz8 := hb1 5 (by decide)
  --Proving the precondition for the last carry
  have hb := carry_bounds _ ‹_› _ hb4 hb5 hb1 hb2 ‹_› ‹_› (by decide)
  clear hb1 hb2 hb3 hb4 hb5
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  step
  · exact hb3 _ (by decide)
  --Final propagation of bounds
  have hb := carry_bounds _ ‹_› _ hb4 hb5 hb1 hb2 ‹_› ‹_› (by decide)
  clear hb1 hb2 hb3 hb4 hb5
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  --Proving the postconditions
  refine (and_iff_right_of_imp (fun h => ?_)).mpr ?_
  · obtain ⟨h1, h2, _⟩ := h
    intro j hj
    by_cases hj5 : j = 5
    · rewrite [hj5]; exact Nat.lt_of_lt_of_le h2 (by decide)
    · exact Nat.lt_of_lt_of_le (h1 j hj hj5)
        (by rewrite [limbRadix, Nat.pow_le_pow_iff_right (by decide)]; exact Nat.sub_le _ _)
  split_conjs
  · intro j hj1 hj2
    have hj : j ∈ range 9 \ {5} := by
      rewrite [mem_sdiff, mem_range, mem_singleton]; exact ⟨hj1, hj2⟩
    exact hb1 j (by apply mem_of_subset (by decide) hj)
  · /- result[5] = z9[5] = z8[5] + z8[4] / 2^26 =
    = z8[5] + (z6[4] + z6[3] / 2 ^ 25) / 2 ^ 26 <
    2 ^ 25 + (2 ^ 26 + (2 ^ 64 - 2 ^ 39) / 2 ^ 25) / 2 ^ 26 < 2 ^ 25 + 2 ^ 14
    This is where the two hypotheses breaking the iterations are used.-/
    have hz10 := ‹∀ j : ℕ, j < 10 → _ → _ → _ = _›
    rewrite [hz10 5 (by decide) (by decide) (by decide) ]; simp only [*]
    have hz7 := ‹∀ j : ℕ, j < 10 → j ≠ 7 → j ≠ 8 → _ = _›
    rewrite [hz7 4 (by decide) (by decide) (by decide) ]; simp only [*]
    agrind
  · simp only [*]


/-- Spec theorem for folding in the carry of the last limb. Anything that exceeds the radix `2^25`
in limb 9 is a multiple of `2^255` in the Nat representation and hence can be interpreted as a
multiple of `19` by the identity `2^255 ≡ 19 [MOD p]`. Therefore the fold in preserves the Nat value
modulo `p` only. -/
@[local step]
private theorem reduceFoldIn_spec (z10 : Array U64 10#usize)
    (hof : z10[0]!.val + 19 * (z10[9]!.val / limbRadix 9) < 2 ^ 64) :
    reduceFoldIn z10 ⦃ (z12 : Array U64 10#usize) =>
      --The first equation is redundant but it is the main statement used later
      z12.asNat2625 % p = z10.asNat2625 % p ∧
      z12[0]!.val = z10[0]!.val + 19 * (z10[9]!.val / limbRadix 9) ∧
      z12[9]!.val = z10[9]!.val % limbRadix 9 ∧
      (∀ j : ℕ, 0 < j → j < 9 → z12[j]!.val = z10[j]!.val) ⦄ := by
  unfold reduceFoldIn
  step*
  --Proving that there is no overflow
  · simp only [*, Nat.shiftRight_eq_div_pow]
    simp_lists at hof
    scalar_tac
  --Proving the redundant, value preserving modulo p statement
  refine (and_iff_right_of_imp (fun h => ?_)).mpr ?_
  · obtain ⟨h1, h2, h3⟩ := h
    rw [Array.asNat2625_eq_sum, Array.asNat2625_eq_sum]
    rewrite [← sum_sdiff (s₁ := {0, 9})
    (f := fun j => limbWeight j * z10[j]!.val)
    (by simp only [insert_subset_iff, singleton_subset_iff, mem_range]; agrind),
    ← sum_sdiff (s₁ := {0, 9})
    (f := fun j => limbWeight j * z12[j]!.val)
    (by simp only [insert_subset_iff, singleton_subset_iff, mem_range]; agrind)]
    rewrite [sum_congr rfl (fun x hx => by rw [h3 x (by grind) (by grind)])]
    apply Nat.add_mod_eq_add_mod_left
    rewrite [sum_pair (by decide), sum_pair (by decide)]
    rewrite [h1, h2]
    agrind [p_add_nineteen]
  --Proving the independent postconditions
  split_conjs
  · simp only [*, limbRadix]; simp_lists; simp only [*, Nat.shiftRight_eq_div_pow]
  · simp only [*, limbRadix]; simp_lists
    conv => lhs; simp only [‹(_ : Nat) = _ &&& _›, UScalar.val_and]
    conv => lhs; arg 2; simp only [*]
    rewrite [Nat.and_two_pow_sub_one_eq_mod _ _]
    simp only [*]; simp_lists
  · intro j hj1 hj2
    simp only [*]; simp_lists


/-- Spec theorem for the casting part. Once every limb is reduced below `2^32` they can be
represented as `U32`s without changing their values. This in particular keeps the represented Nat
value the same as well. -/
@[local step]
private theorem reduceCasts_spec (z13 : Array U64 10#usize)
    (hbounds : ∀ i : ℕ, i < 10 → z13[i]!.val < 2 ^ 32) :
    reduceCasts z13 ⦃ (result : FieldElement2625) =>
      --This equality follows from the next one by a general congruence theorem
      result.asNat = z13.asNat2625 ∧
      (∀ j : ℕ, j < 10 → result[j]!.val = z13[j]!.val) ⦄ := by
  unfold reduceCasts
  step*
  refine (and_iff_right_of_imp (fun h => ?_)).mpr ?_
  · rw [asNat_def, Array.asNat2625_congr _ _ h]
  · intro j hj
    simp only [Array.make, Array.getElem!_Nat_eq, *]
    rewrite [← mem_range] at hj
    fin_cases hj
    · simpa using hbounds 0 (by decide)
    · simpa using hbounds 1 (by decide)
    · simpa using hbounds 2 (by decide)
    · simpa using hbounds 3 (by decide)
    · simpa using hbounds 4 (by decide)
    · simpa using hbounds 5 (by decide)
    · simpa using hbounds 6 (by decide)
    · simpa using hbounds 7 (by decide)
    · simpa using hbounds 8 (by decide)
    · simpa using hbounds 9 (by decide)


@[step]
theorem reduce_spec (z : Array U64 10#usize)
    (hz : ∀ i : ℕ, i < 10 → z[i]!.val ≤ 2 ^ 64 - 2 ^ 39) :
    reduce z ⦃ (r : FieldElement2625) =>
      r.asNat % p = z.asNat2625 % p ∧ r.LimbsLt 26 ∧
      ∀ i : ℕ, i < 10 → r[i]!.val < limbRadix i + i % 2 * 2 ^ 18 ⦄ := by
  rewrite [reduce_decomp]
  --Aeneas has a setting of genLocal = 2 for step. Adding 1 to it here helps discharging a goal.
  step* (genLocal := 3)
  split_conjs
  --Proving the value preservation modulo p
  · simp only [*]
  --Proving the simple, constant bound on the limbs
  · agrind
  --Proving the tighter bound on the limbs
  · intro j hj
    rewrite [← mem_range] at hj
    fin_cases hj
    iterate 10
      agrind


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625
