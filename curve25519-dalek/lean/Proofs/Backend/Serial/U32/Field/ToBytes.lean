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
# Spec theorem for `to_bytes`
`to_bytes` encodes a field element as the 32 little-endian bytes of its canonical representative
modulo `p = 2^255 - 19`. It reduces the limbs, computes `q = ⌊h / p⌋ ∈ {0, 1}` as the carry out of
`h + 19`, subtracts `q * p` by adding `19 * q` and dropping bit 255 while propagating the carries,
and finally packs the ten 26/25-bit limbs into bytes. `to_bytes_spec` states that the bytes, read as
a little-endian number, equal the value of the input modulo `p`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 437:4-548:5
-/


open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

@[step]
theorem to_bytes.LOW_25_BITS_spec :
    to_bytes.LOW_25_BITS ⦃ (result : U32) => result.val = 2 ^ 25 - 1 ⦄ := by
  unfold to_bytes.LOW_25_BITS
  step*


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625



open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

@[step]
theorem to_bytes.LOW_26_BITS_spec :
    to_bytes.LOW_26_BITS ⦃ (result : U32) => result.val = 2 ^ 26 - 1 ⦄ := by
  unfold to_bytes.LOW_26_BITS
  step*


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625


open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP Finset
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/- `to_bytes` can be split into three phases:
- casting then reducing limbs and determining if the result is over p or not,
- calculating the canonical value,
- turning the result into an Array U8 32#usize representation.
-/

set_option linter.hashCommand false in
#decompose to_bytes to_bytes_decomp
  letRange 0 21 => initReduce
  letRange 1 31 => isOverP
  letRange 2 82 => calcCanonical
  letRange 3 127 => toArray

/-- First phase of `to_bytes`: casts the limbs to `u64` and reduces them with `reduce`. -/
add_decl_doc initReduce

/-- Second phase of `to_bytes`: computes the lowest limb and `q = ⌊h / p⌋` as the carry out of the
top limb of `h + 19`. -/
add_decl_doc isOverP

/-- Third phase of `to_bytes`: adds `19 * q` to the lowest limb and propagates the carries, masking
each limb to its radix and dropping the carry out of the top limb, i.e. subtracts `q * p`. -/
add_decl_doc calcCanonical

/-- Fourth phase of `to_bytes`: packs the ten limbs into 32 little-endian bytes and asserts that the
top bit of the last byte is clear. -/
add_decl_doc toArray

set_option linter.hashCommand false in
#decompose calcCanonical calcCanonical_decomp
  letRange 3 42 => roundsLow
  letRange 4 32 => roundsHigh

/-- Carry rounds 0 to 4 of `calcCanonical`, with the two mask constants. -/
add_decl_doc roundsLow

/-- Carry rounds 5 to 8 of `calcCanonical`. -/
add_decl_doc roundsHigh

set_option linter.hashCommand false in
#decompose toArray toArray_decomp
  letRange 1 61 => packLow
  letRange 2 61 => packHigh

/-- Bytes 0 to 15 of `toArray` (limbs 0 to 4). -/
add_decl_doc packLow

/-- Bytes 16 to 31 of `toArray` (limbs 5 to 9). -/
add_decl_doc packHigh




/-- First phase: the reduced limbs represent the same value modulo `p`, the even limbs are below
`2^26` and the odd limbs below `2^25 + 2^18`. -/
@[local step]
private theorem initReduce_spec (self : FieldElement2625) :
    initReduce self ⦃ (fe : FieldElement2625) =>
      self.asNat % p = fe.asNat % p ∧
      (∀ i : ℕ, i < 10 → fe[i]!.val < limbRadix i + i % 2 * 2 ^ 18) ∧
      (∀ i : ℕ, i < 10 → fe[i]!.val < 2 ^ 26) ⦄ := by
  unfold initReduce
  step* 21
  · refine getElem!_make_le _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      scalar_tac
  split_conjs
  · simp only [*]
    rw [asNat_def]
    congr 1
    apply Array.asNat2625_congr
    intro j hj
    rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
    all_goals first | omega | simp [Array.getElem!_Nat_eq]
  · assumption
  · assumption


/-- One step of a carry chain over the limbs of `z`, with an extra summand `m` added into limb 0. If
the first `n` limbs plus `m` split into a remainder below the weight of limb `n` and a carry `q`
times that weight, then with `q1 = z[n] + q` and the new carry `q' = q1 >>> (26 - n % 2)` the same
split holds one limb further. The second conjunct gives the new remainder as the old one plus the
masked limb `q1 % limbRadix n` at its weight. -/
private theorem carry_remainder {n m q q1 q' : Nat} {x : U32} (z : FieldElement2625)
    {hn : n < (↑z : List U32).length}
    (heq : (∑ i ∈ range n, limbWeight i * (z[i]!).val) + m =
      ((∑ i ∈ range n, limbWeight i * (z[i]!).val) + m) % limbWeight n + q * limbWeight n)
    (hq : q' = q1 >>> (26 - n % 2)) (hadd : q1 = x.val + q) (hlimb : x = (↑z : List U32)[n]) :
      --Equation describing the propagation of the remainder in an addition
      (∑ i ∈ range (n + 1), limbWeight i * (z[i]!).val) + m =
        ((∑ i ∈ range (n + 1), limbWeight i * (z[i]!).val) + m) % limbWeight (n + 1) +
        q' * limbWeight (n + 1) ∧
      --Redundant equation describing the propagation of partial results of an addition
      ((∑ i ∈ range (n + 1), limbWeight i * (z[i]!).val) + m) % limbWeight (n + 1) =
        ((∑ i ∈ range n, limbWeight i * (z[i]!).val) + m) % limbWeight n +
        (q1 % limbRadix n) * limbWeight n := by
  refine (and_iff_left_of_imp (fun hcarry => ?_)).mpr ?_
  --The mask identity
  · apply Nat.add_right_cancel (m := q' * limbWeight (n + 1))
    rewrite [← hcarry]
    conv_lhs => rewrite [sum_range_succ, Nat.add_right_comm, heq]
    rw [hq, hadd, hlimb, List.Inhabited_getElem_eq_getElem! _ _ hn, ← Array.getElem!_Nat_eq,
      Nat.shiftRight_eq_div_pow, ← limbRadix, limbWeight_succ, Nat.add_assoc, Nat.add_assoc,
      Nat.add_left_cancel_iff, ← Nat.mul_assoc, ← Nat.right_distrib, Nat.mod_add_div',
      Nat.right_distrib, Nat.add_comm, Nat.mul_comm]
  --The carry identity
  · nth_rewrite 2 [limbWeight_succ]
    rewrite [hq, hadd, hlimb, List.Inhabited_getElem_eq_getElem! _ _ hn, ← Array.getElem!_Nat_eq,
      Nat.shiftRight_eq_div_pow, ← limbRadix, ← Nat.mul_assoc,
      Nat.div_mul_self_eq_mod_sub_self, Nat.sub_mul, sum_range_succ, Nat.add_assoc, Nat.add_comm,
      ← Nat.add_sub_assoc (by apply Nat.mul_le_mul_right; exact Nat.mod_le _ _)]
    apply Nat.eq_sub_of_add_eq
    conv_rhs => rewrite [Nat.add_comm, Nat.right_distrib, Nat.mul_comm]
    simp only [Nat.add_assoc, Nat.add_left_cancel_iff]
    conv_lhs => rewrite [← Nat.add_assoc, Nat.add_comm]
    nth_rewrite 3 4 [Nat.add_comm]
    conv_rhs => rewrite [Nat.add_comm]
    rewrite [heq, ← Nat.add_assoc, Nat.add_right_cancel_iff, ← Nat.add_assoc]
    conv_rhs => rewrite [Nat.add_comm, ← Nat.add_assoc, Nat.mul_comm, ← Nat.left_distrib,
      Nat.mul_comm, Nat.add_mod, limbWeight_succ, Nat.mul_mod_mul_right, Nat.mod_mod_of_dvd' (by
      exact Nat.dvd_mul_left _ _)]
    nth_rewrite 2 [Nat.add_comm]
    rewrite [eq_comm]
    rw [Nat.mod_eq_of_lt
      (by exact Nat.lt_mod_mul_add_mod
            (by unfold limbRadix; exact Nat.two_pow_pos _)
            (by unfold limbWeight; exact Nat.two_pow_pos _))]


/-- Second phase: `i20` is the lowest limb and `q9 = ⌊fe / p⌋`, which is at most 1 given the limb
bounds left by the first phase. -/
@[local step]
private theorem isOverP_spec (fe : FieldElement2625)
    (hfe : ∀ i : ℕ, i < 10 → fe[i]!.val < limbRadix i + i % 2 * 2 ^ 18) :
    isOverP fe ⦃ (i20 : U32) (q9 : UScalar UScalarTy.U32) =>
      i20 = fe[0]! ∧
      q9.val = fe.asNat / p ∧
      q9.val ≤ 1 ⦄ := by
  unfold isOverP
  step* 2
  · subst ‹_›
    rewrite [Array.getElem_val_eq_getElem!]
    apply Nat.le_trans (by apply Nat.le_of_lt; exact Nat.add_lt_add_right (hfe _ (by decide)) _)
      (by rewrite [U32.max_def, U32.numBits_eq]; decide)
  step
  have hq_carry_old : (∑ i ∈ range 0, limbWeight i * (fe[i]!).val) + 19 =
      ((∑ i ∈ range 0, limbWeight i * (fe[i]!).val) + 19) % limbWeight 0 + 19 * limbWeight 0 := by
    rewrite [range_zero, sum_empty, limbWeight]; decide
  have hq_bound (x : U32) (n : Nat) : x.val >>> n ≤ 2 ^ 32 / 2 ^ n := by
    rewrite [Nat.shiftRight_eq_div_pow]
    exact Nat.div_le_div_right (by apply Nat.le_of_lt (UScalar.hBounds _))
  iterate 9
    have hq_carry := (carry_remainder fe hq_carry_old ‹_› ‹_› ‹_›).1
    clear hq_carry_old
    step* 2
    · subst ‹_›
      rewrite [Array.getElem_val_eq_getElem!]
      apply Nat.le_trans
        (by exact Nat.add_le_add
              (by exact Nat.le_of_lt (hfe _ (by decide)))
              (by simp only [‹(_ : Nat) = _ >>> _›]; exact hq_bound _ _))
        (by rewrite [U32.max_def, U32.numBits_eq]; decide)
    step
    rename' hq_carry => hq_carry_old
  have hq_carry := (carry_remainder fe hq_carry_old ‹_› ‹_› ‹_›).1
  clear hq_carry_old
  simp only [Nat.reduceAdd] at hq_carry
  have hsum : ∑ i ∈ range 10, limbWeight i * (fe[i]!).val = fe.asNat := by
    rw [asNat_def, Array.asNat2625_eq_sum]
  have hW : limbWeight 10 = 2 ^ 255 := by simp [limbWeight]
  rw [hsum, hW] at hq_carry
  have hfe_bound : fe.asNat < 2 * p := by
    rw [← hsum, p_def]
    apply Nat.lt_trans
      (by exact sum_lt_sum_of_nonempty
            (g := fun i => limbWeight i * (limbRadix i + i % 2 * 2 ^ 18)) (s := range 10)
            (by decide)
            (by intro i hi
                rewrite [limbWeight, Nat.mul_lt_mul_left (by exact Nat.two_pow_pos _)]
                rewrite [mem_range] at hi; exact hfe i hi))
      (by simp only [limbWeight, limbRadix, sum_range_succ, sum_range_zero]; decide)
  have hp := p_add_nineteen
  have hmod := Nat.mod_lt (fe.asNat + 19) (Nat.two_pow_pos 255)
  simp only [Nat.reducePow] at hq_carry hp hmod
  have hq9 : q9.val = 0 ∨ q9.val = 1 := by omega
  step*
  refine ⟨?_, ?_, by omega⟩
  · simp only [*, Array.getElem_val_eq_getElem!]
  · rcases hq9 with h | h
    · rw [h, eq_comm]
      exact Nat.div_eq_of_lt (by omega)
    · rw [h, eq_comm]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)


/-- Masking limb `n` of the array `A` with `c = 2 ^ (26 - n % 2) - 1` finishes that limb. Given that
the finished limbs below `n` add up to the remainder `R` (`hP`) and are within their radix (`hB`),
the same then holds one limb further, with the remainder `R'` of the mask identity `hM` of
`carry_remainder`. -/
private theorem mask_step {n R R' : Nat} {A : Std.Array U32 10#usize} {k : Usize} {s mk c : U32}
    (hn : n < 10)
    (hP : ∑ j ∈ range n, limbWeight j * (A[j]!).val = R)
    (hB : ∀ j < n, (A[j]!).val < limbRadix j) (hk : k.val = n)
    (hmk : mk.val = (s &&& c).val) (hc : c.val = limbRadix n - 1)
    (hM : R' = R + (s.val % limbRadix n) * limbWeight n) :
    ∑ j ∈ range (n + 1), limbWeight j * ((A.set k mk)[j]!).val = R' ∧
    (∀ j < n + 1, ((A.set k mk)[j]!).val < limbRadix j) := by
  rw [UScalar.val_and, hc, limbRadix, Nat.and_two_pow_sub_one_eq_mod, ← limbRadix] at hmk
  --Limbs below `n` are untouched by the write
  have hlow : ∀ j < n, (A.set k mk)[j]! = A[j]! := fun j hj =>
    Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hk]; exact Nat.ne_of_gt hj)
  --Limb `n` holds the mask
  have hmid : (A.set k mk)[n]! = mk :=
    Array.getElem!_Nat_set_eq _ _ _ _ ⟨hk, by
      simp only [Std.Array.length, Array.length_eq]; exact hn⟩
  refine ⟨?_, fun j hj => ?_⟩
  --The partial sum of the finished limbs
  · rw [sum_range_succ, sum_congr rfl (fun j hj => by rw [hlow j (mem_range.mp hj)]), hP, hmid, hmk,
      hM, Nat.mul_comm]
  --The bounds on the finished limbs
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [hlow j hj]; exact hB j hj
    · rw [hmid, hmk]; exact Nat.mod_lt _ (by unfold limbRadix; exact Nat.two_pow_pos _)


/-- Array bookkeeping for one round of the carry chain in `calcCanonical`. Round `n` writes the
carry-propagated sum `s'` into limb `n + 1` and the masked pending sum `s &&& c` into limb `n`.
Given the invariants of the current array `A`
- `htail`: the limbs above `n` are still those of `fe`,
- `hP`: the finished limbs below `n` add up to the remainder `R`,
- `hB`: the finished limbs below `n` are within their radix,
the lemma re-establishes them for the new array `A''` one limb further, together with the value
`s'` now pending in limb `n + 1`. The carry write leaves the limbs below `n` untouched, so the
masking itself is handled by `mask_step`. -/
private theorem mask_round {n R R' : Nat} {A A' A'' : Std.Array U32 10#usize} {i k : Usize}
    {s s' mk c : U32} (fe : FieldElement2625) (hn : n + 1 < 10)
    (htail : ∀ j, n < j → j < 10 → A[j]! = fe[j]!)
    (hP : ∑ j ∈ range n, limbWeight j * (A[j]!).val = R)
    (hB : ∀ j < n, (A[j]!).val < limbRadix j)
    (hA' : A' = A.set i s') (hA'' : A'' = A'.set k mk) (hi : i.val = n + 1) (hk : k.val = n)
    (hmk : mk.val = (s &&& c).val) (hc : c.val = limbRadix n - 1)
    (hM : R' = R + (s.val % limbRadix n) * limbWeight n) :
    A''[n + 1]! = s' ∧
    (∀ j, n + 1 < j → j < 10 → A''[j]! = fe[j]!) ∧
    ∑ j ∈ range (n + 1), limbWeight j * (A''[j]!).val = R' ∧
    (∀ j < n + 1, (A''[j]!).val < limbRadix j) := by
  subst hA'' hA'
  --Limbs below `n` are untouched by the carry write
  have hlow : ∀ j < n, (A.set i s')[j]! = A[j]! := fun j hj =>
    Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hi]; exact Nat.ne_of_gt (Nat.lt_succ_of_lt hj))
  obtain ⟨hP', hB'⟩ := mask_step (Nat.lt_of_succ_lt hn)
    (by rw [sum_congr rfl (fun j hj => by rw [hlow j (mem_range.mp hj)])]; exact hP)
    (fun j hj => by rw [hlow j hj]; exact hB j hj) hk hmk hc hM
  refine ⟨?_, fun j hj hj10 => ?_, hP', hB'⟩
  --The pending sum in limb `n + 1`
  · rw [Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hk]; exact Nat.ne_of_lt (Nat.lt_succ_self n))]
    exact Array.getElem!_Nat_set_eq _ _ _ _ ⟨hi, by
      simp only [Std.Array.length, Array.length_eq]; exact hn⟩
  --The untouched limbs
  · rw [Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hk]; exact Nat.ne_of_lt (Nat.lt_of_succ_lt hj)),
      Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hi]; exact Nat.ne_of_lt hj)]
    exact htail j (Nat.lt_of_succ_lt hj) hj10


/-- A bound on a shifted `u32`. -/
private theorem shiftRight_le_two_pow (x : U32) (n : Nat) : x.val >>> n ≤ 2 ^ 32 / 2 ^ n := by
  rewrite [Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_div_right (by apply Nat.le_of_lt (UScalar.hBounds _))

/-- The state before carry round `n` of `calcCanonical`: the carry identity for the first `n`
limbs plus `m` with the carry `q` into limb `n`; limb `n` of `A` holds `cur = fe[n] + q`, the limbs
above are those of `fe`, and the limbs below are finished (their sum is the remainder, each limb
within its radix). -/
private def RoundInv (fe : FieldElement2625) (m n : ℕ) (A : Std.Array U32 10#usize) (cur : U32)
    (q : ℕ) : Prop :=
  (∑ i ∈ range n, limbWeight i * (fe[i]!).val) + m =
      ((∑ i ∈ range n, limbWeight i * (fe[i]!).val) + m) % limbWeight n + q * limbWeight n ∧
    A[n]! = cur ∧ cur.val = (fe[n]!).val + q ∧
    (∀ j, n < j → j < 10 → A[j]! = fe[j]!) ∧
    ∑ j ∈ range n, limbWeight j * (A[j]!).val =
      ((∑ i ∈ range n, limbWeight i * (fe[i]!).val) + m) % limbWeight n ∧
    ∀ j < n, (A[j]!).val < limbRadix j

/-- Carry rounds 0 to 4 of `calcCanonical`, with the two mask constants. -/
@[local step]
private theorem roundsLow_spec (fe : FieldElement2625) (hfe : ∀ i : ℕ, i < 10 → fe[i]!.val < 2 ^ 26)
    (m q : ℕ) (A : Std.Array U32 10#usize) (cur : U32) (hI : RoundInv fe m 0 A cur q) :
    roundsLow A ⦃ (c26 : U32) (c25 : U32) (A' : Std.Array U32 10#usize) =>
      c26.val = 2 ^ 26 - 1 ∧ c25.val = 2 ^ 25 - 1 ∧ ∃ cur' q', RoundInv fe m 5 A' cur' q' ⦄ := by
  have hq_bound := shiftRight_le_two_pow
  obtain ⟨hcarry_old, hcur, hadd, htail, hP, hB⟩ := hI
  unfold roundsLow
  iterate 2
    step* 9 -assumTac
    · subst ‹(_ : U32) = (_ : List U32)[_]'_›
      simp (disch := decide) only [Array.getElem_val_eq_getElem!, htail]
      apply Nat.le_trans (Nat.add_le_add (Nat.le_of_lt (hfe _ (by decide)))
        (by rewrite [‹UScalar.val _ = UScalar.val _ >>> _›]; exact hq_bound _ _))
        (by rewrite [U32.max_def, U32.numBits_eq]; decide)
    have hpeel : ∀ {A B : Std.Array U32 10#usize} {k : Usize} {v : U32} {j : Nat},
        A = B.set k v → k.val ≠ j → A[j]! = B[j]! := fun hA hk => by
      rw [hA]; exact Array.getElem!_Nat_set_ne _ _ _ _ hk
    subst ‹(_ : U32) = (_ : List U32)[_]'_›
    subst ‹(_ : U32) = (_ : List U32)[_]'_›
    subst ‹(_ : U32) = (_ : List U32)[_]'_›
    simp only [Array.getElem_val_eq_getElem!, hcur] at ‹UScalar.val _ = UScalar.val _ >>> _›
    simp (disch := decide) only [Array.getElem_val_eq_getElem!, htail]
      at ‹UScalar.val _ = UScalar.val _ + UScalar.val _›
    simp only [Array.getElem_val_eq_getElem!] at ‹UScalar.val _ = UScalar.val (_ &&& _)›
    rw [hpeel ‹_› (by decide), hcur] at ‹UScalar.val _ = UScalar.val (_ &&& _)›
    obtain ⟨hcarry, hM⟩ := carry_remainder fe hcarry_old ‹_› ‹_›
      (Array.getElem_val_eq_getElem! _ _ (by
        simp only [Array.length_eq, UScalar.ofNatCore_val_eq]; decide)).symm
    obtain ⟨hcur', htail', hP', hB'⟩ :=
      mask_round fe (by decide) htail hP hB ‹_› ‹_› (by decide) (by decide) ‹_› ‹_› hM
    clear hpeel hcarry_old hcur htail hP hB hM ‹_ = Std.Array.set _ _ _›
    clear ‹_ = Std.Array.set _ _ _›
    rename' hcarry => hcarry_old, hcur' => hcur, htail' => htail, hP' => hP, hB' => hB
  iterate 3
    step* 8 -assumTac
    · subst ‹(_ : U32) = (_ : List U32)[_]'_›
      simp (disch := decide) only [Array.getElem_val_eq_getElem!, htail]
      apply Nat.le_trans (Nat.add_le_add (Nat.le_of_lt (hfe _ (by decide)))
        (by rewrite [‹UScalar.val _ = UScalar.val _ >>> _›]; exact hq_bound _ _))
        (by rewrite [U32.max_def, U32.numBits_eq]; decide)
    have hpeel : ∀ {A B : Std.Array U32 10#usize} {k : Usize} {v : U32} {j : Nat},
        A = B.set k v → k.val ≠ j → A[j]! = B[j]! := fun hA hk => by
      rw [hA]; exact Array.getElem!_Nat_set_ne _ _ _ _ hk
    subst ‹(_ : U32) = (_ : List U32)[_]'_›
    subst ‹(_ : U32) = (_ : List U32)[_]'_›
    subst ‹(_ : U32) = (_ : List U32)[_]'_›
    simp only [Array.getElem_val_eq_getElem!, hcur] at ‹UScalar.val _ = UScalar.val _ >>> _›
    simp (disch := decide) only [Array.getElem_val_eq_getElem!, htail]
      at ‹UScalar.val _ = UScalar.val _ + UScalar.val _›
    simp only [Array.getElem_val_eq_getElem!] at ‹UScalar.val _ = UScalar.val (_ &&& _)›
    rw [hpeel ‹_› (by decide), hcur] at ‹UScalar.val _ = UScalar.val (_ &&& _)›
    obtain ⟨hcarry, hM⟩ := carry_remainder fe hcarry_old ‹_› ‹_›
      (Array.getElem_val_eq_getElem! _ _ (by
        simp only [Array.length_eq, UScalar.ofNatCore_val_eq]; decide)).symm
    obtain ⟨hcur', htail', hP', hB'⟩ :=
      mask_round fe (by decide) htail hP hB ‹_› ‹_› (by decide) (by decide) ‹_› ‹_› hM
    clear hpeel hcarry_old hcur htail hP hB hM ‹_ = Std.Array.set _ _ _›
    clear ‹_ = Std.Array.set _ _ _›
    rename' hcarry => hcarry_old, hcur' => hcur, htail' => htail, hP' => hP, hB' => hB
  exact ⟨by assumption, by assumption, _, _, hcarry_old, hcur, by assumption, htail, hP, hB⟩

/-- Carry rounds 5 to 8 of `calcCanonical`. -/
@[local step]
private theorem roundsHigh_spec (fe : FieldElement2625)
  (hfe : ∀ i : ℕ, i < 10 → fe[i]!.val < 2 ^ 26)
    (c26 c25 : U32) (hc26 : c26.val = 2 ^ 26 - 1) (hc25 : c25.val = 2 ^ 25 - 1)
    (m q : ℕ) (A : Std.Array U32 10#usize) (cur : U32) (hI : RoundInv fe m 5 A cur q) :
    roundsHigh c26 c25 A ⦃ (A' : Std.Array U32 10#usize) =>
      ∃ cur' q', RoundInv fe m 9 A' cur' q' ⦄ := by
  have hq_bound := shiftRight_le_two_pow
  obtain ⟨hcarry_old, hcur, hadd, htail, hP, hB⟩ := hI
  unfold roundsHigh
  iterate 4
    step* 8 -assumTac
    · subst ‹(_ : U32) = (_ : List U32)[_]'_›
      simp (disch := decide) only [Array.getElem_val_eq_getElem!, htail]
      apply Nat.le_trans (Nat.add_le_add (Nat.le_of_lt (hfe _ (by decide)))
        (by rewrite [‹UScalar.val _ = UScalar.val _ >>> _›]; exact hq_bound _ _))
        (by rewrite [U32.max_def, U32.numBits_eq]; decide)
    have hpeel : ∀ {A B : Std.Array U32 10#usize} {k : Usize} {v : U32} {j : Nat},
        A = B.set k v → k.val ≠ j → A[j]! = B[j]! := fun hA hk => by
      rw [hA]; exact Array.getElem!_Nat_set_ne _ _ _ _ hk
    subst ‹(_ : U32) = (_ : List U32)[_]'_›
    subst ‹(_ : U32) = (_ : List U32)[_]'_›
    subst ‹(_ : U32) = (_ : List U32)[_]'_›
    simp only [Array.getElem_val_eq_getElem!, hcur] at ‹UScalar.val _ = UScalar.val _ >>> _›
    simp (disch := decide) only [Array.getElem_val_eq_getElem!, htail]
      at ‹UScalar.val _ = UScalar.val _ + UScalar.val _›
    simp only [Array.getElem_val_eq_getElem!] at ‹UScalar.val _ = UScalar.val (_ &&& _)›
    rw [hpeel ‹_› (by decide), hcur] at ‹UScalar.val _ = UScalar.val (_ &&& _)›
    obtain ⟨hcarry, hM⟩ := carry_remainder fe hcarry_old ‹_› ‹_›
      (Array.getElem_val_eq_getElem! _ _ (by
        simp only [Array.length_eq, UScalar.ofNatCore_val_eq]; decide)).symm
    obtain ⟨hcur', htail', hP', hB'⟩ :=
      mask_round fe (by decide) htail hP hB ‹_› ‹_› (by decide) (by decide) ‹_› ‹_› hM
    clear hpeel hcarry_old hcur htail hP hB hM ‹_ = Std.Array.set _ _ _›
    clear ‹_ = Std.Array.set _ _ _›
    rename' hcarry => hcarry_old, hcur' => hcur, htail' => htail, hP' => hP, hB' => hB
  exact ⟨_, _, hcarry_old, hcur, by assumption, htail, hP, hB⟩

/-- Third phase: the result is the canonical representative `fe % p`, with every limb within its
radix. -/
@[local step]
private theorem calcCanonical_spec (fe : FieldElement2625) (i20 : U32) (q9 : UScalar UScalarTy.U32)
    (hi20 : i20 = fe[0]!)
    (hfe : ∀ i : ℕ, i < 10 → fe[i]!.val < 2 ^ 26)
    (hq9 : q9.val = fe.asNat / p)
    (hq9' : q9.val ≤ 1) :
    calcCanonical fe i20 q9 ⦃ (h19 : FieldElement2625) =>
      h19.asNat = fe.asNat % p ∧
      (∀ i : ℕ, i < 10 → h19[i]!.val < limbRadix i) ⦄ := by
  rw [calcCanonical_decomp]
  have hq_bound := shiftRight_le_two_pow
  --Prefix: `19 * q9` and `i20 + 19 * q9` written into limb 0 of a new array
  step* 3 -assumTac
  simp only [hi20, ‹UScalar.val _ = 19 * UScalar.val _›]
    at ‹UScalar.val _ = UScalar.val _ + UScalar.val _›
  /- Initial invariants, with `19 * q9` as the carry into limb 0: the carry identity, and, carried
  over to the new array along its defining equation, the value pending in limb 0, the untouched
  limbs above 0, and the (empty) partial sum and bounds of the finished limbs. -/
  have hcarry_old : (∑ i ∈ range 0, limbWeight i * (fe[i]!).val) + 19 * q9.val =
      ((∑ i ∈ range 0, limbWeight i * (fe[i]!).val) + 19 * q9.val) % limbWeight 0 +
      19 * q9.val * limbWeight 0 := by
    simp only [range_zero, sum_empty, limbWeight, Nat.zero_add, Nat.reduceDiv, Nat.reduceMul,
      Nat.pow_zero, Nat.mod_one, Nat.mul_one]
  have hcur := (congrArg (·[0]!) ‹_ = Std.Array.set _ _ _›).trans
    (Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by
      simp only [Std.Array.length, Array.length_eq]; decide⟩)
  obtain ⟨htail, hP, hB⟩ := (congrArg (fun A : Std.Array U32 10#usize =>
      (∀ j : ℕ, 0 < j → j < 10 → A[j]! = fe[j]!) ∧
      ∑ j ∈ range 0, limbWeight j * (A[j]!).val =
        ((∑ i ∈ range 0, limbWeight i * (fe[i]!).val) + 19 * q9.val) % limbWeight 0 ∧
      ∀ j : ℕ, j < 0 → (A[j]!).val < limbRadix j) ‹_ = Std.Array.set _ _ _›).mpr
    ⟨fun j hj _ => Array.getElem!_Nat_set_ne _ _ _ _ (by
        rw [UScalar.ofNatCore_val_eq]; exact Nat.ne_of_lt hj),
      by simp only [range_zero, sum_empty, limbWeight, Nat.zero_add, Nat.reduceDiv, Nat.reduceMul,
        Nat.pow_zero, Nat.mod_one],
      fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  clear ‹_ = Std.Array.set _ _ _›
  /- Rounds 0 to 8: carry out of limb `n` into limb `n + 1`, then mask limb `n`. Arrays are never
  substituted, so all terms stay small. Each round
  - steps through the whole round in one `step*` call (rounds 0 and 1 take one extra step for
    fetching the constants `LOW_26_BITS` and `LOW_25_BITS`), discharging the overflow of the
    addition into limb `n + 1` in the side goal,
  - substitutes the three reads and resolves them with `hcur` and `htail`; the read of limb `n`
    after the carry write is peeled off that write with `hpeel`,
  - propagates the carry identity with `carry_remainder` and the array invariants with
    `mask_round`. -/
  have I0 : RoundInv fe (19 * q9.val) 0 _ _ (19 * q9.val) :=
    ⟨hcarry_old, hcur, ‹_›, htail, hP, hB⟩
  clear hcarry_old hcur htail hP hB
  step with roundsLow_spec fe hfe _ _ _ _ I0 as ⟨c26, c25, A5, hc26, hc25, cur5, q5, I5⟩
  step with roundsHigh_spec fe hfe c26 c25 hc26 hc25 _ _ _ _ I5 as ⟨A9, cur9, q9c, I9⟩
  obtain ⟨hcarry_old, hcur, hadd, htail, hP, hB⟩ := I9
  --Round 9: the top carry out of limb 9
  step* 2 -assumTac
  subst ‹(_ : U32) = (_ : List U32)[_]'_›
  simp only [Array.getElem_val_eq_getElem!, hcur] at ‹UScalar.val _ = UScalar.val _ >>> _›
  obtain ⟨hcarry, hM⟩ := carry_remainder fe hcarry_old ‹_› ‹_›
    (Array.getElem_val_eq_getElem! _ _ (by
      simp only [Array.length_eq, UScalar.ofNatCore_val_eq]; decide)).symm
  --The carry identity at `n = 10` reads `fe + 19 * q9 = R + c * 2 ^ 255` with the top carry `c`
  have hsum : ∑ i ∈ range 10, limbWeight i * (fe[i]!).val = fe.asNat := by
    rw [asNat_def, Array.asNat2625_eq_sum]
  have hW : limbWeight 10 = 2 ^ 255 := by simp [limbWeight]
  simp only [Nat.reduceAdd, hsum, hW] at hcarry
  have hdiv : (fe.asNat + 19 * q9.val) / 2 ^ 255 = q9.val := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq9' with h | h
    --`q9 = 0`: `fe < p < 2 ^ 255`
    · rw [h, eq_comm, Nat.div_eq_zero_iff_lt p_pos] at hq9
      rw [h, Nat.mul_zero, Nat.add_zero]
      exact Nat.div_eq_of_lt (Nat.lt_trans hq9 p_lt_two_pow_255)
    --`q9 = 1`: `p ≤ fe < 2 * p`, so `2 ^ 255 ≤ fe + 19 < 2 * 2 ^ 255`
    · rw [h] at hq9
      rw [h, Nat.mul_one]
      apply Nat.div_eq_of_lt_le
      · rw [Nat.one_mul, ← p_add_nineteen]
        exact Nat.add_le_add_right
          (Nat.one_mul p ▸ (Nat.le_div_iff_mul_le p_pos).mp (Nat.le_of_eq hq9)) 19
      · have hlt := Nat.lt_mul_div_succ fe.asNat p_pos
        rw [← hq9] at hlt
        rw [← p_add_nineteen, Nat.mul_add, Nat.mul_comm]
        exact Nat.add_lt_add hlt (by decide)
  --So the top carry is `q9`, which replaces it from here on
  have hc := congrArg (· / 2 ^ 255) hcarry
  rw [hdiv, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 255),
    Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), Nat.zero_add] at hc
  obtain rfl := UScalar.eq_of_val_eq hc
  /- The remainder at `n = 10` is the canonical value: subtracting `q9 * 2 ^ 255` from
  `fe + 19 * q9` leaves `fe - q9 * p = fe % p`. -/
  have hR10 : (fe.asNat + 19 * q9.val) % 2 ^ 255 = fe.asNat % p := by
    rw [Nat.eq_sub_of_add_eq hcarry.symm, ← p_add_nineteen, Nat.mul_add, Nat.mul_comm q9.val 19,
      Nat.add_sub_add_right, hq9, Nat.mul_comm, ← Nat.mod_eq_sub_mul_div]
  --Both branches of the final `massert` end with the mask of limb 9
  split
  --`q9 = 0`: no assertion to discharge
  next =>
    step* -assumTac
    subst ‹_ = Std.Array.set _ _ _›
    simp only [Array.getElem_val_eq_getElem!, hcur] at ‹UScalar.val _ = UScalar.val (_ &&& _)›
    obtain ⟨hP', hB'⟩ := mask_step (k := 9#usize) (by decide) hP hB (by decide) ‹_› ‹_› hM
    refine ⟨?_, hB'⟩
    simp only [Nat.reduceAdd, hW, hsum] at hP'
    rw [asNat_def, Array.asNat2625_eq_sum, hP', hR10]
  --`q9 ≠ 0`: the assertion that the top carry is 1 holds as `q9 ≤ 1`
  next hne =>
    step* -assumTac
    subst ‹_ = Std.Array.set _ _ _›
    simp only [Array.getElem_val_eq_getElem!, hcur] at ‹UScalar.val _ = UScalar.val (_ &&& _)›
    obtain ⟨hP', hB'⟩ := mask_step (k := 9#usize) (by decide) hP hB (by decide) ‹_› ‹_› hM
    refine ⟨?_, hB'⟩
    simp only [Nat.reduceAdd, hW, hsum] at hP'
    rw [asNat_def, Array.asNat2625_eq_sum, hP', hR10]


/-- Writing byte `n` of `s` as the low byte of `x >>> r`. The bytes written so far plus the bits of
`x` still pending above them add up to `V`; this stays so with one more byte written and 8 fewer
bits of `x` pending. The hypotheses are the postconditions of the update, the cast and the shift,
in this order: when they are picked up by `‹_›`, each one is searched for only after its left-hand
side is fixed by the previous ones, which keeps the search cheap. -/
private theorem byte_step {s s' : Std.Array U8 32#usize} {k : Usize} {n r V : Nat} {x y : U32}
    {b : U8} (hI : ∑ i ∈ range n, 2 ^ (8 * i) * (s[i]!).val + 2 ^ (8 * n) * (x.val >>> r) = V)
    (hs : s' = s.set k b) (hb : b = UScalar.cast .U8 y) (hy : y.val = x.val >>> r)
    (hk : k.val = n ∧ n < 32 := by decide) :
    ∑ i ∈ range (n + 1), 2 ^ (8 * i) * (s'[i]!).val + 2 ^ (8 * (n + 1)) * (x.val >>> (r + 8)) =
      V := by
  subst hs
  rw [sum_range_succ, sum_congr rfl (fun i hi => by
      rw [Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hk.1]; exact Nat.ne_of_gt (mem_range.mp hi))]),
    Array.getElem!_Nat_set_eq _ _ _ _ ⟨hk.1, by
      simp only [Std.Array.length, Array.length_eq]; exact hk.2⟩,
    hb, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, hy, Nat.add_assoc, ← hI,
    Nat.add_left_cancel_iff, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow _ 8, Nat.mul_succ,
    Nat.pow_add, Nat.mul_assoc, ← Nat.mul_add, Nat.mod_add_div]


/-- Writing byte `n` of `s` as the low byte of `(x >>> r) ||| (w <<< t)`, where `x` is limb `l` of
`h` and `w` is limb `l + 1`. The last `t` bits of `x` and the first `8 - t` bits of `w` are joined,
so the invariant of `byte_step` moves on to limb `l + 1`, with the limb sum growing by one term.
The hypotheses are the postconditions of the update, the cast, the `|||`, the left shift, the read
of `w`, the shift and the read of `x`, in this order (see `byte_step`). The numeric side conditions
say that the remaining bits of `x` are exactly `t` (given the limb bounds), that byte `n` reaches
`t` bits into limb `l + 1`, and that `w <<< t` does not overflow. -/
private theorem byte_join_step {h : FieldElement2625} {s s' : Std.Array U8 32#usize} {k : Usize}
    {l n r t : Nat} {x y w z o : U32} {b : U8}
    {hl : l < (↑h : List U32).length} {hl' : l + 1 < (↑h : List U32).length}
    (hbound : ∀ i : ℕ, i < 10 → h[i]!.val < limbRadix i)
    (hI : ∑ i ∈ range n, 2 ^ (8 * i) * (s[i]!).val + 2 ^ (8 * n) * (x.val >>> r) =
      ∑ i ∈ range (l + 1), limbWeight i * (h[i]!).val)
    (hs : s' = s.set k b) (hb : b = UScalar.cast .U8 o) (ho : o.val = (y ||| z).val)
    (hz : z.val = w.val <<< t % U32.size) (hw : w = (↑h : List U32)[l + 1])
    (hy : y.val = x.val >>> r) (hx : x = (↑h : List U32)[l])
    (hnum : k.val = n ∧ n < 32 ∧ r + t = 26 - l % 2 ∧
      8 * n + t = 26 * ((l + 1 + 1) / 2) + 25 * ((l + 1) / 2) ∧ t ≤ 6 ∧ l + 1 < 10 := by decide) :
    ∑ i ∈ range (n + 1), 2 ^ (8 * i) * (s'[i]!).val + 2 ^ (8 * (n + 1)) * (w.val >>> (8 - t)) =
      ∑ i ∈ range (l + 1 + 1), limbWeight i * (h[i]!).val := by
  obtain ⟨hk, hn, hrt, he, ht, hl10⟩ := hnum
  subst hs
  rw [Array.getElem_val_eq_getElem! _ _ hl] at hx
  rw [Array.getElem_val_eq_getElem! _ _ hl'] at hw
  --The bits of `x` left after the shift fit below the join
  have hxb : x.val >>> r < 2 ^ t := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos r), ← Nat.pow_add,
      Nat.add_comm, hrt, hx]
    exact hbound l (Nat.lt_of_succ_lt hl10)
  --The left shift of `w` does not wrap
  have hzw : z.val = w.val * 2 ^ t := by
    rw [hz, Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    rw [U32.size_def, U32.numBits_eq]
    apply Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (hw ▸ hbound (l + 1) hl10)
      (Nat.two_pow_pos t))
    rw [limbRadix, ← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide)
      (Nat.le_trans (Nat.add_le_add (Nat.sub_le 26 _) ht) (by decide))
  rw [UScalar.val_or, hy, hzw, Nat.or_mul_two_pow_eq_add_of_lt hxb] at ho
  --The new pending bits of `w` are the high bits of the joined value
  have hdiv : (x.val >>> r + w.val * 2 ^ t) / 2 ^ 8 = w.val >>> (8 - t) := by
    have h8 : 2 ^ 8 = 2 ^ t * 2 ^ (8 - t) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_trans ht (by decide))]
    rw [h8, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos t),
      Nat.div_eq_of_lt hxb, Nat.zero_add, Nat.shiftRight_eq_div_pow]
  rw [sum_range_succ, sum_congr rfl (fun i hi => by
      rw [Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hk]; exact Nat.ne_of_gt (mem_range.mp hi))]),
    Array.getElem!_Nat_set_eq _ _ _ _ ⟨hk, by
      simp only [Std.Array.length, Array.length_eq]; exact hn⟩,
    hb, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, ho, ← hdiv, Nat.mul_succ, Nat.pow_add,
    Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, Nat.mod_add_div, sum_range_succ _ (l + 1), ← hI,
    Nat.mul_add, ← Nat.add_assoc, Nat.add_left_cancel_iff, limbWeight, ← he, Nat.pow_add, hw,
    Nat.mul_comm _ (2 ^ t), Nat.mul_assoc]


/-- Bytes 0 to 15 of `toArray`: limbs 0 to 4, which end exactly at bit 128. -/
@[local step]
private theorem packLow_spec (h19 : FieldElement2625)
    (hbound : ∀ i : ℕ, i < 10 → h19[i]!.val < limbRadix i) (s : Std.Array U8 32#usize) :
    packLow h19 s ⦃ (s16 : Std.Array U8 32#usize) =>
      ∑ i ∈ range 16, 2 ^ (8 * i) * (s16[i]!).val =
        ∑ i ∈ range 5, limbWeight i * (h19[i]!).val ⦄ := by
  unfold packLow
  step* -assumTac
  have hI0 : ∀ {x : U32} {h0 : 0 < (↑h19 : List U32).length}, x = (↑h19 : List U32)[0]'h0 →
      ∑ i ∈ range 0, 2 ^ (8 * i) * (s[i]!).val +
        2 ^ (8 * 0) * (x.val >>> 0) = ∑ i ∈ range (0 + 1), limbWeight i * (h19[i]!).val :=
    fun hx => by
      rw [hx, Array.getElem_val_eq_getElem!]
      simp only [range_zero, sum_empty, sum_range_one, limbWeight, Nat.mul_zero, Nat.pow_zero,
        Nat.shiftRight_zero, Nat.zero_add, Nat.reduceDiv]
  have hI := byte_step (hI0 ‹_›) ‹_› ‹_› ‹_›
  clear hI0
  iterate 2
    replace hI := byte_step hI ‹_› ‹_› ‹_›
  replace hI := byte_join_step hbound hI ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  iterate 3
    iterate 2
      replace hI := byte_step hI ‹_› ‹_› ‹_›
    replace hI := byte_join_step hbound hI ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  iterate 3
    replace hI := byte_step hI ‹_› ‹_› ‹_›
  --Limb 4 is used up
  have hdone : ∀ {s' : Std.Array U8 32#usize} {x : U32} {h4 : 4 < (↑h19 : List U32).length},
      x = (↑h19 : List U32)[4]'h4 →
      ∑ i ∈ range 16, 2 ^ (8 * i) * (s'[i]!).val + 2 ^ (8 * 16) * (x.val >>> 26) =
        ∑ i ∈ range 5, limbWeight i * (h19[i]!).val →
      ∑ i ∈ range 16, 2 ^ (8 * i) * (s'[i]!).val =
        ∑ i ∈ range 5, limbWeight i * (h19[i]!).val := fun hx hI => by
    rw [hx, Array.getElem_val_eq_getElem!, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (by apply hbound 4 (by decide)), Nat.mul_zero, Nat.add_zero] at hI
    exact hI
  exact hdone ‹_› hI

/-- Bytes 16 to 31 of `toArray`: limbs 5 to 9; the value of all 32 bytes, and the top bit of the
last byte is clear, as limb 9 has 25 bits. -/
@[local step]
private theorem packHigh_spec (h19 : FieldElement2625)
    (hbound : ∀ i : ℕ, i < 10 → h19[i]!.val < limbRadix i) (s16 : Std.Array U8 32#usize)
    (hI16 : ∑ i ∈ range 16, 2 ^ (8 * i) * (s16[i]!).val =
      ∑ i ∈ range 5, limbWeight i * (h19[i]!).val) :
    packHigh h19 s16 ⦃ (s32 : Std.Array U8 32#usize) =>
      s32.asNat 8 = h19.asNat ∧ (s32[31]!).val < 2 ^ 7 ⦄ := by
  unfold packHigh
  step* -assumTac
  have hstart : ∀ {x' : U32} {h5 : 5 < (↑h19 : List U32).length},
      x' = (↑h19 : List U32)[5]'h5 →
      ∑ i ∈ range 16, 2 ^ (8 * i) * (s16[i]!).val + 2 ^ (8 * 16) * (x'.val >>> 0) =
        ∑ i ∈ range 6, limbWeight i * (h19[i]!).val := fun hx' => by
    rw [hx', Array.getElem_val_eq_getElem!, Nat.shiftRight_zero, sum_range_succ _ 5, ← hI16]
    rfl
  have hI := byte_step (hstart ‹_›) ‹_› ‹_› ‹_›
  clear hstart
  iterate 2
    replace hI := byte_step hI ‹_› ‹_› ‹_›
  replace hI := byte_join_step hbound hI ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  iterate 3
    iterate 2
      replace hI := byte_step hI ‹_› ‹_› ‹_›
    replace hI := byte_join_step hbound hI ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  iterate 3
    replace hI := byte_step hI ‹_› ‹_› ‹_›
  have hend : ∀ {s : Std.Array U8 32#usize} {x : U32} {h9 : 9 < (↑h19 : List U32).length},
      x = (↑h19 : List U32)[9]'h9 →
      ∑ i ∈ range 32, 2 ^ (8 * i) * (s[i]!).val + 2 ^ (8 * 32) * (x.val >>> 26) =
        ∑ i ∈ range 10, limbWeight i * (h19[i]!).val → s.asNat 8 = h19.asNat :=
    fun hx hI => by
      rw [hx, Array.getElem_val_eq_getElem!, Nat.shiftRight_eq_div_pow,
        Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (hbound 9 (by decide)) (by decide)), Nat.mul_zero,
        Nat.add_zero] at hI
      rw [Array.asNat_eq_sum, UScalar.ofNatCore_val_eq, asNat_def, Array.asNat2625_eq_sum]
      exact hI
  have hlast : ∀ {s s' : Std.Array U8 32#usize} {x y : U32} {b : U8}
      {h9 : 9 < (↑h19 : List U32).length}, x = (↑h19 : List U32)[9]'h9 →
      y.val = x.val >>> 18 → b = UScalar.cast .U8 y → s' = s.set 31#usize b →
      (s'[31]!).val < 2 ^ 7 := fun hx hy hb hs => by
    subst hs
    rw [Array.getElem!_Nat_set_eq _ 31#usize 31 _ ⟨rfl, by
        simp only [Std.Array.length, Array.length_eq]; decide⟩,
      hb, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, hy, hx, Array.getElem_val_eq_getElem!]
    apply Nat.lt_of_le_of_lt (Nat.mod_le _ _)
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 18), ← Nat.pow_add]
    exact hbound 9 (by decide)
  exact ⟨hend ‹_› hI, hlast ‹_› ‹_› ‹_› ‹_›⟩

/-- Fourth phase: packing ten limbs within their radix into 32 bytes preserves the value, and the
top bit of the last byte is clear. -/
@[local step]
private theorem toArray_spec (h19 : FieldElement2625)
    (hbound : ∀ i : ℕ, i < 10 → h19[i]!.val < limbRadix i) :
    toArray h19 ⦃ (result : Array U8 32#usize) =>
      result.asNat 8 = h19.asNat ⦄ := by
  rw [toArray_decomp]
  dsimp only
  step with packLow_spec h19 hbound as ⟨s16, hs16⟩
  step with packHigh_spec h19 hbound s16 hs16 as ⟨s32, hs32, hlt⟩
  step as ⟨c, hc⟩
  step as ⟨d, hd⟩
  step
  · apply UScalar.eq_of_val_eq
    rw [hd, UScalar.val_and, hc, Array.getElem_val_eq_getElem!]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, show (128#u8).val = 2 ^ 7 from rfl, show (0#u8).val = 0 from rfl,
      Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : 7 = i
    · rw [← hi, Nat.testBit_lt_two_pow hlt, Bool.false_and]
    · rw [decide_eq_false hi, Bool.and_false]
  exact hs32


/-- `to_bytes` returns the little-endian encoding of the canonical representative of `self`: the 32
bytes, read as a little-endian number, equal `self.asNat % p`. -/
@[step]
theorem to_bytes_spec (self : FieldElement2625) :
    to_bytes self ⦃ (r : Array U8 32#usize) =>
      r.asNat 8 = self.asNat % p ⦄ := by
  rewrite [to_bytes_decomp]
  step*


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625
