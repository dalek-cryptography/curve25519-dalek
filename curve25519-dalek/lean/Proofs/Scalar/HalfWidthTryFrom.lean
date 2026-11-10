/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar52
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
import Subtle
public import Proofs.Helpers.ByteValues
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

/-- An array with digits below `2 ^ bits` is below `2 ^ (bits * m)` iff its digits from `m` on
are zero. -/
private theorem Aeneas.Std.Array.asNat_lt_pow_iff {ty : UScalarTy} {n : Usize} (bits m : ℕ)
    (a : Array (UScalar ty) n) (hmn : m ≤ n.val) (ha : ∀ j < n.val, a[j]!.val < 2 ^ bits) :
    a.asNat bits < 2 ^ (bits * m) ↔ ∀ j, m ≤ j → j < n.val → a[j]!.val = 0 := by
  rw [Array.asNat_eq_sum, ← Finset.sum_range_add_sum_Ico _ hmn]
  constructor
  · intro hlt j hmj hjn
    by_contra hne
    have hle : 2 ^ (bits * j) * a[j]!.val ≤
        ∑ k ∈ Finset.Ico m n.val, 2 ^ (bits * k) * a[k]!.val :=
      Finset.single_le_sum (f := fun k => 2 ^ (bits * k) * a[k]!.val) (fun _ _ => Nat.zero_le _)
        (Finset.mem_Ico.mpr ⟨hmj, hjn⟩)
    have hpow : 2 ^ (bits * m) ≤ 2 ^ (bits * j) * a[j]!.val :=
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hmj)).trans
        (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne))
    exact absurd hlt (Nat.not_lt.mpr (hpow.trans (hle.trans (Nat.le_add_left _ _))))
  · intro hz
    have h0 : ∑ k ∈ Finset.Ico m n.val, 2 ^ (bits * k) * a[k]!.val = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [Finset.mem_Ico] at hk
        rw [hz k hk.1 hk.2, Nat.mul_zero]
    rw [h0, Nat.add_zero]
    exact Nat.sum_pow_mul_lt bits m (fun j => a[j]!.val) fun j hj => ha j (hj.trans_le hmn)

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertTryFromScalarTuple

/-- The iterator checks that every byte in its slice is zero. -/
@[local step]
private theorem try_from_loop_spec (value : Scalar) (iter : core.slice.iter.Iter U8)
    (hi : iter.i ≤ iter.slice.val.length)
    (hz : ∀ j < iter.i, iter.slice.val[j]!.val = 0) :
    try_from_loop iter value.bytes ⦃ (r : core.result.Result HalfWidthScalar Unit) =>
      ((∀ j < iter.slice.val.length, iter.slice.val[j]!.val = 0) → r = .Ok value) ∧
      (¬ (∀ j < iter.slice.val.length, iter.slice.val[j]!.val = 0) → r = .Err ()) ⦄ := by
  unfold try_from_loop
  apply loop.spec_decr_nat (measure := fun it => it.slice.val.length - it.i)
    (inv := fun it => it.slice = iter.slice ∧ it.i ≤ it.slice.val.length ∧
      ∀ j < it.i, it.slice.val[j]!.val = 0)
  · rintro it ⟨hs, hi, hz⟩
    unfold try_from_loop.body core.slice.iter.IteratorSliceIter.next
    split
    · rename_i hnext
      have hlt : it.i < it.slice.val.length := by simpa using hnext
      simp only [bind_ok]
      change (if it.slice[it.i] != 0#u8 then
        ok (ControlFlow.done (core.result.Result.Err ())) else
        ok (ControlFlow.cont { it with i := it.i + 1 })) ⦃ _ ⦄
      by_cases hx : it.slice[it.i] = 0#u8
      · simp only [hx, bne_self_eq_false, Bool.false_eq_true, ite_false, WP.spec_ok]
        refine ⟨⟨hs, by omega, ?_⟩, by omega⟩
        intro j hj
        by_cases heq : j = it.i
        · subst j
          rw [getElem!_pos it.slice.val it.i hlt]
          exact congrArg UScalar.val hx
        · exact hz j (by omega)
      · simp only [bne_iff_ne, ne_eq, hx, not_false_eq_true, ite_true, WP.spec_ok]
        refine ⟨fun hall => absurd ?_ hx, fun _ => trivial⟩
        apply UScalar.eq_of_val_eq
        have h := hall it.i (by simpa only [← hs] using hlt)
        rw [← hs, getElem!_pos it.slice.val it.i hlt] at h
        exact h
    · rename_i hnext
      have hlt : ¬ it.i < it.slice.val.length := by simpa using hnext
      simp only [bind_ok]
      change (ok (ControlFlow.done (core.result.Result.Ok value))) ⦃ _ ⦄
      simp only [WP.spec_ok]
      refine ⟨fun _ => trivial, fun hn => False.elim (hn ?_)⟩
      intro j hj
      rw [← hs] at hj ⊢
      exact hz j (by omega)
  · exact ⟨rfl, hi, hz⟩

@[step]
theorem try_from_spec (value : Scalar) :
    try_from value ⦃ (r : core.result.Result HalfWidthScalar Unit) =>
      (value.asNat < 2 ^ 128 → r = .Ok value) ∧ (2 ^ 128 ≤ value.asNat → r = .Err ()) ⦄ := by
  unfold try_from
  step as ⟨s, hs, hlen⟩
  simp only [core.slice.Slice.iter, bind_ok]
  let iter : core.slice.iter.Iter U8 := { slice := s, i := 0 }
  step with try_from_loop_spec value iter (by simp [iter]) (by simp [iter]) as ⟨r, hok, herr⟩
  have hiff := Array.asNat_lt_pow_iff 8 16 value.bytes (by simp)
    fun j _ => (value.bytes[j]!).hBounds
  have hzero : (∀ j < iter.slice.val.length, iter.slice.val[j]!.val = 0) ↔
      ∀ j : ℕ, 16 ≤ j → j < value.bytes.val.length → value.bytes[j]!.val = 0 := by
    rw [show iter.slice = s from rfl, hs]
    simp only [Array.val_to_slice]
    constructor
    · intro h j hj hjlen
      have := h (j - 16) (by simp only [List.length_drop]; omega)
      simpa [List.getElem!_drop, Nat.add_sub_of_le hj, Array.getElem!_Nat_eq] using this
    · intro h j hj
      simp only [List.length_drop] at hj
      simpa [List.getElem!_drop, Array.getElem!_Nat_eq] using
        h (16 + j) (by omega) (by omega)
  simp only [scalar.Scalar.asNat_def, Array.property] at *
  refine ⟨fun hlt => hok (hzero.mpr (hiff.mp hlt)), fun hge => herr fun hall => ?_⟩
  exact absurd (hiff.mpr (hzero.mp hall)) (Nat.not_lt.mpr hge)

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertTryFromScalarTuple
