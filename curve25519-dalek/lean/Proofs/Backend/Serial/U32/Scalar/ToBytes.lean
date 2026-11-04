/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar29
public import Curve25519.Basic
import Proofs.Helpers.AsNat
import Proofs.Helpers.Scalar29
import Proofs.Helpers.Array
public section

/-! # `Scalar29::to_bytes`

The 32 bytes are written one at a time, each the low byte of a limb shifted right, or of the
remaining bits of a limb joined with the low bits of the next one. The invariant (`byte_step`,
`byte_join_step`) is that the bytes written so far plus the bits of the current limb still
pending add up to the limbs consumed so far. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 Finset
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29)

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

set_option linter.hashCommand false in
#decompose to_bytes to_bytes_decomp
  letRange 1 58 => bytesLow
  letRange 2 61 => bytesHigh

/-- Bytes 0 to 14 of `to_bytes` (limbs 0 to 3 and the low 4 bits of limb 4). -/
add_decl_doc bytesLow

/-- Bytes 15 to 31 of `to_bytes` (the rest of limb 4 and limbs 5 to 8). -/
add_decl_doc bytesHigh

/-- Writing byte `n` of `s` as the low byte of `x >>> r`: the bytes written so far plus the bits
of `x` still pending add up to `V`, with one more byte written and 8 fewer bits pending. -/
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

/-- The low byte of the remaining `t` bits of `a` joined with `w` shifted by `t` (in `u32`, so
the shift may wrap) is the low byte of their sum. -/
private theorem low_byte_join {a w t : Nat} (ha : a < 2 ^ t) :
    (a ||| w <<< t % U32.size) % 2 ^ 8 = (a + w * 2 ^ t) % 2 ^ 8 := by
  have hsize : U32.size = 2 ^ 32 := by simp [U32.size, U32.numBits]
  rw [Nat.or_mod_two_pow, hsize, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num)),
    ← Nat.or_mod_two_pow, Nat.shiftLeft_eq, Nat.or_comm, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt ha, Nat.add_comm, Nat.mul_comm]

/-- Writing byte `n` of `s` as the low byte of `(x >>> r) ||| (w <<< t)`, where `x` is limb `l`
of `h` and `w` is limb `l + 1`: the last `t` bits of `x` and the low bits of `w` are joined, so
the invariant of `byte_step` moves on to limb `l + 1`. The hypotheses are the postconditions of
the update, the cast, the `|||`, the left shift, the read of `w`, the shift and the read of `x`,
in this order. -/
private theorem byte_join_step {h : Scalar29} {s s' : Std.Array U8 32#usize} {k : Usize}
    {l n r t : Nat} {x y w z o : U32} {b : U8}
    {hl : l < (↑h : List U32).length} {hl' : l + 1 < (↑h : List U32).length}
    (hbound : h.LimbsLt 29)
    (hI : ∑ i ∈ range n, 2 ^ (8 * i) * (s[i]!).val + 2 ^ (8 * n) * (x.val >>> r) =
      ∑ i ∈ range (l + 1), 2 ^ (29 * i) * (h[i]!).val)
    (hs : s' = s.set k b) (hb : b = UScalar.cast .U8 o) (ho : o.val = (y ||| z).val)
    (hz : z.val = w.val <<< t % U32.size) (hw : w = (↑h : List U32)[l + 1])
    (hy : y.val = x.val >>> r) (hx : x = (↑h : List U32)[l])
    (hnum : k.val = n ∧ n < 32 ∧ r + t = 29 ∧ 8 * n + t = 29 * (l + 1) ∧ t ≤ 8 ∧ l + 1 < 9 := by
      decide) :
    ∑ i ∈ range (n + 1), 2 ^ (8 * i) * (s'[i]!).val + 2 ^ (8 * (n + 1)) * (w.val >>> (8 - t)) =
      ∑ i ∈ range (l + 1 + 1), 2 ^ (29 * i) * (h[i]!).val := by
  obtain ⟨hk, hn, hrt, he, ht, hl9⟩ := hnum
  subst hs
  rw [Array.getElem_val_eq_getElem! _ _ hl] at hx
  rw [Array.getElem_val_eq_getElem! _ _ hl'] at hw
  --The bits of `x` left after the shift fit below the join
  have hxb : x.val >>> r < 2 ^ t := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos r), ← Nat.pow_add,
      Nat.add_comm, hrt, hx]
    exact hbound l (by omega)
  --The byte written
  have hbyte : b.val = (x.val >>> r + w.val * 2 ^ t) % 2 ^ 8 := by
    rw [hb, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, ho, UScalar.val_or, hy, hz,
      low_byte_join hxb]
  --The new pending bits of `w` are the high bits of the joined value
  have hdiv : (x.val >>> r + w.val * 2 ^ t) / 2 ^ 8 = w.val >>> (8 - t) := by
    have h8 : 2 ^ 8 = 2 ^ t * 2 ^ (8 - t) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' ht]
    rw [h8, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos t),
      Nat.div_eq_of_lt hxb, Nat.zero_add, Nat.shiftRight_eq_div_pow]
  rw [sum_range_succ, sum_congr rfl (fun i hi => by
      rw [Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hk]; exact Nat.ne_of_gt (mem_range.mp hi))]),
    Array.getElem!_Nat_set_eq _ _ _ _ ⟨hk, by
      simp only [Std.Array.length, Array.length_eq]; exact hn⟩,
    hbyte, ← hdiv, Nat.mul_succ, Nat.pow_add, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add,
    Nat.mod_add_div, sum_range_succ _ (l + 1), ← hI, Nat.mul_add, ← Nat.add_assoc,
    Nat.add_left_cancel_iff, ← he, Nat.pow_add, hw, Nat.mul_comm _ (2 ^ t), Nat.mul_assoc]

/-- A top limb of weight `2 ^ 232` in a number below `2 ^ 256` has at most 24 bits. -/
private theorem top_limb_lt {r x : ℕ} (h : r + 2 ^ 232 * x < 2 ^ 256) : x < 2 ^ 24 := by
  omega

/-- Bytes 0 to 14: limbs 0 to 3, and limb 4 pending above its low 4 bits. -/
private theorem bytesLow_spec (self : Scalar29) (hself : self.LimbsLt 29)
    (s : Std.Array U8 32#usize) :
    bytesLow self s ⦃ (x4 : U32) (s15 : Std.Array U8 32#usize) =>
      x4 = self[4]! ∧
      ∑ i ∈ range 15, 2 ^ (8 * i) * (s15[i]!).val + 2 ^ (8 * 15) * (x4.val >>> 4) =
        ∑ i ∈ range 5, 2 ^ (29 * i) * (self[i]!).val ⦄ := by
  unfold bytesLow
  step* -assumTac
  have hI0 : ∀ {x : U32} {h0 : 0 < (↑self : List U32).length}, x = (↑self : List U32)[0]'h0 →
      ∑ i ∈ range 0, 2 ^ (8 * i) * (s[i]!).val + 2 ^ (8 * 0) * (x.val >>> 0) =
        ∑ i ∈ range (0 + 1), 2 ^ (29 * i) * (self[i]!).val :=
    fun hx => by
      rw [hx, Array.getElem_val_eq_getElem!]
      simp only [range_zero, sum_empty, sum_range_one, Nat.mul_zero, Nat.pow_zero,
        Nat.shiftRight_zero, Nat.zero_add, Nat.one_mul]
  have hI := byte_step (hI0 ‹_›) ‹_› ‹_› ‹_›
  clear hI0
  iterate 2
    replace hI := byte_step hI ‹_› ‹_› ‹_›
  replace hI := byte_join_step hself hI ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  iterate 3
    replace hI := byte_step hI ‹_› ‹_› ‹_›
  replace hI := byte_join_step hself hI ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  iterate 2
    replace hI := byte_step hI ‹_› ‹_› ‹_›
  replace hI := byte_join_step hself hI ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  iterate 3
    replace hI := byte_step hI ‹_› ‹_› ‹_›
  replace hI := byte_join_step hself hI ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  exact ⟨(‹_ = (↑self : List U32)[4]›).trans (Array.getElem_val_eq_getElem! _ _ _), hI⟩

/-- Bytes 15 to 31: the rest of limb 4 and limbs 5 to 8. -/
private theorem bytesHigh_spec (self : Scalar29) (hself : self.LimbsLt 29)
    (h8 : self[8]!.val < 2 ^ 24) (x4 : U32) (hx : x4 = self[4]!) (s15 : Std.Array U8 32#usize)
    (hI15 : ∑ i ∈ range 15, 2 ^ (8 * i) * (s15[i]!).val + 2 ^ (8 * 15) * (x4.val >>> 4) =
      ∑ i ∈ range 5, 2 ^ (29 * i) * (self[i]!).val) :
    bytesHigh self x4 s15 ⦃ (r : Array U8 32#usize) => r.asNat 8 = self.asNat ⦄ := by
  have hx4 : x4 = (↑self : List U32)[4]'(by simp) := by rw [hx, Array.getElem_val_eq_getElem!]
  clear hx
  unfold bytesHigh
  step* -assumTac
  have hI := hI15
  clear hI15
  iterate 3
    replace hI := byte_step hI ‹_› ‹_› ‹_›
  replace hI := byte_join_step hself hI ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  iterate 2
    replace hI := byte_step hI ‹_› ‹_› ‹_›
  replace hI := byte_join_step hself hI ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  iterate 3
    replace hI := byte_step hI ‹_› ‹_› ‹_›
  replace hI := byte_join_step hself hI ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  iterate 3
    replace hI := byte_step hI ‹_› ‹_› ‹_›
  --Limb 7 is used up exactly at bit 232, limb 8 pending in full
  have hswitch : ∀ {s : Std.Array U8 32#usize} {x x' : U32} {h7 : 7 < (↑self : List U32).length}
      {h8' : 8 < (↑self : List U32).length}, x = (↑self : List U32)[7]'h7 →
      x' = (↑self : List U32)[8]'h8' →
      ∑ i ∈ range 29, 2 ^ (8 * i) * (s[i]!).val + 2 ^ (8 * 29) * (x.val >>> 29) =
        ∑ i ∈ range 8, 2 ^ (29 * i) * (self[i]!).val →
      ∑ i ∈ range 29, 2 ^ (8 * i) * (s[i]!).val + 2 ^ (8 * 29) * (x'.val >>> 0) =
        ∑ i ∈ range 9, 2 ^ (29 * i) * (self[i]!).val := fun hx hx' hI => by
    rw [hx, Array.getElem_val_eq_getElem!, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (by apply hself 7 (by decide)), Nat.mul_zero, Nat.add_zero] at hI
    rw [hx', Array.getElem_val_eq_getElem!, Nat.shiftRight_zero, sum_range_succ _ 8, ← hI]
  replace hI := byte_step (hswitch ‹_› ‹_› hI) ‹_› ‹_› ‹_›
  clear hswitch
  iterate 2
    replace hI := byte_step hI ‹_› ‹_› ‹_›
  --Limb 8 is used up
  have hend : ∀ {s : Std.Array U8 32#usize} {x : U32} {h8' : 8 < (↑self : List U32).length},
      x = (↑self : List U32)[8]'h8' →
      ∑ i ∈ range 32, 2 ^ (8 * i) * (s[i]!).val + 2 ^ (8 * 32) * (x.val >>> 24) =
        ∑ i ∈ range 9, 2 ^ (29 * i) * (self[i]!).val → s.asNat 8 = self.asNat :=
    fun hx hI => by
      rw [hx, Array.getElem_val_eq_getElem!, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h8,
        Nat.mul_zero, Nat.add_zero] at hI
      rw [Array.asNat_eq_sum, UScalar.ofNatCore_val_eq, Scalar29.asNat_def, Array.asNat_eq_sum,
        UScalar.ofNatCore_val_eq]
      exact hI
  exact hend ‹_› hI

@[step]
theorem to_bytes_spec (self : Scalar29) (hself : self.LimbsLt 29)
    (hself' : self.asNat < 2 ^ 256) :
    to_bytes self ⦃ (r : Array U8 32#usize) =>
      r.asNat 8 = self.asNat ⦄ := by
  have h8 : self[8]!.val < 2 ^ 24 :=
    top_limb_lt (by rw [Scalar29.asNat_eq] at hself'; exact hself')
  rw [to_bytes_decomp]
  dsimp only
  step with bytesLow_spec self hself as ⟨x4, s15, hx, hI⟩
  exact bytesHigh_spec self hself h8 x4 hx s15 hI

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29
