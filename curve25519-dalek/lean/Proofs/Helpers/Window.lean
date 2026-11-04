/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Helpers.StepSpecs
public section

/-! # Generic forms of the `window.rs` functions

The five `select` functions of `LookupTable{,Radix32,Radix64,Radix128,Radix256}` differ only in
the array size and three literals (the bounds of the `debug_assert`s and the end of the loop
range), and the `From<&EdwardsPoint>` impls of all tables run the same loop (entry `j + 1` is the
Niels form of `Q + entry j`). This file defines the generic shapes (`select`, `fromLoopBody`),
which the translated functions are definitionally equal to, and proves their specs once, for any
entry type with a `PointRepr` instance. It also gives `PointRepr` instances for `EdwardsPoint` and
`CompletedPoint`, so that the intermediate results of the loops can be described the same way. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP ControlFlow
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek

/-! ### `PointRepr` instances for the intermediate point types -/

noncomputable instance edwards.EdwardsPoint.«x86_64-tables».instPointRepr :
    PointRepr edwards.EdwardsPoint.«x86_64-tables» where
  OnCurve := edwards.EdwardsPoint.«x86_64-tables».OnCurve
  toPoint := edwards.EdwardsPoint.«x86_64-tables».toPoint
  LimbsLt := edwards.EdwardsPoint.«x86_64-tables».LimbsLt

noncomputable instance edwards.EdwardsPoint.«i686-tables».instPointRepr :
    PointRepr edwards.EdwardsPoint.«i686-tables» where
  OnCurve := edwards.EdwardsPoint.«i686-tables».OnCurve
  toPoint := edwards.EdwardsPoint.«i686-tables».toPoint
  LimbsLt := edwards.EdwardsPoint.«i686-tables».LimbsLt

noncomputable instance edwards.EdwardsPoint.«x86_64-no-tables».instPointRepr :
    PointRepr edwards.EdwardsPoint.«x86_64-no-tables» where
  OnCurve := edwards.EdwardsPoint.«x86_64-no-tables».OnCurve
  toPoint := edwards.EdwardsPoint.«x86_64-no-tables».toPoint
  LimbsLt := edwards.EdwardsPoint.«x86_64-no-tables».LimbsLt

noncomputable instance edwards.EdwardsPoint.«i686-no-tables».instPointRepr :
    PointRepr edwards.EdwardsPoint.«i686-no-tables» where
  OnCurve := edwards.EdwardsPoint.«i686-no-tables».OnCurve
  toPoint := edwards.EdwardsPoint.«i686-no-tables».toPoint
  LimbsLt := edwards.EdwardsPoint.«i686-no-tables».LimbsLt

noncomputable instance CompletedPoint.«x86_64-tables».instPointRepr :
    PointRepr CompletedPoint.«x86_64-tables» where
  OnCurve := CompletedPoint.«x86_64-tables».OnCurve
  toPoint := CompletedPoint.«x86_64-tables».toPoint
  LimbsLt := CompletedPoint.«x86_64-tables».LimbsLt

noncomputable instance CompletedPoint.«i686-tables».instPointRepr :
    PointRepr CompletedPoint.«i686-tables» where
  OnCurve := CompletedPoint.«i686-tables».OnCurve
  toPoint := CompletedPoint.«i686-tables».toPoint
  LimbsLt := CompletedPoint.«i686-tables».LimbsLt

noncomputable instance CompletedPoint.«x86_64-no-tables».instPointRepr :
    PointRepr CompletedPoint.«x86_64-no-tables» where
  OnCurve := CompletedPoint.«x86_64-no-tables».OnCurve
  toPoint := CompletedPoint.«x86_64-no-tables».toPoint
  LimbsLt := CompletedPoint.«x86_64-no-tables».LimbsLt

noncomputable instance CompletedPoint.«i686-no-tables».instPointRepr :
    PointRepr CompletedPoint.«i686-no-tables» where
  OnCurve := CompletedPoint.«i686-no-tables».OnCurve
  toPoint := CompletedPoint.«i686-no-tables».toPoint
  LimbsLt := CompletedPoint.«i686-no-tables».LimbsLt

namespace window

open PointRepr

/-! ### Bit operations of `select` -/

private theorem bmod_two_pow_sub (w t : ℕ) (hw : 0 < w) (ht : t < 2 ^ w) :
    Int.bmod ((2 : ℤ) ^ w - 1 - t) (2 ^ w) = -Int.bmod t (2 ^ w) - 1 := by
  obtain ⟨n, hn, hn'⟩ : ∃ n : ℕ, 2 ^ w = 2 * n ∧ 0 < n :=
    ⟨2 ^ (w - 1), by rw [← pow_succ', Nat.sub_add_cancel hw], by positivity⟩
  have hz : (2 : ℤ) ^ w = 2 * (n : ℤ) := by exact_mod_cast hn
  rw [hn] at ht
  rw [hz, hn]
  rw [Int.bmod_def, Int.bmod_def, Int.emod_eq_of_lt (by omega) (by push_cast; omega),
    Int.emod_eq_of_lt (by omega) (by push_cast; omega)]
  push_cast
  split_ifs <;> omega

private theorem val_xor_of_val_eq_zero {ty : IScalarTy} (a b : IScalar ty) (hb : b.val = 0) :
    (a ^^^ b).val = a.val := by
  have hb' : b.bv = 0#_ :=
    BitVec.eq_of_toInt_eq (by rw [IScalar.bv_toInt_eq, hb, BitVec.toInt_zero])
  change (a.bv ^^^ b.bv).toInt = a.bv.toInt
  rw [hb', BitVec.xor_zero]

private theorem val_xor_of_val_eq_neg_one {ty : IScalarTy} (a b : IScalar ty)
    (hb : b.val = -1) : (a ^^^ b).val = -a.val - 1 := by
  have h0 : 0 < ty.numBits := Nat.pos_of_ne_zero (IScalarTy.numBits_nonzero ty)
  have hb' : b.bv = BitVec.allOnes _ :=
    BitVec.eq_of_toInt_eq (by rw [IScalar.bv_toInt_eq, hb, BitVec.toInt_allOnes, ite_eq_left h0])
  change (a.bv ^^^ b.bv).toInt = -a.bv.toInt - 1
  rw [hb', BitVec.xor_allOnes, BitVec.toInt_not, BitVec.toInt_eq_toNat_bmod]
  exact bmod_two_pow_sub _ _ h0 a.bv.isLt

private theorem val_and_of_val_eq_neg_one {ty : IScalarTy} (b c : IScalar ty)
    (hb : b.val = -1) : (b &&& c).val = c.val := by
  have h0 : 0 < ty.numBits := Nat.pos_of_ne_zero (IScalarTy.numBits_nonzero ty)
  have hb' : b.bv = BitVec.allOnes _ :=
    BitVec.eq_of_toInt_eq (by rw [IScalar.bv_toInt_eq, hb, BitVec.toInt_allOnes, ite_eq_left h0])
  change (b.bv &&& c.bv).toInt = c.bv.toInt
  rw [hb', BitVec.allOnes_and]

private theorem val_and_of_val_eq_zero {ty : IScalarTy} (b c : IScalar ty) (hb : b.val = 0) :
    (b &&& c).val = 0 := by
  have hb' : b.bv = 0#_ :=
    BitVec.eq_of_toInt_eq (by rw [IScalar.bv_toInt_eq, hb, BitVec.toInt_zero])
  change (b.bv &&& c.bv).toInt = 0
  rw [hb', BitVec.zero_and, BitVec.toInt_zero]

/-! ### `select` -/

/-- The loop body of `LookupTable*::select`: `t := self[j - 1]` if `j = xabs`. -/
@[expose] def selectLoopBody {T : Type} {N : Usize} (selInst : subtle.ConditionallySelectable T)
    (xabs : I16) (iter : core.ops.range.Range Usize) (self : Array T N) (t : T) :
    Result (ControlFlow ((core.ops.range.Range Usize) × (Array T N) × T) T) := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done t)
  | some j =>
    let i ← lift (IScalar.hcast .U16 xabs)
    let i1 ← lift (UScalar.cast .U16 j)
    let c ← U16.Insts.SubtleConstantTimeEq.ct_eq i i1
    let i2 ← j - 1#usize
    let t1 ← Array.index_usize self i2
    let t2 ← selInst.conditional_assign t t1 c
    ok (cont (iter1, self, t2))

/-- The loop of `LookupTable*::select`. -/
@[expose] def selectLoop {T : Type} {N : Usize} (selInst : subtle.ConditionallySelectable T)
    (iter : core.ops.range.Range Usize) (self : Array T N) (xabs : I16) (t : T) : Result T :=
  loop (fun (iter1, self1, t1) => selectLoopBody selInst xabs iter1 self1 t1) (iter, self, t)

/-- `LookupTable*::select`, with the bounds `lo`, `hi` of its `debug_assert`s and the end `e` of
its loop range as parameters. -/
@[expose] def select {T : Type} {N : Usize} (lo : I8) (hi : I16) (e : Usize)
    (identityInst : traits.Identity T) (selInst : subtle.ConditionallySelectable T)
    (negInst : subtle.ConditionallyNegatable T) (self : Array T N) (x : I8) : Result T := do
  massert (x >= lo)
  let i ← lift (IScalar.cast .I16 x)
  massert (i <= hi)
  let i1 ← lift (IScalar.cast .I16 x)
  let xmask ← i1 >>> 7#i32
  let i2 ← lift (IScalar.cast .I16 x)
  let i3 ← i2 + xmask
  let xabs ← lift (i3 ^^^ xmask)
  let t ← identityInst.identity
  let t1 ← selectLoop selInst { start := 1#usize, «end» := e } self xabs t
  let i4 ← lift (xmask &&& 1#i16)
  let i5 ← lift (IScalar.hcast .U8 i4)
  let neg_mask ← subtle.Choice.Insts.CoreConvertFromU8.from i5
  negInst.conditional_negate t1 neg_mask

variable {T : Type} [Inhabited T] [PointRepr T] {n : ℕ}

/-- The loop of `select`: after the loop, `t` represents `n • P` (`n = |x| ≤ N`), the entry
`n - 1` if `n > 0` and the identity if `n = 0`. -/
theorem selectLoop_spec {N : Usize} (selInst : subtle.ConditionallySelectable T)
    (hsel : ∀ a b (c : subtle.Choice), c.IsValid →
      selInst.conditional_assign a b c ⦃ (r : T) => (c = 0#u8 → r = a) ∧ (c = 1#u8 → r = b) ⦄)
    (self : Array T N) (P : curve25519.edwards.Point)
    (hself : ∀ j < N.val, LimbsLt n self[j]!)
    (hP : ∀ j < N.val, OnCurve self[j]! ∧ toPoint self[j]! = (j + 1) • P)
    (e : Usize) (he : e.val = N.val + 1) (hN : N.val ≤ 128) (xabs : I16)
    (hxabs : 0 ≤ xabs.val ∧ xabs.val ≤ N.val) (t : T)
    (ht : OnCurve t ∧ toPoint t = 0 ∧ LimbsLt n t) :
    selectLoop selInst { start := 1#usize, «end» := e } self xabs t ⦃ (r : T) =>
      OnCurve r ∧ toPoint r = xabs.val.toNat • P ∧ LimbsLt n r ⦄ := by
  unfold selectLoop
  apply loop.spec_decr_nat (measure := fun (it, _, _) => it.end.val - it.start.val)
    (inv := fun (it, s, t') => s = self ∧ it.end = e ∧ 1 ≤ it.start.val ∧
      it.start.val ≤ e.val ∧ OnCurve t' ∧ LimbsLt n t' ∧
      toPoint t' = (if xabs.val.toNat < it.start.val then xabs.val.toNat else 0) • P)
  · rintro ⟨it, s, t'⟩ ⟨rfl, hend, hstart, hle, hon', hb', hpt'⟩
    unfold selectLoopBody
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨o, it1, ho, hstart1, hend1⟩
      subst ho
      step with IScalar.hcast_inBounds_spec as ⟨i, hi⟩
      step with UScalar.cast_inBounds_spec as ⟨i1, hi1⟩
      step as ⟨c, hcv, hc⟩
      step as ⟨i2, hi2⟩
      step with Array.index_usize_getElem!_spec as ⟨t1, ht1⟩
      step with hsel as ⟨t2, ht2a, ht2b⟩
      rw [hend] at hlt
      have hj : it.start.val - 1 < N.val := by scalar_tac
      have hm : it1.end.val - it1.start.val < it.end.val - it.start.val := by
        rw [hend1, hend]; scalar_tac
      by_cases hn : xabs.val.toNat = it.start.val
      · have hc1 : c = 1#u8 := by
          rw [hc, ite_eq_left ((UScalar.eq_equiv i i1).mpr (by scalar_tac))]
        rw [ht2b hc1, ht1, hi2]
        obtain ⟨hon1, hpt1⟩ := hP _ hj
        refine ⟨hend1.trans hend, by scalar_tac, by scalar_tac, hon1, hself _ hj, ?_, hm⟩
        rw [hpt1, ite_eq_left (by scalar_tac), hn, Nat.sub_add_cancel hstart]
      · have hc0 : c = 0#u8 := by
          rw [hc, ite_eq_right fun h => hn (by have := (UScalar.eq_equiv i i1).mp h; scalar_tac)]
        rw [ht2a hc0]
        refine ⟨hend1.trans hend, by scalar_tac, by scalar_tac, hon', hb', ?_, hm⟩
        rw [hpt', hstart1]
        by_cases hlt' : xabs.val.toNat < it.start.val
        · rw [ite_eq_left hlt', ite_eq_left (by omega)]
        · rw [ite_eq_right hlt', ite_eq_right (by omega)]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have : xabs.val.toNat < it.start.val := by scalar_tac
      rw [ite_eq_left this] at hpt'
      exact ⟨hon', hpt', hb'⟩
  · refine ⟨rfl, rfl, le_refl _, by scalar_tac, ht.1, ht.2.2, ?_⟩
    rw [ht.2.1]
    split_ifs with h
    · rw [show xabs.val.toNat = 0 by simp at h; omega, zero_smul]
    · rw [zero_smul]

/-- `LookupTable*::select`: for `-N ≤ x ≤ N`, the entry `|x| - 1` (the identity for `x = 0`),
negated if `x < 0`, i.e. a representative of `x • P`. -/
theorem select_spec {N : Usize} (lo : I8) (hi : I16) (e : Usize) (hlo : lo.val = -(N.val : ℤ))
    (hhi : hi.val = N.val) (he : e.val = N.val + 1) (hN : N.val ≤ 128)
    (identityInst : traits.Identity T) (selInst : subtle.ConditionallySelectable T)
    (negInst : core.ops.arith.Neg T T)
    (hid : identityInst.identity ⦃ (r : T) => OnCurve r ∧ toPoint r = 0 ∧ LimbsLt n r ⦄)
    (hsel : ∀ a b (c : subtle.Choice), c.IsValid →
      selInst.conditional_assign a b c ⦃ (r : T) => (c = 0#u8 → r = a) ∧ (c = 1#u8 → r = b) ⦄)
    (hneg : ∀ a, LimbsLt n a → OnCurve a →
      negInst.neg a ⦃ (r : T) => OnCurve r ∧ toPoint r = -toPoint a ∧ LimbsLt n r ⦄)
    (self : Array T N) (P : curve25519.edwards.Point)
    (hself : ∀ j < N.val, LimbsLt n self[j]!)
    (hP : ∀ j < N.val, OnCurve self[j]! ∧ toPoint self[j]! = (j + 1) • P)
    (x : I8) (hx : -(N.val : ℤ) ≤ x.val ∧ x.val ≤ N.val) :
    select lo hi e identityInst selInst (subtle.ConditionallyNegatable.Blanket selInst negInst)
      self x ⦃ (r : T) => OnCurve r ∧ toPoint r = x.val • P ∧ LimbsLt n r ⦄ := by
  unfold select
  step
  step as ⟨i, hi'⟩
  step
  step as ⟨i1, hi1⟩
  step as ⟨xmask, hxmask, _⟩
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  step as ⟨xabs, hxabs, _⟩
  have hcast : ∀ y : I16, y = IScalar.cast .I16 x → y.val = x.val := fun y hy => by
    rw [hy]; exact IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have hx8 : -128 ≤ x.val ∧ x.val ≤ 127 := ⟨by scalar_tac, by scalar_tac⟩
  rw [hcast i1 hi1, Int.shiftRight_eq_div_pow] at hxmask
  rw [hcast i2 hi2] at hi3
  have hm : (x.val < 0 ∧ xmask.val = -1 ∧ xabs.val = -x.val) ∨
      (0 ≤ x.val ∧ xmask.val = 0 ∧ xabs.val = x.val) := by
    rcases lt_or_ge x.val 0 with hneg' | hpos
    · have h1 : xmask.val = -1 := by rw [hxmask]; omega
      refine Or.inl ⟨hneg', h1, ?_⟩
      rw [hxabs, val_xor_of_val_eq_neg_one _ _ h1, hi3, h1]
      ring
    · have h0 : xmask.val = 0 := by rw [hxmask]; omega
      exact Or.inr ⟨hpos, h0, by rw [hxabs, val_xor_of_val_eq_zero _ _ h0, hi3, h0, add_zero]⟩
  have hxabs' : 0 ≤ xabs.val ∧ xabs.val ≤ N.val := by omega
  step with hid as ⟨t, hton, htp, htb⟩
  step with selectLoop_spec selInst hsel self P hself hP e he hN xabs hxabs' t ⟨hton, htp, htb⟩
    as ⟨t1, ht1on, ht1p, ht1b⟩
  step as ⟨i4, hi4, _⟩
  have hi4' : i4.val = if x.val < 0 then 1 else 0 := by
    rcases hm with ⟨hlt, h1, _⟩ | ⟨hge, h0, _⟩
    · rw [hi4, val_and_of_val_eq_neg_one _ _ h1, ite_eq_left hlt]; rfl
    · rw [hi4, val_and_of_val_eq_zero _ _ h0, ite_eq_right (not_lt.mpr hge)]
  have hi4b : 0 ≤ i4.val ∧ i4.val ≤ UScalar.max .U8 := by
    rw [hi4']; split_ifs <;> exact ⟨by norm_num, by scalar_tac⟩
  step with IScalar.hcast_inBounds_spec .U8 i4 hi4b as ⟨i5, hi5⟩
  have hi5' : i5 = 0#u8 ∨ i5 = 1#u8 := by
    split_ifs at hi4' with hlt
    · exact Or.inr ((UScalar.eq_equiv i5 1#u8).mpr (by
        rw [hi4'] at hi5; rw [show (1#u8).val = 1 from rfl]; omega))
    · exact Or.inl ((UScalar.eq_equiv i5 0#u8).mpr (by
        rw [hi4'] at hi5; rw [show (0#u8).val = 0 from rfl]; omega))
  step with subtle.Choice.Insts.CoreConvertFromU8.from_spec i5 hi5' as ⟨neg_mask, hnmv, hnm⟩
  unfold subtle.ConditionallyNegatable.Blanket.conditional_negate
  step with hneg as ⟨n, hnon, hnp, hnb⟩
  step with hsel as ⟨r, hr0, hr1⟩
  rcases hm with ⟨hlt, _, hxa⟩ | ⟨hge, _, hxa⟩
  · have h1 : neg_mask = 1#u8 := by
      rw [hnm]; rw [ite_eq_left hlt] at hi4'
      exact (UScalar.eq_equiv i5 1#u8).mpr (by
        rw [hi4'] at hi5; rw [show (1#u8).val = 1 from rfl]; omega)
    rw [hr1 h1]
    refine ⟨hnon, ?_, hnb⟩
    rw [hnp, ht1p, hxa, ← natCast_zsmul, Int.toNat_of_nonneg (by omega), ← neg_zsmul, neg_neg]
  · have h0 : neg_mask = 0#u8 := by
      rw [hnm]; rw [ite_eq_right (not_lt.mpr hge)] at hi4'
      exact (UScalar.eq_equiv i5 0#u8).mpr (by
        rw [hi4'] at hi5; rw [show (0#u8).val = 0 from rfl]; omega)
    rw [hr0 h0]
    refine ⟨ht1on, ?_, ht1b⟩
    rw [ht1p, hxa, ← natCast_zsmul, Int.toNat_of_nonneg hge]

/-! ### The loops of the `From<&EdwardsPoint>` impls -/

/-- The loop body of the `From<&EdwardsPoint>` impls: entry `j + 1` is
`asNiels (asExt (add (entry j)))`, where `add` adds a fixed point `Q`. -/
@[expose] def fromLoopBody {C E : Type} {N : Usize} (add : T → Result C) (asExt : C → Result E)
    (asNiels : E → Result T) (iter : core.ops.range.Range Usize) (points : Array T N) :
    Result (ControlFlow ((core.ops.range.Range Usize) × (Array T N)) (Array T N)) := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done points)
  | some j =>
    let pnp ← Array.index_usize points j
    let cp ← add pnp
    let ep ← asExt cp
    let pnp1 ← asNiels ep
    let i ← j + 1#usize
    let a ← Array.update points i pnp1
    ok (cont (iter1, a))

open scoped Helpers.IndexStep Helpers.UpdateStep in
/-- The loop of the `From<&EdwardsPoint>` impls over `0..N-1`: entry `k` represents
`entry 0 + k • Q`. The bounds `BC`, `BE` of the intermediate completed and extended points are
those of the specs passed in. -/
theorem fromLoop_spec {C E : Type} [PointRepr C] [PointRepr E] {BC : C → Prop} {BE : E → Prop}
    {N : Usize}
    (add : T → Result C) (asExt : C → Result E) (asNiels : E → Result T)
    (Q : curve25519.edwards.Point)
    (hadd : ∀ q, LimbsLt n q → OnCurve q →
      add q ⦃ (c : C) => OnCurve c ∧ toPoint c = Q + toPoint q ∧ BC c ⦄)
    (hext : ∀ c : C, BC c → OnCurve c →
      asExt c ⦃ (e : E) => OnCurve e ∧ toPoint e = toPoint c ∧ BE e ⦄)
    (hniels : ∀ e : E, BE e → OnCurve e →
      asNiels e ⦃ (r : T) => OnCurve r ∧ toPoint r = toPoint e ∧ LimbsLt n r ⦄)
    (iter : core.ops.range.Range Usize) (hstart : iter.start.val = 0)
    (hend : iter.end.val + 1 = N.val) (points : Array T N)
    (h0 : OnCurve points[0]! ∧ LimbsLt n points[0]!) :
    loop (fun (iter1, points1) => fromLoopBody add asExt asNiels iter1 points1) (iter, points)
      ⦃ (r : Array T N) => ∀ k < N.val,
        OnCurve r[k]! ∧ toPoint r[k]! = toPoint points[0]! + k • Q ∧ LimbsLt n r[k]! ⦄ := by
  apply loop.spec_decr_nat (measure := fun (it, _) => it.end.val - it.start.val)
    (inv := fun (it, pts) => it.end = iter.end ∧ it.start.val ≤ it.end.val ∧
      ∀ k ≤ it.start.val,
        OnCurve pts[k]! ∧ toPoint pts[k]! = toPoint points[0]! + k • Q ∧ LimbsLt n pts[k]!)
  · rintro ⟨it, pts⟩ ⟨hend', hle, hinv⟩
    unfold fromLoopBody
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨o, it1, ho, hstart1, hend1⟩
      subst ho
      obtain ⟨hon, hpt, hb⟩ := hinv _ (le_refl _)
      step as ⟨pnp, hpnp⟩
      subst hpnp
      step with hadd _ hb hon as ⟨cp, hcpon, hcp, hcpb⟩
      step with hext cp hcpb hcpon as ⟨ep, hepon, hep, hepb⟩
      step with hniels ep hepb hepon as ⟨pnp1, hpon, hp, hpb⟩
      step as ⟨i, hi⟩
      step as ⟨a, ha, ha'⟩
      refine ⟨hend1.trans hend', by scalar_tac, fun k hk => ?_, by rw [hend1]; scalar_tac⟩
      rcases Nat.lt_or_ge k (it.start.val + 1) with hk' | hk'
      · rw [ha' k (by scalar_tac)]
        exact hinv k (by omega)
      · have hk1 : k = i.val := by scalar_tac
        subst hk1
        rw [ha]
        refine ⟨hpon, ?_, hpb⟩
        rw [hp, hep, hcp, hpt, hi, add_smul, one_smul]
        abel
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      intro k hk
      exact hinv k (by scalar_tac)
  · refine ⟨rfl, by scalar_tac, fun k hk => ?_⟩
    have hk0 : k = 0 := by scalar_tac
    subst hk0
    exact ⟨h0.1, by rw [zero_smul, add_zero], h0.2⟩

end window

end Curve25519Dalek
