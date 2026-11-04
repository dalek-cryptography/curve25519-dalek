/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Edwards.Encoding
public import Defs.Edwards
public import Proofs.Field.InvertBatchAlloc
import Proofs.Edwards.Affine.Compress
import Proofs.Helpers.Coords
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Vec
public section

/-! # `EdwardsPoint::compress_batch_alloc`

As `compress_batch`, on a slice: the `Z` coordinates are inverted in one batch
(`invert_batch_alloc`), then each point is compressed as the affine point `(X Z⁻¹, Y Z⁻¹)`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.Backend

variable (B : Backend)

open ControlFlow

/-- `compress_batch_alloc_loop0.body` over a backend: the coordinate `Z` of a point by `Zf`. -/
@[expose] def cbaLoop0Body {E : Type} (Zf : E → B.F) (iter : core.slice.iter.Iter E)
    (zs : alloc.vec.Vec B.F) :
    Result (ControlFlow ((core.slice.iter.Iter E) × (alloc.vec.Vec B.F))
      (alloc.vec.Vec B.F)) := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done zs)
  | some input =>
    let zs1 ← alloc.vec.Vec.push zs (Zf input)
    ok (cont (iter1, zs1))

/-- `compress_batch_alloc_loop0` over a backend. -/
@[expose] def cbaLoop0 {E : Type} (Zf : E → B.F) (iter : core.slice.iter.Iter E)
    (zs : alloc.vec.Vec B.F) : Result (alloc.vec.Vec B.F) := do
  loop (fun (iter1, zs1) => B.cbaLoop0Body Zf iter1 zs1) (iter, zs)

/-- `compress_batch_alloc_loop1.body` over a backend: `compress x y` is
`AffinePoint::compress` of `(x, y)`. -/
@[expose] def cbaLoop1Body {E : Type} (Xf Yf : E → B.F)
    (compress : B.F → B.F → Result edwards.CompressedEdwardsY) (inputs : Slice E)
    (zs : alloc.vec.Vec B.F) (iter : core.ops.range.Range Usize)
    (out : alloc.vec.Vec edwards.CompressedEdwardsY) :
    Result (ControlFlow ((core.ops.range.Range Usize) ×
      (alloc.vec.Vec edwards.CompressedEdwardsY)) (alloc.vec.Vec edwards.CompressedEdwardsY)) := do
  let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done out)
  | some i =>
    let ep ← Slice.index_usize inputs i
    let fe ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice B.F) zs i
    let x ← B.mul (Xf ep) fe
    let y ← B.mul (Yf ep) fe
    let cey ← compress x y
    let out1 ← alloc.vec.Vec.push out cey
    ok (cont (iter1, out1))

/-- `compress_batch_alloc_loop1` over a backend. -/
@[expose] def cbaLoop1 {E : Type} (Xf Yf : E → B.F)
    (compress : B.F → B.F → Result edwards.CompressedEdwardsY)
    (iter : core.ops.range.Range Usize) (inputs : Slice E)
    (zs : alloc.vec.Vec B.F) (out : alloc.vec.Vec edwards.CompressedEdwardsY) :
    Result (alloc.vec.Vec edwards.CompressedEdwardsY) := do
  loop (fun (iter1, out1) => B.cbaLoop1Body Xf Yf compress inputs zs iter1 out1) (iter, out)

/-- `EdwardsPoint::compress_batch_alloc` over a backend. -/
@[expose] def compressBatchAlloc {E : Type} (Xf Yf Zf : E → B.F)
    (compress : B.F → B.F → Result edwards.CompressedEdwardsY) (inputs : Slice E) :
    Result (alloc.vec.Vec edwards.CompressedEdwardsY) := do
  let n := Slice.len inputs
  let zs := alloc.vec.Vec.with_capacity B.F n
  let iter ← SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter inputs
  let zs1 ← B.cbaLoop0 Zf iter zs
  let (s, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut zs1)
  let s1 ← B.invertBatchAlloc s
  let n1 := Slice.len inputs
  let out := alloc.vec.Vec.with_capacity edwards.CompressedEdwardsY n1
  let n2 := Slice.len inputs
  let zs2 := deref_mut_back s1
  B.cbaLoop1 Xf Yf compress { start := 0#usize, «end» := n2 } inputs zs2 out

/-- The first loop collects the `Z` coordinates of the iterator's slice. -/
private theorem cbaLoop0_spec {E : Type} [Inhabited E] (Zf : E → B.F)
    (iter : core.slice.iter.Iter E) (zs : alloc.vec.Vec B.F)
    (hi : iter.i ≤ iter.slice.length) (hlen : zs.length = iter.i)
    (hzs : ∀ k < iter.i, zs[k]! = Zf iter.slice[k]!) :
    B.cbaLoop0 Zf iter zs ⦃ (r : alloc.vec.Vec B.F) =>
      r.length = iter.slice.length ∧ ∀ k < iter.slice.length, r[k]! = Zf iter.slice[k]! ⦄ := by
  unfold cbaLoop0
  apply loop.spec_decr_nat (measure := fun (it, _) => it.slice.length - it.i)
    (inv := fun (it, z) => it.slice = iter.slice ∧ it.i ≤ it.slice.length ∧
      z.length = it.i ∧ ∀ k < it.i, z[k]! = Zf it.slice[k]!)
  · rintro ⟨it, z⟩ ⟨hs, hi', hl, hz⟩
    dsimp only
    unfold cbaLoop0Body core.slice.iter.IteratorSliceIter.next
    split
    · rename_i hnext
      have hlt : it.i < it.slice.length := by simpa using hnext
      simp only [bind_ok]
      change (do
        let z1 ← alloc.vec.Vec.push z (Zf it.slice[it.i])
        ok (cont ({ it with i := it.i + 1 }, z1))) ⦃ _ ⦄
      step as ⟨z1, hz1⟩
      refine ⟨hs, by omega, ?_, ?_, by omega⟩
      · rw [alloc.vec.Vec.length_of_val_eq_append hz1, hl]
      · rw [← hl]
        refine alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x => x = Zf it.slice[k]!)
          hz1 (hl ▸ hz) ?_
        rw [hl, Slice.getElem!_Nat_eq, getElem!_pos it.slice.val it.i hlt]
        rfl
    · rename_i hnext
      have hlt : ¬ it.i < it.slice.length := by simpa using hnext
      simp only [bind_ok]
      change (ok (done z)) ⦃ _ ⦄
      simp only [WP.spec_ok]
      have hin : it.i = it.slice.length := by omega
      rw [← hs]
      exact ⟨hl.trans hin, hin ▸ hz⟩
  · exact ⟨rfl, hi, hlen, hzs⟩

open scoped Helpers.IndexStep in
/-- The second loop of `compress_batch_alloc`: compress `(X z, Y z)` for the inverse `z` of
`Z`. -/
private theorem cbaLoop1_spec (hmul : B.MulSpec) {E : Type} [Inhabited E] (Xf Yf Zf : E → B.F)
    (compress : B.F → B.F → Result edwards.CompressedEdwardsY)
    (hcomp : ∀ x y, compress x y ⦃ (r : edwards.CompressedEdwardsY) =>
      r.asNat = (B.toField y).val + 2 ^ 255 * (if (B.toField x).IsNeg then 1 else 0) ⦄)
    (inputs : Slice E)
    (hinputs : ∀ k < inputs.length, B.Red (Xf inputs[k]!) ∧ B.Red (Yf inputs[k]!))
    (iter : core.ops.range.Range Usize) (hn : iter.end.val = inputs.length)
    (zs : alloc.vec.Vec B.F) (hzslen : zs.length = inputs.length)
    (hzs : ∀ k < inputs.length,
      B.toField zs[k]! = (B.toField (Zf inputs[k]!))⁻¹ ∧ B.Red zs[k]!)
    (out : alloc.vec.Vec edwards.CompressedEdwardsY) (hi : iter.start.val ≤ iter.end.val)
    (hlen : out.length = iter.start.val)
    (hout : ∀ k < iter.start.val, out[k]!.asNat =
      (B.toField (Yf inputs[k]!) / B.toField (Zf inputs[k]!)).val + 2 ^ 255 *
        (if (B.toField (Xf inputs[k]!) / B.toField (Zf inputs[k]!)).IsNeg then 1 else 0)) :
    B.cbaLoop1 Xf Yf compress iter inputs zs out
      ⦃ (r : alloc.vec.Vec edwards.CompressedEdwardsY) =>
        r.length = inputs.length ∧ ∀ k < inputs.length, r[k]!.asNat =
          (B.toField (Yf inputs[k]!) / B.toField (Zf inputs[k]!)).val + 2 ^ 255 *
            (if (B.toField (Xf inputs[k]!) / B.toField (Zf inputs[k]!)).IsNeg then 1 else 0) ⦄ := by
  unfold cbaLoop1
  apply loop.spec_decr_nat (measure := fun (it, _) => it.end.val - it.start.val)
    (inv := fun (it, o) => it.end.val = inputs.length ∧ it.start.val ≤ it.end.val ∧
      o.length = it.start.val ∧ ∀ k < it.start.val,
      o[k]!.asNat = (B.toField (Yf inputs[k]!) / B.toField (Zf inputs[k]!)).val + 2 ^ 255 *
        (if (B.toField (Xf inputs[k]!) / B.toField (Zf inputs[k]!)).IsNeg then 1 else 0))
  · rintro ⟨it, o⟩ ⟨hend, hi', hl, ho⟩
    dsimp only
    unfold cbaLoop1Body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨next, it1, hnext, hstart1, hend1⟩
      subst hnext
      step as ⟨ep, hep⟩
      have hik : it.start.val < inputs.length := by scalar_tac
      obtain ⟨hX, hY⟩ := hep ▸ hinputs it.start.val hik
      obtain ⟨hzk, hzkb⟩ := hzs it.start.val hik
      step as ⟨fe, hfe⟩
      have hfee : fe = zs[it.start.val]! := by
        rw [hfe, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      rw [← hfee] at hzk hzkb
      step with hmul (Xf ep) fe (B.red_mulIn hX) (B.red_mulIn hzkb) as ⟨x, hx, hxb⟩
      step with hmul (Yf ep) fe (B.red_mulIn hY) (B.red_mulIn hzkb) as ⟨y, hy, hyb⟩
      step with hcomp x y as ⟨cey, hcey⟩
      step as ⟨o1, ho1⟩
      refine ⟨by scalar_tac, by scalar_tac,
        by rw [alloc.vec.Vec.length_of_val_eq_append ho1, hl, hstart1], ?_, by scalar_tac⟩
      rw [hstart1, ← hl]
      refine alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x => x.asNat =
        (B.toField (Yf inputs[k]!) / B.toField (Zf inputs[k]!)).val + 2 ^ 255 *
          (if (B.toField (Xf inputs[k]!) / B.toField (Zf inputs[k]!)).IsNeg then 1 else 0))
        ho1 (hl ▸ ho) ?_
      rw [hcey, hx, hy, hzk, hep, hl, div_eq_mul_inv, div_eq_mul_inv]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨next, it1, hnext, hit1⟩
      subst hnext
      simp only [WP.spec_ok]
      have hin : it.start.val = inputs.length := by scalar_tac
      exact ⟨hl.trans hin, hin ▸ ho⟩
  · exact ⟨hn, hi, hlen, hout⟩

/-- `compressBatchAlloc`: entry `i` is the canonical `y = Y / Z` of point `i` with the sign of
`x = X / Z` in bit `255`. -/
theorem compressBatchAlloc_spec (hmul : B.MulSpec) (hinv : B.InvertBatchAllocSpec) {E : Type}
    [Inhabited E] (Xf Yf Zf : E → B.F)
    (compress : B.F → B.F → Result edwards.CompressedEdwardsY)
    (hcomp : ∀ x y, compress x y ⦃ (r : edwards.CompressedEdwardsY) =>
      r.asNat = (B.toField y).val + 2 ^ 255 * (if (B.toField x).IsNeg then 1 else 0) ⦄)
    (inputs : Slice E) (hinputs : ∀ i < inputs.length,
      B.Red (Xf inputs[i]!) ∧ B.Red (Yf inputs[i]!) ∧ B.Red (Zf inputs[i]!)) :
    B.compressBatchAlloc Xf Yf Zf compress inputs
      ⦃ (r : alloc.vec.Vec edwards.CompressedEdwardsY) =>
        r.length = inputs.length ∧ ∀ i < inputs.length, r[i]!.asNat =
          (B.toField (Yf inputs[i]!) / B.toField (Zf inputs[i]!)).val + 2 ^ 255 *
            (if (B.toField (Xf inputs[i]!) / B.toField (Zf inputs[i]!)).IsNeg then 1 else 0) ⦄ := by
  unfold compressBatchAlloc
  step as ⟨iter, hsiter, hi⟩
  step with B.cbaLoop0_spec Zf iter (alloc.vec.Vec.with_capacity B.F (Slice.len inputs))
    (by simp [hi]) (by simp [hi]; rfl)
    (fun k hk => by simp [hi] at hk) as ⟨z1, hz1len, hz1⟩
  rw [hsiter] at hz1len hz1
  simp only [alloc.vec.Vec.deref_mut, lift]
  step with hinv z1.slice (fun k hk => by
      rw [alloc.vec.Vec.getElem!_slice, hz1 k (hz1len ▸ hk)]
      exact (hinputs k (hz1len ▸ hk)).2.2) as ⟨s1, hs1len, hs1⟩
  have hs1' : ∀ k < inputs.length,
      B.toField ({ slice := s1 } : alloc.vec.Vec B.F)[k]! = (B.toField (Zf inputs[k]!))⁻¹ ∧
      B.Red ({ slice := s1 } : alloc.vec.Vec B.F)[k]! := by
    intro k hk
    rw [alloc.vec.Vec.getElem!_mk, ← hz1 k hk, ← alloc.vec.Vec.getElem!_slice]
    exact hs1 k (by rw [← hz1len] at hk; exact hk)
  step with B.cbaLoop1_spec hmul Xf Yf Zf compress hcomp inputs
    (fun k hk => ⟨(hinputs k hk).1, (hinputs k hk).2.1⟩)
    { start := 0#usize, «end» := Slice.len inputs } (Slice.len_val inputs) _
    (hs1len.trans hz1len) hs1' (alloc.vec.Vec.with_capacity edwards.CompressedEdwardsY
      (Slice.len inputs)) (by scalar_tac) (by rfl)
    (fun k hk => absurd hk (Nat.not_lt_zero k)) as ⟨r, hrlen, hr⟩
  exact ⟨hrlen, hr⟩

end Curve25519Dalek.Backend

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

private theorem compress_batch_alloc_loop0_eq
    (iter : core.slice.iter.Iter EdwardsPoint.«x86_64-tables»)
    (zs : alloc.vec.Vec FieldElement51) :
    compress_batch_alloc_loop0 iter zs = Backend.U64.cbaLoop0 (·.Z) iter zs := by
  unfold compress_batch_alloc_loop0 Backend.cbaLoop0
  congr 1
  funext ⟨it, z⟩
  dsimp only
  unfold compress_batch_alloc_loop0.body Backend.cbaLoop0Body
  congr 1
  funext ⟨o, it1⟩
  cases o <;> rfl

private theorem compress_batch_alloc_eq (inputs : Slice EdwardsPoint.«x86_64-tables») :
    compress_batch_alloc inputs = Backend.U64.compressBatchAlloc (·.X) (·.Y) (·.Z)
      (fun x y => affine.«AffinePointx86_64-tables».compress { x, y }) inputs := by
  unfold compress_batch_alloc Backend.compressBatchAlloc
  simp only [compress_batch_alloc_loop0_eq]
  rfl

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is the canonical `y = Y / Z` of point `i`
with the sign of `x = X / Z` in bit `255`; limbs `< 2^52`. -/
@[step]
theorem compress_batch_alloc_spec (inputs : Slice EdwardsPoint.«x86_64-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.LimbsLt 52) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧ ∀ i < inputs.length,
        r[i]!.asNat = (inputs[i]!.Y.toField / inputs[i]!.Z.toField).val +
          2 ^ 255 * (if (inputs[i]!.X.toField / inputs[i]!.Z.toField).IsNeg then 1 else 0) ⦄ := by
  rw [compress_batch_alloc_eq]
  exact Backend.compressBatchAlloc_spec Backend.U64 Backend.U64.mul_spec
    Backend.U64.invertBatchAlloc_spec _ _ _ _
    (fun x y => affine.«AffinePointx86_64-tables».compress_spec { x, y }) inputs
    fun i hi => by obtain ⟨hX, hY, hZ, -⟩ := hinputs i hi; exact ⟨hX, hY, hZ⟩

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is RFC 8032's encoding of point `i`. -/
theorem compress_batch_alloc_spec_point (inputs : Slice EdwardsPoint.«x86_64-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.LimbsLt 52)
    (hinputs_on : ∀ i < inputs.length, inputs[i]!.OnCurve) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧
        ∀ i < inputs.length, r[i]!.asNat = curve25519.encode inputs[i]!.toPoint ⦄ :=
  spec_mono (compress_batch_alloc_spec inputs hinputs) fun r ⟨hlen, hr⟩ => ⟨hlen, fun i hi => by
    rw [hr i hi, encode_eq, EdwardsPoint.«x86_64-tables».toPoint_x (hinputs_on i hi),
      EdwardsPoint.«x86_64-tables».toPoint_y (hinputs_on i hi)]⟩

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

private theorem compress_batch_alloc_loop0_eq
    (iter : core.slice.iter.Iter EdwardsPoint.«i686-tables»)
    (zs : alloc.vec.Vec FieldElement2625) :
    compress_batch_alloc_loop0 iter zs = Backend.U32.cbaLoop0 (·.Z) iter zs := by
  unfold compress_batch_alloc_loop0 Backend.cbaLoop0
  congr 1
  funext ⟨it, z⟩
  dsimp only
  unfold compress_batch_alloc_loop0.body Backend.cbaLoop0Body
  congr 1
  funext ⟨o, it1⟩
  cases o <;> rfl

private theorem compress_batch_alloc_eq (inputs : Slice EdwardsPoint.«i686-tables») :
    compress_batch_alloc inputs = Backend.U32.compressBatchAlloc (·.X) (·.Y) (·.Z)
      (fun x y => affine.«AffinePointi686-tables».compress { x, y }) inputs := by
  unfold compress_batch_alloc Backend.compressBatchAlloc
  simp only [compress_batch_alloc_loop0_eq]
  rfl

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is the canonical `y = Y / Z` of point `i`
with the sign of `x = X / Z` in bit `255`; limbs `< 2^26`. -/
@[step]
theorem compress_batch_alloc_spec (inputs : Slice EdwardsPoint.«i686-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.LimbsLt 26) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧ ∀ i < inputs.length,
        r[i]!.asNat = (inputs[i]!.Y.toField / inputs[i]!.Z.toField).val +
          2 ^ 255 * (if (inputs[i]!.X.toField / inputs[i]!.Z.toField).IsNeg then 1 else 0) ⦄ := by
  rw [compress_batch_alloc_eq]
  exact Backend.compressBatchAlloc_spec Backend.U32 Backend.U32.mul_spec
    Backend.U32.invertBatchAlloc_spec _ _ _ _
    (fun x y => affine.«AffinePointi686-tables».compress_spec { x, y }) inputs
    fun i hi => by obtain ⟨hX, hY, hZ, -⟩ := hinputs i hi; exact ⟨hX, hY, hZ⟩

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is RFC 8032's encoding of point `i`. -/
theorem compress_batch_alloc_spec_point (inputs : Slice EdwardsPoint.«i686-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.LimbsLt 26)
    (hinputs_on : ∀ i < inputs.length, inputs[i]!.OnCurve) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧
        ∀ i < inputs.length, r[i]!.asNat = curve25519.encode inputs[i]!.toPoint ⦄ :=
  spec_mono (compress_batch_alloc_spec inputs hinputs) fun r ⟨hlen, hr⟩ => ⟨hlen, fun i hi => by
    rw [hr i hi, encode_eq, EdwardsPoint.«i686-tables».toPoint_x (hinputs_on i hi),
      EdwardsPoint.«i686-tables».toPoint_y (hinputs_on i hi)]⟩

end «EdwardsPointi686-tables»

namespace «EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

private theorem compress_batch_alloc_loop0_eq
    (iter : core.slice.iter.Iter EdwardsPoint.«x86_64-no-tables»)
    (zs : alloc.vec.Vec FieldElement51) :
    compress_batch_alloc_loop0 iter zs = Backend.U64.cbaLoop0 (·.Z) iter zs := by
  unfold compress_batch_alloc_loop0 Backend.cbaLoop0
  congr 1
  funext ⟨it, z⟩
  dsimp only
  unfold compress_batch_alloc_loop0.body Backend.cbaLoop0Body
  congr 1
  funext ⟨o, it1⟩
  cases o <;> rfl

private theorem compress_batch_alloc_eq (inputs : Slice EdwardsPoint.«x86_64-no-tables») :
    compress_batch_alloc inputs = Backend.U64.compressBatchAlloc (·.X) (·.Y) (·.Z)
      (fun x y => affine.«AffinePointx86_64-no-tables».compress { x, y }) inputs := by
  unfold compress_batch_alloc Backend.compressBatchAlloc
  simp only [compress_batch_alloc_loop0_eq]
  rfl

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is the canonical `y = Y / Z` of point `i`
with the sign of `x = X / Z` in bit `255`; limbs `< 2^52`. -/
@[step]
theorem compress_batch_alloc_spec (inputs : Slice EdwardsPoint.«x86_64-no-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.LimbsLt 52) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧ ∀ i < inputs.length,
        r[i]!.asNat = (inputs[i]!.Y.toField / inputs[i]!.Z.toField).val +
          2 ^ 255 * (if (inputs[i]!.X.toField / inputs[i]!.Z.toField).IsNeg then 1 else 0) ⦄ := by
  rw [compress_batch_alloc_eq]
  exact Backend.compressBatchAlloc_spec Backend.U64 Backend.U64.mul_spec
    Backend.U64.invertBatchAlloc_spec _ _ _ _
    (fun x y => affine.«AffinePointx86_64-no-tables».compress_spec { x, y }) inputs
    fun i hi => by obtain ⟨hX, hY, hZ, -⟩ := hinputs i hi; exact ⟨hX, hY, hZ⟩

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is RFC 8032's encoding of point `i`. -/
theorem compress_batch_alloc_spec_point (inputs : Slice EdwardsPoint.«x86_64-no-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.LimbsLt 52)
    (hinputs_on : ∀ i < inputs.length, inputs[i]!.OnCurve) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧
        ∀ i < inputs.length, r[i]!.asNat = curve25519.encode inputs[i]!.toPoint ⦄ :=
  spec_mono (compress_batch_alloc_spec inputs hinputs) fun r ⟨hlen, hr⟩ => ⟨hlen, fun i hi => by
    rw [hr i hi, encode_eq, EdwardsPoint.«x86_64-no-tables».toPoint_x (hinputs_on i hi),
      EdwardsPoint.«x86_64-no-tables».toPoint_y (hinputs_on i hi)]⟩

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

private theorem compress_batch_alloc_loop0_eq
    (iter : core.slice.iter.Iter EdwardsPoint.«i686-no-tables»)
    (zs : alloc.vec.Vec FieldElement2625) :
    compress_batch_alloc_loop0 iter zs = Backend.U32.cbaLoop0 (·.Z) iter zs := by
  unfold compress_batch_alloc_loop0 Backend.cbaLoop0
  congr 1
  funext ⟨it, z⟩
  dsimp only
  unfold compress_batch_alloc_loop0.body Backend.cbaLoop0Body
  congr 1
  funext ⟨o, it1⟩
  cases o <;> rfl

private theorem compress_batch_alloc_eq (inputs : Slice EdwardsPoint.«i686-no-tables») :
    compress_batch_alloc inputs = Backend.U32.compressBatchAlloc (·.X) (·.Y) (·.Z)
      (fun x y => affine.«AffinePointi686-no-tables».compress { x, y }) inputs := by
  unfold compress_batch_alloc Backend.compressBatchAlloc
  simp only [compress_batch_alloc_loop0_eq]
  rfl

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is the canonical `y = Y / Z` of point `i`
with the sign of `x = X / Z` in bit `255`; limbs `< 2^26`. -/
@[step]
theorem compress_batch_alloc_spec (inputs : Slice EdwardsPoint.«i686-no-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.LimbsLt 26) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧ ∀ i < inputs.length,
        r[i]!.asNat = (inputs[i]!.Y.toField / inputs[i]!.Z.toField).val +
          2 ^ 255 * (if (inputs[i]!.X.toField / inputs[i]!.Z.toField).IsNeg then 1 else 0) ⦄ := by
  rw [compress_batch_alloc_eq]
  exact Backend.compressBatchAlloc_spec Backend.U32 Backend.U32.mul_spec
    Backend.U32.invertBatchAlloc_spec _ _ _ _
    (fun x y => affine.«AffinePointi686-no-tables».compress_spec { x, y }) inputs
    fun i hi => by obtain ⟨hX, hY, hZ, -⟩ := hinputs i hi; exact ⟨hX, hY, hZ⟩

/-- `EdwardsPoint::compress_batch_alloc`: entry `i` is RFC 8032's encoding of point `i`. -/
theorem compress_batch_alloc_spec_point (inputs : Slice EdwardsPoint.«i686-no-tables»)
    (hinputs : ∀ i < inputs.length, inputs[i]!.LimbsLt 26)
    (hinputs_on : ∀ i < inputs.length, inputs[i]!.OnCurve) :
    compress_batch_alloc inputs ⦃ (r : alloc.vec.Vec CompressedEdwardsY) =>
      r.length = inputs.length ∧
        ∀ i < inputs.length, r[i]!.asNat = curve25519.encode inputs[i]!.toPoint ⦄ :=
  spec_mono (compress_batch_alloc_spec inputs hinputs) fun r ⟨hlen, hr⟩ => ⟨hlen, fun i hi => by
    rw [hr i hi, encode_eq, EdwardsPoint.«i686-no-tables».toPoint_x (hinputs_on i hi),
      EdwardsPoint.«i686-no-tables».toPoint_y (hinputs_on i hi)]⟩

end «EdwardsPointi686-no-tables»

end Curve25519Dalek.edwards
