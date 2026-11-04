/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Iterator
public import Defs.Scalar
import Proofs.Backend.Serial.CurveModels.AddProjectiveNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Edwards.Identity
import Proofs.Edwards.MulByPow2
import Proofs.Helpers.Cmp
import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
import Proofs.Helpers.Naf
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Vec
import Proofs.Scalar.AsRadix16
import Proofs.Window.LookupTableFrom
import Proofs.Window.LookupTableSelect
import Zeroize
public import Proofs.Helpers.EdwardsOps.Instances
public import Proofs.Backend.Serial.ScalarMul.Straus.MultiscalarMulGeneric
public section

/-! # `Straus::multiscalar_mul`

Constant-time Straus: the lookup tables of `P, 2 P, …, 8 P` of the points, the radix-`16` digits
of the scalars, and Horner's rule over the `64` digit positions, adding `d_i[j] • P_i` for every
point (up to the shorter of the two inputs, as the patched index loop) after `16 •` the
accumulator. The inputs are `IntoIterator`s (`IntoIterator.Yields`) whose items are borrowed as
scalars and points. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.straus

section
open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
    (add_spec_point)

namespace «MultiscalarMulStrausEdwardsPointx86_64-tables».multiscalar_mul

open window.«LookupTableProjectiveNielsPointx86_64-tables».Insts in
/-- The points' lookup tables. -/
@[local step]
private theorem lookup_tables_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«x86_64-tables»)
    (points : It) (ys : List Clause0_Item) (hit : iterInst.Yields points ys)
    (ps : List edwards.EdwardsPoint.«x86_64-tables»)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : edwards.EdwardsPoint.«x86_64-tables») => P' = P ⦄) ys
          ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve) (hlen : ys.length ≤ Usize.max) :
    loop (fun ((it, out) : It × alloc.vec.Vec
        (window.LookupTable ProjectiveNielsPoint.«x86_64-tables»)) =>
      collect.collectMapBody iterInst borrowInst.borrow
        «CoreConvertFromSharedAEdwardsPointx86_64-tables».«from» it out)
      (points, alloc.vec.Vec.new _)
      ⦃ (r : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«x86_64-tables»)) =>
        List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) ps r.val ⦄ := by
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow
    «CoreConvertFromSharedAEdwardsPointx86_64-tables».«from»
    (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) points ys hit ps hborrow
    (fun P hP =>
        «CoreConvertFromSharedAEdwardsPointx86_64-tables».from_spec
      P (hps P hP).1 (hps P hP).2) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

/-- The scalars' radix-`16` digits. -/
@[local step]
private theorem scalar_digits_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (scalars : It) (xs : List Clause0_Item) (hit : iterInst.Yields scalars xs)
    (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hlen : xs.length ≤ Usize.max) :
    loop (fun ((it, out) : It × alloc.vec.Vec (Array I8 64#usize)) =>
      collect.collectMapBody iterInst borrowInst.borrow scalar.Scalar.as_radix_16 it out)
      (scalars, alloc.vec.Vec.new _)
      ⦃ (r : alloc.vec.Vec (Array I8 64#usize)) =>
        List.Forall₂ (fun s d => d.asInt 4 = s.asNat ∧
          ∀ i : ℕ, i < 64 → -8 ≤ d[i]!.val ∧ d[i]!.val ≤ 8) ss r.val ⦄ := by
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow scalar.Scalar.as_radix_16
    (fun s d => d.asInt 4 = s.asNat ∧ ∀ i : ℕ, i < 64 → -8 ≤ d[i]!.val ∧ d[i]!.val ≤ 8)
    scalars xs hit ss hborrow (fun s hs => spec_mono (scalar.Scalar.as_radix_16_spec s (hss s hs))
      fun d ⟨hval, hlow, h63l, h63u⟩ => ⟨hval, fun i hi => by
        rcases Nat.lt_or_ge i 63 with h | h
        · exact ⟨(hlow i h).1, (hlow i h).2.le⟩
        · rw [show i = 63 by omega]; exact ⟨h63l, h63u⟩⟩) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

end «MultiscalarMulStrausEdwardsPointx86_64-tables».multiscalar_mul

namespace Straus.Insts.«Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-tables»

private theorem multiscalar_mul_loop2_loop0_eq
    (lookup_tables : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«x86_64-tables»))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize))
    (Q : edwards.EdwardsPoint.«x86_64-tables») (j : Usize) (it : core.ops.range.Range Usize) :
    multiscalar_mul_loop2_loop0 it lookup_tables scalar_digits Q j =
      EdwardsOps.X86Tables.strausMsLoop00 it lookup_tables scalar_digits Q j := by
  unfold multiscalar_mul_loop2_loop0 EdwardsOps.strausMsLoop00
  congr 1

private theorem multiscalar_mul_loop2_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (lookup_tables : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«x86_64-tables»))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize))
    (Q : edwards.EdwardsPoint.«x86_64-tables») :
    multiscalar_mul_loop2 iter lookup_tables scalar_digits Q =
      EdwardsOps.X86Tables.strausMsLoop0 iter lookup_tables scalar_digits Q := by
  unfold multiscalar_mul_loop2 EdwardsOps.strausMsLoop0
  congr 1

/-- The outer loop: after the digit positions `e, …, 63`, the accumulator represents
`∑_{k < n} radix16Tail d_k e • P_k`. -/
@[local step]
private theorem multiscalar_mul_loop2_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (lookup_tables : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«x86_64-tables»))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize)) (Q : edwards.EdwardsPoint.«x86_64-tables»)
    (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min scalar_digits.length lookup_tables.length)
    (hT : ∀ k < n, lookup_tables.val[k]!.Represents (P k) ∧ lookup_tables.val[k]!.LimbsLt 54)
    (hD : ∀ k < n, ∀ e : ℕ, e < 64 → -8 ≤ (scalar_digits.val[k]!)[e]!.val ∧
      (scalar_digits.val[k]!)[e]!.val ≤ 8)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 64)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve)
    (hQp : Q.toPoint = ∑ k ∈ Finset.range n,
      radix16Tail scalar_digits.val[k]! iter.iter.end.val • P k) :
    multiscalar_mul_loop2 iter lookup_tables scalar_digits Q
      ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») => r.OnCurve ∧ r.LimbsLt 52 ∧
        r.toPoint = ∑ k ∈ Finset.range n, radix16Tail scalar_digits.val[k]! 0 • P k ⦄ := by
  rw [multiscalar_mul_loop2_eq]
  exact EdwardsOps.X86Tables.strausMsLoop0_spec
    EdwardsOps.X86Tables.addN_spec EdwardsOps.X86Tables.asExtended_spec
    EdwardsOps.X86Tables.ltSelect_spec EdwardsOps.X86Tables.mulByPow2_spec iter lookup_tables
    scalar_digits Q P n hn hT hD hstart hend hQ hon hQp

/-- `Straus::multiscalar_mul`: `∑ s_i • P_i` over the scalars and points the two inputs yield,
up to the shorter one (unreduced scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«x86_64-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«x86_64-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«x86_64-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 52 ⦄ := by
  unfold multiscalar_mul
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  step with hpoints' as ⟨it, hit⟩
  unfold multiscalar_mul_loop0
  apply spec_bind
    («MultiscalarMulStrausEdwardsPointx86_64-tables».multiscalar_mul.lookup_tables_spec
      _ _ it ys hit ps hborrow_points hps hys)
  intro tables htables
  step with hscalars' as ⟨it1, hit1⟩
  unfold multiscalar_mul_loop1
  apply spec_bind
    («MultiscalarMulStrausEdwardsPointx86_64-tables».multiscalar_mul.scalar_digits_spec
      _ _ it1 xs hit1 ss hborrow_scalars hss hxs)
  intro digits hdigits
  step with
      edwards.EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨Q, hQon, hQ, hQb⟩
  step as ⟨iter, hiter⟩
  obtain ⟨hTlen, hT⟩ := forall₂_getElem! htables
  obtain ⟨hDlen, hD⟩ := forall₂_getElem! hdigits
  have hn : min ss.length ps.length = min digits.length tables.length := by
    rw [hTlen, hDlen]
  step with multiscalar_mul_loop2_spec iter tables digits Q (fun k => ps[k]!.toPoint)
    (min ss.length ps.length) hn
    (fun k hk => hT k (by have := min_le_right ss.length ps.length; omega))
    (fun k hk => (hD k (by have := min_le_left ss.length ps.length; omega)).2)
    (by rw [hiter]; rfl) (by rw [hiter]; decide) hQb hQon
    (by
      rw [hQ, hiter]
      exact (Finset.sum_eq_zero fun k _ => by
        rw [show ({ start := 0#usize, «end» := 64#usize } : core.ops.range.Range Usize).end.val
          = 64 from rfl, radix16Tail_sixtyFour, zero_smul]).symm)
    as ⟨r, hron, hrb, hr⟩
  have hzer : ∀ x ∈ digits.val, (Array.Insts.ZeroizeZeroize 64#usize
      (zeroize.Zeroize.Blanket I8.Insts.ZeroizeDefaultIsZeroes)).zeroize x ⦃ _ => True ⦄ :=
    fun x _ => spec_mono (_root_.Array.Insts.ZeroizeZeroize.zeroize_spec (post := fun _ => True) _ x
      fun y _ => spec_mono (I8.Insts.ZeroizeDefaultIsZeroes.zeroize_spec y) fun _ _ => trivial)
      fun _ _ => trivial
  step with alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_spec _ _ hzer as ⟨z, hz⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, sum_zipWith_eq]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [radix16Tail_zero, (hD k (by have := min_le_left ss.length ps.length; omega)).1,
    natCast_zsmul]

end Straus.Insts.«Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-tables»

end

section
open «Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-tablesCompletedPointi686-tables»
    (add_spec_point)

namespace «MultiscalarMulStrausEdwardsPointi686-tables».multiscalar_mul

open window.«LookupTableProjectiveNielsPointi686-tables».Insts in
/-- The points' lookup tables. -/
@[local step]
private theorem lookup_tables_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«i686-tables»)
    (points : It) (ys : List Clause0_Item) (hit : iterInst.Yields points ys)
    (ps : List edwards.EdwardsPoint.«i686-tables»)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : edwards.EdwardsPoint.«i686-tables») => P' = P ⦄) ys
          ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26 ∧ P.OnCurve) (hlen : ys.length ≤ Usize.max) :
    loop (fun ((it, out) : It × alloc.vec.Vec
        (window.LookupTable ProjectiveNielsPoint.«i686-tables»)) =>
      collect.collectMapBody iterInst borrowInst.borrow
        «CoreConvertFromSharedAEdwardsPointi686-tables».«from» it out)
      (points, alloc.vec.Vec.new _)
      ⦃ (r : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«i686-tables»)) =>
        List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27) ps r.val ⦄ := by
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow
    «CoreConvertFromSharedAEdwardsPointi686-tables».«from»
    (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27) points ys hit ps hborrow
    (fun P hP =>
        «CoreConvertFromSharedAEdwardsPointi686-tables».from_spec
      P (hps P hP).1 (hps P hP).2) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

/-- The scalars' radix-`16` digits. -/
@[local step]
private theorem scalar_digits_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (scalars : It) (xs : List Clause0_Item) (hit : iterInst.Yields scalars xs)
    (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hlen : xs.length ≤ Usize.max) :
    loop (fun ((it, out) : It × alloc.vec.Vec (Array I8 64#usize)) =>
      collect.collectMapBody iterInst borrowInst.borrow scalar.Scalar.as_radix_16 it out)
      (scalars, alloc.vec.Vec.new _)
      ⦃ (r : alloc.vec.Vec (Array I8 64#usize)) =>
        List.Forall₂ (fun s d => d.asInt 4 = s.asNat ∧
          ∀ i : ℕ, i < 64 → -8 ≤ d[i]!.val ∧ d[i]!.val ≤ 8) ss r.val ⦄ := by
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow scalar.Scalar.as_radix_16
    (fun s d => d.asInt 4 = s.asNat ∧ ∀ i : ℕ, i < 64 → -8 ≤ d[i]!.val ∧ d[i]!.val ≤ 8)
    scalars xs hit ss hborrow (fun s hs => spec_mono (scalar.Scalar.as_radix_16_spec s (hss s hs))
      fun d ⟨hval, hlow, h63l, h63u⟩ => ⟨hval, fun i hi => by
        rcases Nat.lt_or_ge i 63 with h | h
        · exact ⟨(hlow i h).1, (hlow i h).2.le⟩
        · rw [show i = 63 by omega]; exact ⟨h63l, h63u⟩⟩) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

end «MultiscalarMulStrausEdwardsPointi686-tables».multiscalar_mul

namespace Straus.Insts.«Curve25519_dalekTraitsMultiscalarMulEdwardsPointi686-tables»

private theorem multiscalar_mul_loop2_loop0_eq
    (lookup_tables : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«i686-tables»))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize))
    (Q : edwards.EdwardsPoint.«i686-tables») (j : Usize) (it : core.ops.range.Range Usize) :
    multiscalar_mul_loop2_loop0 it lookup_tables scalar_digits Q j =
      EdwardsOps.I686Tables.strausMsLoop00 it lookup_tables scalar_digits Q j := by
  unfold multiscalar_mul_loop2_loop0 EdwardsOps.strausMsLoop00
  congr 1

private theorem multiscalar_mul_loop2_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (lookup_tables : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«i686-tables»))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize))
    (Q : edwards.EdwardsPoint.«i686-tables») :
    multiscalar_mul_loop2 iter lookup_tables scalar_digits Q =
      EdwardsOps.I686Tables.strausMsLoop0 iter lookup_tables scalar_digits Q := by
  unfold multiscalar_mul_loop2 EdwardsOps.strausMsLoop0
  congr 1

/-- The outer loop: after the digit positions `e, …, 63`, the accumulator represents
`∑_{k < n} radix16Tail d_k e • P_k`. -/
@[local step]
private theorem multiscalar_mul_loop2_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (lookup_tables : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«i686-tables»))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize)) (Q : edwards.EdwardsPoint.«i686-tables»)
    (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min scalar_digits.length lookup_tables.length)
    (hT : ∀ k < n, lookup_tables.val[k]!.Represents (P k) ∧ lookup_tables.val[k]!.LimbsLt 27)
    (hD : ∀ k < n, ∀ e : ℕ, e < 64 → -8 ≤ (scalar_digits.val[k]!)[e]!.val ∧
      (scalar_digits.val[k]!)[e]!.val ≤ 8)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 64)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve)
    (hQp : Q.toPoint = ∑ k ∈ Finset.range n,
      radix16Tail scalar_digits.val[k]! iter.iter.end.val • P k) :
    multiscalar_mul_loop2 iter lookup_tables scalar_digits Q
      ⦃ (r : edwards.EdwardsPoint.«i686-tables») => r.OnCurve ∧ r.LimbsLt 26 ∧
        r.toPoint = ∑ k ∈ Finset.range n, radix16Tail scalar_digits.val[k]! 0 • P k ⦄ := by
  rw [multiscalar_mul_loop2_eq]
  exact EdwardsOps.I686Tables.strausMsLoop0_spec
    EdwardsOps.I686Tables.addN_spec EdwardsOps.I686Tables.asExtended_spec
    EdwardsOps.I686Tables.ltSelect_spec EdwardsOps.I686Tables.mulByPow2_spec iter lookup_tables
    scalar_digits Q P n hn hT hD hstart hend hQ hon hQp

/-- `Straus::multiscalar_mul`: `∑ s_i • P_i` over the scalars and points the two inputs yield,
up to the shorter one (unreduced scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«i686-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«i686-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«i686-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 26 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«i686-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 26 ⦄ := by
  unfold multiscalar_mul
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  step with hpoints' as ⟨it, hit⟩
  unfold multiscalar_mul_loop0
  apply spec_bind
    («MultiscalarMulStrausEdwardsPointi686-tables».multiscalar_mul.lookup_tables_spec
      _ _ it ys hit ps hborrow_points hps hys)
  intro tables htables
  step with hscalars' as ⟨it1, hit1⟩
  unfold multiscalar_mul_loop1
  apply spec_bind
    («MultiscalarMulStrausEdwardsPointi686-tables».multiscalar_mul.scalar_digits_spec
      _ _ it1 xs hit1 ss hborrow_scalars hss hxs)
  intro digits hdigits
  step with
      edwards.EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨Q, hQon, hQ, hQb⟩
  step as ⟨iter, hiter⟩
  obtain ⟨hTlen, hT⟩ := forall₂_getElem! htables
  obtain ⟨hDlen, hD⟩ := forall₂_getElem! hdigits
  have hn : min ss.length ps.length = min digits.length tables.length := by
    rw [hTlen, hDlen]
  step with multiscalar_mul_loop2_spec iter tables digits Q (fun k => ps[k]!.toPoint)
    (min ss.length ps.length) hn
    (fun k hk => hT k (by have := min_le_right ss.length ps.length; omega))
    (fun k hk => (hD k (by have := min_le_left ss.length ps.length; omega)).2)
    (by rw [hiter]; rfl) (by rw [hiter]; decide) hQb hQon
    (by
      rw [hQ, hiter]
      exact (Finset.sum_eq_zero fun k _ => by
        rw [show ({ start := 0#usize, «end» := 64#usize } : core.ops.range.Range Usize).end.val
          = 64 from rfl, radix16Tail_sixtyFour, zero_smul]).symm)
    as ⟨r, hron, hrb, hr⟩
  have hzer : ∀ x ∈ digits.val, (Array.Insts.ZeroizeZeroize 64#usize
      (zeroize.Zeroize.Blanket I8.Insts.ZeroizeDefaultIsZeroes)).zeroize x ⦃ _ => True ⦄ :=
    fun x _ => spec_mono (_root_.Array.Insts.ZeroizeZeroize.zeroize_spec (post := fun _ => True) _ x
      fun y _ => spec_mono (I8.Insts.ZeroizeDefaultIsZeroes.zeroize_spec y) fun _ _ => trivial)
      fun _ _ => trivial
  step with alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_spec _ _ hzer as ⟨z, hz⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, sum_zipWith_eq]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [radix16Tail_zero, (hD k (by have := min_le_left ss.length ps.length; omega)).1,
    natCast_zsmul]

end Straus.Insts.«Curve25519_dalekTraitsMultiscalarMulEdwardsPointi686-tables»

end

section
open «Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
    (add_spec_point)

namespace «MultiscalarMulStrausEdwardsPointx86_64-no-tables».multiscalar_mul

open window.«LookupTableProjectiveNielsPointx86_64-no-tables».Insts in
/-- The points' lookup tables. -/
@[local step]
private theorem lookup_tables_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«x86_64-no-tables»)
    (points : It) (ys : List Clause0_Item) (hit : iterInst.Yields points ys)
    (ps : List edwards.EdwardsPoint.«x86_64-no-tables»)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : edwards.EdwardsPoint.«x86_64-no-tables») => P' = P ⦄)
          ys ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve) (hlen : ys.length ≤ Usize.max) :
    loop (fun ((it, out) : It × alloc.vec.Vec
        (window.LookupTable ProjectiveNielsPoint.«x86_64-no-tables»)) =>
      collect.collectMapBody iterInst borrowInst.borrow
        «CoreConvertFromSharedAEdwardsPointx86_64-no-tables».«from» it out)
      (points, alloc.vec.Vec.new _)
      ⦃ (r : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«x86_64-no-tables»)) =>
        List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) ps r.val ⦄ := by
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow
    «CoreConvertFromSharedAEdwardsPointx86_64-no-tables».«from»
    (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) points ys hit ps hborrow
    (fun P hP =>
        «CoreConvertFromSharedAEdwardsPointx86_64-no-tables».from_spec
      P (hps P hP).1 (hps P hP).2) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

/-- The scalars' radix-`16` digits. -/
@[local step]
private theorem scalar_digits_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (scalars : It) (xs : List Clause0_Item) (hit : iterInst.Yields scalars xs)
    (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hlen : xs.length ≤ Usize.max) :
    loop (fun ((it, out) : It × alloc.vec.Vec (Array I8 64#usize)) =>
      collect.collectMapBody iterInst borrowInst.borrow scalar.Scalar.as_radix_16 it out)
      (scalars, alloc.vec.Vec.new _)
      ⦃ (r : alloc.vec.Vec (Array I8 64#usize)) =>
        List.Forall₂ (fun s d => d.asInt 4 = s.asNat ∧
          ∀ i : ℕ, i < 64 → -8 ≤ d[i]!.val ∧ d[i]!.val ≤ 8) ss r.val ⦄ := by
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow scalar.Scalar.as_radix_16
    (fun s d => d.asInt 4 = s.asNat ∧ ∀ i : ℕ, i < 64 → -8 ≤ d[i]!.val ∧ d[i]!.val ≤ 8)
    scalars xs hit ss hborrow (fun s hs => spec_mono (scalar.Scalar.as_radix_16_spec s (hss s hs))
      fun d ⟨hval, hlow, h63l, h63u⟩ => ⟨hval, fun i hi => by
        rcases Nat.lt_or_ge i 63 with h | h
        · exact ⟨(hlow i h).1, (hlow i h).2.le⟩
        · rw [show i = 63 by omega]; exact ⟨h63l, h63u⟩⟩) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

end «MultiscalarMulStrausEdwardsPointx86_64-no-tables».multiscalar_mul

namespace Straus.Insts.«Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-no-tables»

private theorem multiscalar_mul_loop2_loop0_eq
    (lookup_tables : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«x86_64-no-tables»))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize))
    (Q : edwards.EdwardsPoint.«x86_64-no-tables») (j : Usize) (it : core.ops.range.Range Usize) :
    multiscalar_mul_loop2_loop0 it lookup_tables scalar_digits Q j =
      EdwardsOps.X86NoTables.strausMsLoop00 it lookup_tables scalar_digits Q j := by
  unfold multiscalar_mul_loop2_loop0 EdwardsOps.strausMsLoop00
  congr 1

private theorem multiscalar_mul_loop2_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (lookup_tables : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«x86_64-no-tables»))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize))
    (Q : edwards.EdwardsPoint.«x86_64-no-tables») :
    multiscalar_mul_loop2 iter lookup_tables scalar_digits Q =
      EdwardsOps.X86NoTables.strausMsLoop0 iter lookup_tables scalar_digits Q := by
  unfold multiscalar_mul_loop2 EdwardsOps.strausMsLoop0
  congr 1

/-- The outer loop: after the digit positions `e, …, 63`, the accumulator represents
`∑_{k < n} radix16Tail d_k e • P_k`. -/
@[local step]
private theorem multiscalar_mul_loop2_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (lookup_tables : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«x86_64-no-tables»))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize))
        (Q : edwards.EdwardsPoint.«x86_64-no-tables»)
    (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min scalar_digits.length lookup_tables.length)
    (hT : ∀ k < n, lookup_tables.val[k]!.Represents (P k) ∧ lookup_tables.val[k]!.LimbsLt 54)
    (hD : ∀ k < n, ∀ e : ℕ, e < 64 → -8 ≤ (scalar_digits.val[k]!)[e]!.val ∧
      (scalar_digits.val[k]!)[e]!.val ≤ 8)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 64)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve)
    (hQp : Q.toPoint = ∑ k ∈ Finset.range n,
      radix16Tail scalar_digits.val[k]! iter.iter.end.val • P k) :
    multiscalar_mul_loop2 iter lookup_tables scalar_digits Q
      ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») => r.OnCurve ∧ r.LimbsLt 52 ∧
        r.toPoint = ∑ k ∈ Finset.range n, radix16Tail scalar_digits.val[k]! 0 • P k ⦄ := by
  rw [multiscalar_mul_loop2_eq]
  exact EdwardsOps.X86NoTables.strausMsLoop0_spec
    EdwardsOps.X86NoTables.addN_spec EdwardsOps.X86NoTables.asExtended_spec
    EdwardsOps.X86NoTables.ltSelect_spec EdwardsOps.X86NoTables.mulByPow2_spec iter lookup_tables
    scalar_digits Q P n hn hT hD hstart hend hQ hon hQp

open edwards.EdwardsPoint.«x86_64-no-tables».Insts in
/-- `Straus::multiscalar_mul`: `∑ s_i • P_i` over the scalars and points the two inputs yield,
up to the shorter one (unreduced scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«x86_64-no-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«x86_64-no-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«x86_64-no-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 52 ⦄ := by
  unfold multiscalar_mul
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  step with hpoints' as ⟨it, hit⟩
  unfold multiscalar_mul_loop0
  apply spec_bind
    («MultiscalarMulStrausEdwardsPointx86_64-no-tables».multiscalar_mul.lookup_tables_spec
      _ _ it ys hit ps hborrow_points hps hys)
  intro tables htables
  step with hscalars' as ⟨it1, hit1⟩
  unfold multiscalar_mul_loop1
  apply spec_bind
    («MultiscalarMulStrausEdwardsPointx86_64-no-tables».multiscalar_mul.scalar_digits_spec
      _ _ it1 xs hit1 ss hborrow_scalars hss hxs)
  intro digits hdigits
  step with Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨Q, hQon, hQ, hQb⟩
  step as ⟨iter, hiter⟩
  obtain ⟨hTlen, hT⟩ := forall₂_getElem! htables
  obtain ⟨hDlen, hD⟩ := forall₂_getElem! hdigits
  have hn : min ss.length ps.length = min digits.length tables.length := by
    rw [hTlen, hDlen]
  step with multiscalar_mul_loop2_spec iter tables digits Q (fun k => ps[k]!.toPoint)
    (min ss.length ps.length) hn
    (fun k hk => hT k (by have := min_le_right ss.length ps.length; omega))
    (fun k hk => (hD k (by have := min_le_left ss.length ps.length; omega)).2)
    (by rw [hiter]; rfl) (by rw [hiter]; decide) hQb hQon
    (by
      rw [hQ, hiter]
      exact (Finset.sum_eq_zero fun k _ => by
        rw [show ({ start := 0#usize, «end» := 64#usize } : core.ops.range.Range Usize).end.val
          = 64 from rfl, radix16Tail_sixtyFour, zero_smul]).symm)
    as ⟨r, hron, hrb, hr⟩
  have hzer : ∀ x ∈ digits.val, (Array.Insts.ZeroizeZeroize 64#usize
      (zeroize.Zeroize.Blanket I8.Insts.ZeroizeDefaultIsZeroes)).zeroize x ⦃ _ => True ⦄ :=
    fun x _ => spec_mono (_root_.Array.Insts.ZeroizeZeroize.zeroize_spec (post := fun _ => True) _ x
      fun y _ => spec_mono (I8.Insts.ZeroizeDefaultIsZeroes.zeroize_spec y) fun _ _ => trivial)
      fun _ _ => trivial
  step with alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_spec _ _ hzer as ⟨z, hz⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, sum_zipWith_eq]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [radix16Tail_zero, (hD k (by have := min_le_left ss.length ps.length; omega)).1,
    natCast_zsmul]

end Straus.Insts.«Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-no-tables»

end

section
open «Shared0EdwardsPointi686-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»
    (add_spec_point)

namespace «MultiscalarMulStrausEdwardsPointi686-no-tables».multiscalar_mul

open window.«LookupTableProjectiveNielsPointi686-no-tables».Insts in
/-- The points' lookup tables. -/
@[local step]
private theorem lookup_tables_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«i686-no-tables»)
    (points : It) (ys : List Clause0_Item) (hit : iterInst.Yields points ys)
    (ps : List edwards.EdwardsPoint.«i686-no-tables»)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : edwards.EdwardsPoint.«i686-no-tables») => P' = P ⦄)
          ys ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26 ∧ P.OnCurve) (hlen : ys.length ≤ Usize.max) :
    loop (fun ((it, out) : It × alloc.vec.Vec
        (window.LookupTable ProjectiveNielsPoint.«i686-no-tables»)) =>
      collect.collectMapBody iterInst borrowInst.borrow
        «CoreConvertFromSharedAEdwardsPointi686-no-tables».«from» it out)
      (points, alloc.vec.Vec.new _)
      ⦃ (r : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«i686-no-tables»)) =>
        List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27) ps r.val ⦄ := by
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow
    «CoreConvertFromSharedAEdwardsPointi686-no-tables».«from»
    (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27) points ys hit ps hborrow
    (fun P hP =>
        «CoreConvertFromSharedAEdwardsPointi686-no-tables».from_spec
      P (hps P hP).1 (hps P hP).2) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

/-- The scalars' radix-`16` digits. -/
@[local step]
private theorem scalar_digits_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (scalars : It) (xs : List Clause0_Item) (hit : iterInst.Yields scalars xs)
    (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hlen : xs.length ≤ Usize.max) :
    loop (fun ((it, out) : It × alloc.vec.Vec (Array I8 64#usize)) =>
      collect.collectMapBody iterInst borrowInst.borrow scalar.Scalar.as_radix_16 it out)
      (scalars, alloc.vec.Vec.new _)
      ⦃ (r : alloc.vec.Vec (Array I8 64#usize)) =>
        List.Forall₂ (fun s d => d.asInt 4 = s.asNat ∧
          ∀ i : ℕ, i < 64 → -8 ≤ d[i]!.val ∧ d[i]!.val ≤ 8) ss r.val ⦄ := by
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow scalar.Scalar.as_radix_16
    (fun s d => d.asInt 4 = s.asNat ∧ ∀ i : ℕ, i < 64 → -8 ≤ d[i]!.val ∧ d[i]!.val ≤ 8)
    scalars xs hit ss hborrow (fun s hs => spec_mono (scalar.Scalar.as_radix_16_spec s (hss s hs))
      fun d ⟨hval, hlow, h63l, h63u⟩ => ⟨hval, fun i hi => by
        rcases Nat.lt_or_ge i 63 with h | h
        · exact ⟨(hlow i h).1, (hlow i h).2.le⟩
        · rw [show i = 63 by omega]; exact ⟨h63l, h63u⟩⟩) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

end «MultiscalarMulStrausEdwardsPointi686-no-tables».multiscalar_mul

namespace Straus.Insts.«Curve25519_dalekTraitsMultiscalarMulEdwardsPointi686-no-tables»

private theorem multiscalar_mul_loop2_loop0_eq
    (lookup_tables : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«i686-no-tables»))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize))
    (Q : edwards.EdwardsPoint.«i686-no-tables») (j : Usize) (it : core.ops.range.Range Usize) :
    multiscalar_mul_loop2_loop0 it lookup_tables scalar_digits Q j =
      EdwardsOps.I686NoTables.strausMsLoop00 it lookup_tables scalar_digits Q j := by
  unfold multiscalar_mul_loop2_loop0 EdwardsOps.strausMsLoop00
  congr 1

private theorem multiscalar_mul_loop2_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (lookup_tables : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«i686-no-tables»))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize))
    (Q : edwards.EdwardsPoint.«i686-no-tables») :
    multiscalar_mul_loop2 iter lookup_tables scalar_digits Q =
      EdwardsOps.I686NoTables.strausMsLoop0 iter lookup_tables scalar_digits Q := by
  unfold multiscalar_mul_loop2 EdwardsOps.strausMsLoop0
  congr 1

/-- The outer loop: after the digit positions `e, …, 63`, the accumulator represents
`∑_{k < n} radix16Tail d_k e • P_k`. -/
@[local step]
private theorem multiscalar_mul_loop2_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (lookup_tables : alloc.vec.Vec (window.LookupTable ProjectiveNielsPoint.«i686-no-tables»))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize))
        (Q : edwards.EdwardsPoint.«i686-no-tables»)
    (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min scalar_digits.length lookup_tables.length)
    (hT : ∀ k < n, lookup_tables.val[k]!.Represents (P k) ∧ lookup_tables.val[k]!.LimbsLt 27)
    (hD : ∀ k < n, ∀ e : ℕ, e < 64 → -8 ≤ (scalar_digits.val[k]!)[e]!.val ∧
      (scalar_digits.val[k]!)[e]!.val ≤ 8)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 64)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve)
    (hQp : Q.toPoint = ∑ k ∈ Finset.range n,
      radix16Tail scalar_digits.val[k]! iter.iter.end.val • P k) :
    multiscalar_mul_loop2 iter lookup_tables scalar_digits Q
      ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») => r.OnCurve ∧ r.LimbsLt 26 ∧
        r.toPoint = ∑ k ∈ Finset.range n, radix16Tail scalar_digits.val[k]! 0 • P k ⦄ := by
  rw [multiscalar_mul_loop2_eq]
  exact EdwardsOps.I686NoTables.strausMsLoop0_spec
    EdwardsOps.I686NoTables.addN_spec EdwardsOps.I686NoTables.asExtended_spec
    EdwardsOps.I686NoTables.ltSelect_spec EdwardsOps.I686NoTables.mulByPow2_spec iter lookup_tables
    scalar_digits Q P n hn hT hD hstart hend hQ hon hQp

open edwards.EdwardsPoint.«i686-no-tables».Insts in
/-- `Straus::multiscalar_mul`: `∑ s_i • P_i` over the scalars and points the two inputs yield,
up to the shorter one (unreduced scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«i686-no-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«i686-no-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«i686-no-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 26 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 26 ⦄ := by
  unfold multiscalar_mul
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  step with hpoints' as ⟨it, hit⟩
  unfold multiscalar_mul_loop0
  apply spec_bind
    («MultiscalarMulStrausEdwardsPointi686-no-tables».multiscalar_mul.lookup_tables_spec
      _ _ it ys hit ps hborrow_points hps hys)
  intro tables htables
  step with hscalars' as ⟨it1, hit1⟩
  unfold multiscalar_mul_loop1
  apply spec_bind
    («MultiscalarMulStrausEdwardsPointi686-no-tables».multiscalar_mul.scalar_digits_spec
      _ _ it1 xs hit1 ss hborrow_scalars hss hxs)
  intro digits hdigits
  step with Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨Q, hQon, hQ, hQb⟩
  step as ⟨iter, hiter⟩
  obtain ⟨hTlen, hT⟩ := forall₂_getElem! htables
  obtain ⟨hDlen, hD⟩ := forall₂_getElem! hdigits
  have hn : min ss.length ps.length = min digits.length tables.length := by
    rw [hTlen, hDlen]
  step with multiscalar_mul_loop2_spec iter tables digits Q (fun k => ps[k]!.toPoint)
    (min ss.length ps.length) hn
    (fun k hk => hT k (by have := min_le_right ss.length ps.length; omega))
    (fun k hk => (hD k (by have := min_le_left ss.length ps.length; omega)).2)
    (by rw [hiter]; rfl) (by rw [hiter]; decide) hQb hQon
    (by
      rw [hQ, hiter]
      exact (Finset.sum_eq_zero fun k _ => by
        rw [show ({ start := 0#usize, «end» := 64#usize } : core.ops.range.Range Usize).end.val
          = 64 from rfl, radix16Tail_sixtyFour, zero_smul]).symm)
    as ⟨r, hron, hrb, hr⟩
  have hzer : ∀ x ∈ digits.val, (Array.Insts.ZeroizeZeroize 64#usize
      (zeroize.Zeroize.Blanket I8.Insts.ZeroizeDefaultIsZeroes)).zeroize x ⦃ _ => True ⦄ :=
    fun x _ => spec_mono (_root_.Array.Insts.ZeroizeZeroize.zeroize_spec (post := fun _ => True) _ x
      fun y _ => spec_mono (I8.Insts.ZeroizeDefaultIsZeroes.zeroize_spec y) fun _ _ => trivial)
      fun _ _ => trivial
  step with alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_spec _ _ hzer as ⟨z, hz⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, sum_zipWith_eq]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [radix16Tail_zero, (hD k (by have := min_le_left ss.length ps.length; omega)).1,
    natCast_zsmul]

end Straus.Insts.«Curve25519_dalekTraitsMultiscalarMulEdwardsPointi686-no-tables»

end

end Curve25519Dalek.backend.serial.scalar_mul.straus
