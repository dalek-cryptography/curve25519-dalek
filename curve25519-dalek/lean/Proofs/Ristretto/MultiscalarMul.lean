/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import ToAeneas.Iterator
public import Defs.Scalar
import Proofs.Edwards.MultiscalarMul
import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
public section

/-! # `MultiscalarMul for RistrettoPoint`

The patched wrapper collects the borrowed points into a vector and calls the Edwards
`multiscalar_mul` on it, with `Borrow::borrow` of the vector entries. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulRistrettoPointx86_64-tables»

open edwards.EdwardsPoint.«x86_64-tables».Insts in
/-- `MultiscalarMul::multiscalar_mul` for `RistrettoPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item ristretto.RistrettoPoint.«x86_64-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List ristretto.RistrettoPoint.«x86_64-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«x86_64-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 52)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 52 ⦄ := by
  have hys : ys.length ≤ Usize.max := hlen ▸ hxs
  unfold multiscalar_mul
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  step with hpoints' as ⟨it, hit⟩
  unfold multiscalar_mul_loop
  have hpsys := hborrow_points.length_eq
  apply spec_bind (collect.collectApplyLoop_spec _ borrowPointInst.borrow it ys hit ps
    hborrow_points (alloc.vec.Vec.new _) (by simpa using hys))
  intro v hv
  replace hv : v.val = ps := by rw [hv]; rfl
  step with
    «Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-tables».multiscalar_mul_spec _ _
      (core.iter.traits.collect.IntoIteratorVec _) (core.borrow.Borrow.Blanket _) scalars v
      xs v.val ss ps hscalars (core.iter.traits.collect.IntoIteratorVec_yields v)
      hborrow_scalars (by rw [hv]; exact List.forall₂_same.mpr fun P _ =>
        core.borrow.Borrow.Blanket.borrow_spec P) hss hps hps_on hxs
      (by rw [hv, ← hpsys]; exact hlen) as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «Curve25519_dalekTraitsMultiscalarMulRistrettoPointx86_64-tables»
end Curve25519Dalek.ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«i686-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulRistrettoPointi686-tables»

open edwards.EdwardsPoint.«i686-tables».Insts in
/-- `MultiscalarMul::multiscalar_mul` for `RistrettoPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item ristretto.RistrettoPoint.«i686-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List ristretto.RistrettoPoint.«i686-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«i686-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 26)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : ristretto.RistrettoPoint.«i686-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 26 ⦄ := by
  have hys : ys.length ≤ Usize.max := hlen ▸ hxs
  unfold multiscalar_mul
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  step with hpoints' as ⟨it, hit⟩
  unfold multiscalar_mul_loop
  have hpsys := hborrow_points.length_eq
  apply spec_bind (collect.collectApplyLoop_spec _ borrowPointInst.borrow it ys hit ps
    hborrow_points (alloc.vec.Vec.new _) (by simpa using hys))
  intro v hv
  replace hv : v.val = ps := by rw [hv]; rfl
  step with
    «Curve25519_dalekTraitsMultiscalarMulEdwardsPointi686-tables».multiscalar_mul_spec _ _
      (core.iter.traits.collect.IntoIteratorVec _) (core.borrow.Borrow.Blanket _) scalars v
      xs v.val ss ps hscalars (core.iter.traits.collect.IntoIteratorVec_yields v)
      hborrow_scalars (by rw [hv]; exact List.forall₂_same.mpr fun P _ =>
        core.borrow.Borrow.Blanket.borrow_spec P) hss hps hps_on hxs
      (by rw [hv, ← hpsys]; exact hlen) as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «Curve25519_dalekTraitsMultiscalarMulRistrettoPointi686-tables»
end Curve25519Dalek.ristretto.RistrettoPoint.«i686-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulRistrettoPointx86_64-no-tables»

open edwards.EdwardsPoint.«x86_64-no-tables».Insts in
/-- `MultiscalarMul::multiscalar_mul` for `RistrettoPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item ristretto.RistrettoPoint.«x86_64-no-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«x86_64-no-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 52)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 52 ⦄ := by
  have hys : ys.length ≤ Usize.max := hlen ▸ hxs
  unfold multiscalar_mul
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  step with hpoints' as ⟨it, hit⟩
  unfold multiscalar_mul_loop
  have hpsys := hborrow_points.length_eq
  apply spec_bind (collect.collectApplyLoop_spec _ borrowPointInst.borrow it ys hit ps
    hborrow_points (alloc.vec.Vec.new _) (by simpa using hys))
  intro v hv
  replace hv : v.val = ps := by rw [hv]; rfl
  step with
    «Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-no-tables».multiscalar_mul_spec _ _
      (core.iter.traits.collect.IntoIteratorVec _) (core.borrow.Borrow.Blanket _) scalars v
      xs v.val ss ps hscalars (core.iter.traits.collect.IntoIteratorVec_yields v)
      hborrow_scalars (by rw [hv]; exact List.forall₂_same.mpr fun P _ =>
        core.borrow.Borrow.Blanket.borrow_spec P) hss hps hps_on hxs
      (by rw [hv, ← hpsys]; exact hlen) as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «Curve25519_dalekTraitsMultiscalarMulRistrettoPointx86_64-no-tables»
end Curve25519Dalek.ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulRistrettoPointi686-no-tables»

open edwards.EdwardsPoint.«i686-no-tables».Insts in
/-- `MultiscalarMul::multiscalar_mul` for `RistrettoPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item ristretto.RistrettoPoint.«i686-no-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List ristretto.RistrettoPoint.«i686-no-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«i686-no-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 26)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 26 ⦄ := by
  have hys : ys.length ≤ Usize.max := hlen ▸ hxs
  unfold multiscalar_mul
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  step with hpoints' as ⟨it, hit⟩
  unfold multiscalar_mul_loop
  have hpsys := hborrow_points.length_eq
  apply spec_bind (collect.collectApplyLoop_spec _ borrowPointInst.borrow it ys hit ps
    hborrow_points (alloc.vec.Vec.new _) (by simpa using hys))
  intro v hv
  replace hv : v.val = ps := by rw [hv]; rfl
  step with
    «Curve25519_dalekTraitsMultiscalarMulEdwardsPointi686-no-tables».multiscalar_mul_spec _ _
      (core.iter.traits.collect.IntoIteratorVec _) (core.borrow.Borrow.Blanket _) scalars v
      xs v.val ss ps hscalars (core.iter.traits.collect.IntoIteratorVec_yields v)
      hborrow_scalars (by rw [hv]; exact List.forall₂_same.mpr fun P _ =>
        core.borrow.Borrow.Blanket.borrow_spec P) hss hps hps_on hxs
      (by rw [hv, ← hpsys]; exact hlen) as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «Curve25519_dalekTraitsMultiscalarMulRistrettoPointi686-no-tables»
end Curve25519Dalek.ristretto.RistrettoPoint.«i686-no-tables».Insts
