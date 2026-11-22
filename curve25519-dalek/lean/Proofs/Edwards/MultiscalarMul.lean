/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.ToAeneas.Iterator
public import Proofs.Representation.Scalar
import Proofs.Backend.StrausMultiscalarMul
import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
public section

/-! # `MultiscalarMul for EdwardsPoint`

The patched wrapper collects both inputs into vectors, asserts that they have the same length
and calls `backend::straus_multiscalar_mul` on the vectors. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.EdwardsPoint.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulEdwardsPoint64bit-tables»

/-- `MultiscalarMul::multiscalar_mul` for `EdwardsPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«64bit-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«64bit-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«64bit-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 52)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«64bit-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 52 ⦄ := by
  have hys : ys.length ≤ Usize.max := hlen ▸ hxs
  unfold multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  step with collect.fromIter_spec _ it xs hit hxs as ⟨vs, hvs⟩
  step with hpoints' as ⟨it1, hit1⟩
  step with collect.fromIter_spec _ it1 ys hit1 hys as ⟨vp, hvp⟩
  step
  exact backend.«64bit-tables».straus_multiscalar_mul_spec _ _ _ _ _ _ xs ys ss ps
    (hvs ▸ core.iter.traits.collect.IntoIteratorVec_yields vs)
    (hvp ▸ core.iter.traits.collect.IntoIteratorVec_yields vp)
    hborrow_scalars hborrow_points hss (fun P hP => ⟨hps P hP, hps_on P hP⟩) hxs hys

end «Curve25519_dalekTraitsMultiscalarMulEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«32bit-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulEdwardsPoint32bit-tables»

/-- `MultiscalarMul::multiscalar_mul` for `EdwardsPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«32bit-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«32bit-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«32bit-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 26)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«32bit-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 26 ⦄ := by
  have hys : ys.length ≤ Usize.max := hlen ▸ hxs
  unfold multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  step with collect.fromIter_spec _ it xs hit hxs as ⟨vs, hvs⟩
  step with hpoints' as ⟨it1, hit1⟩
  step with collect.fromIter_spec _ it1 ys hit1 hys as ⟨vp, hvp⟩
  step
  exact backend.«32bit-tables».straus_multiscalar_mul_spec _ _ _ _ _ _ xs ys ss ps
    (hvs ▸ core.iter.traits.collect.IntoIteratorVec_yields vs)
    (hvp ▸ core.iter.traits.collect.IntoIteratorVec_yields vp)
    hborrow_scalars hborrow_points hss (fun P hP => ⟨hps P hP, hps_on P hP⟩) hxs hys

end «Curve25519_dalekTraitsMultiscalarMulEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«64bit-notables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulEdwardsPoint64bit-notables»

/-- `MultiscalarMul::multiscalar_mul` for `EdwardsPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«64bit-notables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«64bit-notables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«64bit-notables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 52)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«64bit-notables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 52 ⦄ := by
  have hys : ys.length ≤ Usize.max := hlen ▸ hxs
  unfold multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  step with collect.fromIter_spec _ it xs hit hxs as ⟨vs, hvs⟩
  step with hpoints' as ⟨it1, hit1⟩
  step with collect.fromIter_spec _ it1 ys hit1 hys as ⟨vp, hvp⟩
  step
  exact backend.«64bit-notables».straus_multiscalar_mul_spec _ _ _ _ _ _ xs ys ss ps
    (hvs ▸ core.iter.traits.collect.IntoIteratorVec_yields vs)
    (hvp ▸ core.iter.traits.collect.IntoIteratorVec_yields vp)
    hborrow_scalars hborrow_points hss (fun P hP => ⟨hps P hP, hps_on P hP⟩) hxs hys

end «Curve25519_dalekTraitsMultiscalarMulEdwardsPoint64bit-notables»
end Curve25519Dalek.edwards.EdwardsPoint.«64bit-notables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«32bit-notables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulEdwardsPoint32bit-notables»

/-- `MultiscalarMul::multiscalar_mul` for `EdwardsPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item edwards.EdwardsPoint.«32bit-notables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List edwards.EdwardsPoint.«32bit-notables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : edwards.EdwardsPoint.«32bit-notables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 26)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : edwards.EdwardsPoint.«32bit-notables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 26 ⦄ := by
  have hys : ys.length ≤ Usize.max := hlen ▸ hxs
  unfold multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  step with collect.fromIter_spec _ it xs hit hxs as ⟨vs, hvs⟩
  step with hpoints' as ⟨it1, hit1⟩
  step with collect.fromIter_spec _ it1 ys hit1 hys as ⟨vp, hvp⟩
  step
  exact backend.«32bit-notables».straus_multiscalar_mul_spec _ _ _ _ _ _ xs ys ss ps
    (hvs ▸ core.iter.traits.collect.IntoIteratorVec_yields vs)
    (hvp ▸ core.iter.traits.collect.IntoIteratorVec_yields vp)
    hborrow_scalars hborrow_points hss (fun P hP => ⟨hps P hP, hps_on P hP⟩) hxs hys

end «Curve25519_dalekTraitsMultiscalarMulEdwardsPoint32bit-notables»
end Curve25519Dalek.edwards.EdwardsPoint.«32bit-notables».Insts


