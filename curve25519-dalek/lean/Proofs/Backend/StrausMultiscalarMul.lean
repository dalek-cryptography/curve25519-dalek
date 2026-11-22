/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.ToAeneas.Iterator
public import Proofs.Representation.Scalar
import Proofs.Backend.GetSelectedBackend
import Proofs.Backend.Serial.ScalarMul.Straus.MultiscalarMul
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

namespace «64bit-tables»

open serial.scalar_mul.straus.Straus.Insts in
/-- `straus_multiscalar_mul`: the serial `Straus::multiscalar_mul`, `∑ s_i • P_i` up to the
shorter input; limbs `< 2^52`. -/
@[step]
theorem straus_multiscalar_mul_spec
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
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max) :
    straus_multiscalar_mul.«64bit-tables» scalarsInst borrowScalarInst pointsInst borrowPointInst
      scalars points ⦃ (r : edwards.EdwardsPoint.«64bit-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 52 ⦄ := by
  unfold straus_multiscalar_mul.«64bit-tables»
  step
  exact «Curve25519_dalekTraitsMultiscalarMulEdwardsPoint64bit-tables».multiscalar_mul_spec
    _ _ _ _ _ _ xs ys ss ps hscalars hpoints hborrow_scalars hborrow_points hss hps hxs hys

end «64bit-tables»

namespace «32bit-tables»

open serial.scalar_mul.straus.Straus.Insts in
/-- `straus_multiscalar_mul`: the serial `Straus::multiscalar_mul`, `∑ s_i • P_i` up to the
shorter input; limbs `< 2^26`. -/
@[step]
theorem straus_multiscalar_mul_spec
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
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 26 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max) :
    straus_multiscalar_mul.«32bit-tables» scalarsInst borrowScalarInst pointsInst borrowPointInst
      scalars points ⦃ (r : edwards.EdwardsPoint.«32bit-tables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 26 ⦄ := by
  unfold straus_multiscalar_mul.«32bit-tables»
  step
  exact «Curve25519_dalekTraitsMultiscalarMulEdwardsPoint32bit-tables».multiscalar_mul_spec
    _ _ _ _ _ _ xs ys ss ps hscalars hpoints hborrow_scalars hborrow_points hss hps hxs hys

end «32bit-tables»

namespace «64bit-notables»

open serial.scalar_mul.straus.Straus.Insts in
/-- `straus_multiscalar_mul`: the serial `Straus::multiscalar_mul`, `∑ s_i • P_i` up to the
shorter input; limbs `< 2^52`. -/
@[step]
theorem straus_multiscalar_mul_spec
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
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max) :
    straus_multiscalar_mul.«64bit-notables» scalarsInst borrowScalarInst pointsInst
        borrowPointInst
      scalars points ⦃ (r : edwards.EdwardsPoint.«64bit-notables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 52 ⦄ := by
  unfold straus_multiscalar_mul.«64bit-notables»
  step
  exact «Curve25519_dalekTraitsMultiscalarMulEdwardsPoint64bit-notables».multiscalar_mul_spec
    _ _ _ _ _ _ xs ys ss ps hscalars hpoints hborrow_scalars hborrow_points hss hps hxs hys

end «64bit-notables»

namespace «32bit-notables»

open serial.scalar_mul.straus.Straus.Insts in
/-- `straus_multiscalar_mul`: the serial `Straus::multiscalar_mul`, `∑ s_i • P_i` up to the
shorter input; limbs `< 2^26`. -/
@[step]
theorem straus_multiscalar_mul_spec
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
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 26 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max) :
    straus_multiscalar_mul.«32bit-notables» scalarsInst borrowScalarInst pointsInst
        borrowPointInst
      scalars points ⦃ (r : edwards.EdwardsPoint.«32bit-notables») => r.OnCurve ∧
        r.toPoint = (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧ r.LimbsLt 26 ⦄ := by
  unfold straus_multiscalar_mul.«32bit-notables»
  step
  exact «Curve25519_dalekTraitsMultiscalarMulEdwardsPoint32bit-notables».multiscalar_mul_spec
    _ _ _ _ _ _ xs ys ss ps hscalars hpoints hborrow_scalars hborrow_points hss hps hxs hys

end «32bit-notables»

end Curve25519Dalek.backend
