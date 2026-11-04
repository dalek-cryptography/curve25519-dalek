/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Iterator
public import Defs.Scalar
import Proofs.Backend.GetSelectedBackend
import Proofs.Backend.Serial.ScalarMul.Straus.OptionalMultiscalarMul
public section

/-! # `straus_optional_multiscalar_mul` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

namespace «x86_64-tables»

open serial.scalar_mul.straus.Straus.Insts in
open «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables» in
/-- `straus_optional_multiscalar_mul`: the serial `Straus::optional_multiscalar_mul`. -/
@[step]
theorem straus_optional_multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«x86_64-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«x86_64-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max) :
    straus_optional_multiscalar_mul.«x86_64-tables» scalarsInst borrowScalarInst pointsInst scalars
      points ⦃ (r : Option edwards.EdwardsPoint.«x86_64-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  unfold straus_optional_multiscalar_mul.«x86_64-tables»
  step
  exact optional_multiscalar_mul_spec
    _ _ _ _ _ xs ops ss hscalars hpoints hborrow_scalars hss hps hxs hops

end «x86_64-tables»

namespace «i686-tables»

open serial.scalar_mul.straus.Straus.Insts in
open «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-tables» in
/-- `straus_optional_multiscalar_mul`: the serial `Straus::optional_multiscalar_mul`. -/
@[step]
theorem straus_optional_multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«i686-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«i686-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 26 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max) :
    straus_optional_multiscalar_mul.«i686-tables» scalarsInst borrowScalarInst pointsInst scalars
      points ⦃ (r : Option edwards.EdwardsPoint.«i686-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  unfold straus_optional_multiscalar_mul.«i686-tables»
  step
  exact optional_multiscalar_mul_spec
    _ _ _ _ _ xs ops ss hscalars hpoints hborrow_scalars hss hps hxs hops

end «i686-tables»

namespace «x86_64-no-tables»

open serial.scalar_mul.straus.Straus.Insts in
open «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables» in
/-- `straus_optional_multiscalar_mul`: the serial `Straus::optional_multiscalar_mul`. -/
@[step]
theorem straus_optional_multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«x86_64-no-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«x86_64-no-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max) :
    straus_optional_multiscalar_mul.«x86_64-no-tables» scalarsInst borrowScalarInst pointsInst
        scalars
      points ⦃ (r : Option edwards.EdwardsPoint.«x86_64-no-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  unfold straus_optional_multiscalar_mul.«x86_64-no-tables»
  step
  exact optional_multiscalar_mul_spec
    _ _ _ _ _ xs ops ss hscalars hpoints hborrow_scalars hss hps hxs hops

end «x86_64-no-tables»

namespace «i686-no-tables»

open serial.scalar_mul.straus.Straus.Insts in
open «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-no-tables» in
/-- `straus_optional_multiscalar_mul`: the serial `Straus::optional_multiscalar_mul`. -/
@[step]
theorem straus_optional_multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«i686-no-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«i686-no-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 26 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max) :
    straus_optional_multiscalar_mul.«i686-no-tables» scalarsInst borrowScalarInst pointsInst
        scalars
      points ⦃ (r : Option edwards.EdwardsPoint.«i686-no-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  unfold straus_optional_multiscalar_mul.«i686-no-tables»
  step
  exact optional_multiscalar_mul_spec
    _ _ _ _ _ xs ops ss hscalars hpoints hborrow_scalars hss hps hxs hops

end «i686-no-tables»

end Curve25519Dalek.backend
