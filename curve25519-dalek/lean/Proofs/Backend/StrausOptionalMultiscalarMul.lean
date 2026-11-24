module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.ToAeneas.Iterator
public import Proofs.Representation.Scalar
import Proofs.Backend.GetSelectedBackend
import Proofs.Backend.Serial.ScalarMul.Straus.OptionalMultiscalarMul
public section

/-! # `straus_optional_multiscalar_mul` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

namespace «64bit-tables»

open serial.scalar_mul.straus.Straus.Insts in
open «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint64bit-tables» in
/-- `straus_optional_multiscalar_mul`: the serial `Straus::optional_multiscalar_mul`. -/
@[step]
theorem straus_optional_multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«64bit-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«64bit-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max) :
    straus_optional_multiscalar_mul.«64bit-tables» scalarsInst borrowScalarInst pointsInst scalars
      points ⦃ (r : Option edwards.EdwardsPoint.«64bit-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  unfold straus_optional_multiscalar_mul.«64bit-tables»
  step
  exact optional_multiscalar_mul_spec
    _ _ _ _ _ xs ops ss hscalars hpoints hborrow_scalars hss hps hxs hops

end «64bit-tables»

namespace «32bit-tables»

open serial.scalar_mul.straus.Straus.Insts in
open «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint32bit-tables» in
/-- `straus_optional_multiscalar_mul`: the serial `Straus::optional_multiscalar_mul`. -/
@[step]
theorem straus_optional_multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«32bit-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«32bit-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 26 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max) :
    straus_optional_multiscalar_mul.«32bit-tables» scalarsInst borrowScalarInst pointsInst scalars
      points ⦃ (r : Option edwards.EdwardsPoint.«32bit-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  unfold straus_optional_multiscalar_mul.«32bit-tables»
  step
  exact optional_multiscalar_mul_spec
    _ _ _ _ _ xs ops ss hscalars hpoints hborrow_scalars hss hps hxs hops

end «32bit-tables»

namespace «64bit-notables»

open serial.scalar_mul.straus.Straus.Insts in
open «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint64bit-notables» in
/-- `straus_optional_multiscalar_mul`: the serial `Straus::optional_multiscalar_mul`. -/
@[step]
theorem straus_optional_multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«64bit-notables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«64bit-notables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max) :
    straus_optional_multiscalar_mul.«64bit-notables» scalarsInst borrowScalarInst pointsInst
        scalars
      points ⦃ (r : Option edwards.EdwardsPoint.«64bit-notables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  unfold straus_optional_multiscalar_mul.«64bit-notables»
  step
  exact optional_multiscalar_mul_spec
    _ _ _ _ _ xs ops ss hscalars hpoints hborrow_scalars hss hps hxs hops

end «64bit-notables»

namespace «32bit-notables»

open serial.scalar_mul.straus.Straus.Insts in
open «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint32bit-notables» in
/-- `straus_optional_multiscalar_mul`: the serial `Straus::optional_multiscalar_mul`. -/
@[step]
theorem straus_optional_multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«32bit-notables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«32bit-notables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 26 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max) :
    straus_optional_multiscalar_mul.«32bit-notables» scalarsInst borrowScalarInst pointsInst
        scalars
      points ⦃ (r : Option edwards.EdwardsPoint.«32bit-notables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  unfold straus_optional_multiscalar_mul.«32bit-notables»
  step
  exact optional_multiscalar_mul_spec
    _ _ _ _ _ xs ops ss hscalars hpoints hborrow_scalars hss hps hxs hops

end «32bit-notables»

end Curve25519Dalek.backend
