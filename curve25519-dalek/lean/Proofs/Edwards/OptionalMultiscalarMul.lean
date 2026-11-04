/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Iterator
public import Defs.Scalar
import Proofs.Backend.PippengerOptionalMultiscalarMul
import Proofs.Backend.StrausOptionalMultiscalarMul
import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
public section

/-! # `VartimeMultiscalarMul for EdwardsPoint`

The patched wrapper collects both inputs into vectors, asserts that they have the same length and
calls `backend::straus_optional_multiscalar_mul` (fewer than `190` pairs) or
`backend::pippenger_optional_multiscalar_mul` on the vectors; both compute the same sum. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `EdwardsPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; Straus below `190` points, Pippenger from `190` on; unreduced scalars
`< 2^255`); limbs `< 2^52`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
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
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  unfold optional_multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  step with collect.fromIter_spec _ it xs hit hxs as ⟨vs, hvs⟩
  step with hpoints' as ⟨it1, hit1⟩
  step with collect.fromIter_spec _ it1 ops hit1 hops as ⟨vp, hvp⟩
  step
  have hys : (core.iter.traits.collect.IntoIteratorVec Clause0_Item).Yields vs xs :=
    hvs ▸ core.iter.traits.collect.IntoIteratorVec_yields vs
  have hyp : (core.iter.traits.collect.IntoIteratorVec
      (Option edwards.EdwardsPoint.«x86_64-tables»)).Yields vp ops :=
    hvp ▸ core.iter.traits.collect.IntoIteratorVec_yields vp
  split
  · exact backend.«x86_64-tables».straus_optional_multiscalar_mul_spec _ _ _ _ _ xs ops ss hys hyp
      hborrow_scalars hss hps hxs hops
  · apply spec_mono
      (backend.«x86_64-tables».pippenger_optional_multiscalar_mul_spec _ _ _ _ _ xs ops ss
      hys hyp hborrow_scalars hss hps hxs)
    rintro r ⟨hnone, hsome⟩
    rw [List.take_of_length_le (by rw [← hborrow_scalars.length_eq, hlen])] at hnone
    exact ⟨hnone, hsome⟩

end «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts
namespace «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-tables»

/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `EdwardsPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; Straus below `190` points, Pippenger from `190` on; unreduced scalars
`< 2^255`); limbs `< 2^26`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
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
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«i686-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  unfold optional_multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  step with collect.fromIter_spec _ it xs hit hxs as ⟨vs, hvs⟩
  step with hpoints' as ⟨it1, hit1⟩
  step with collect.fromIter_spec _ it1 ops hit1 hops as ⟨vp, hvp⟩
  step
  have hys : (core.iter.traits.collect.IntoIteratorVec Clause0_Item).Yields vs xs :=
    hvs ▸ core.iter.traits.collect.IntoIteratorVec_yields vs
  have hyp : (core.iter.traits.collect.IntoIteratorVec
      (Option edwards.EdwardsPoint.«i686-tables»)).Yields vp ops :=
    hvp ▸ core.iter.traits.collect.IntoIteratorVec_yields vp
  split
  · exact backend.«i686-tables».straus_optional_multiscalar_mul_spec _ _ _ _ _ xs ops ss hys hyp
      hborrow_scalars hss hps hxs hops
  · apply spec_mono
      (backend.«i686-tables».pippenger_optional_multiscalar_mul_spec _ _ _ _ _ xs ops ss
      hys hyp hborrow_scalars hss hps hxs)
    rintro r ⟨hnone, hsome⟩
    rw [List.take_of_length_le (by rw [← hborrow_scalars.length_eq, hlen])] at hnone
    exact ⟨hnone, hsome⟩

end «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `EdwardsPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; Straus below `190` points, Pippenger from `190` on; unreduced scalars
`< 2^255`); limbs `< 2^52`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
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
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-no-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  unfold optional_multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  step with collect.fromIter_spec _ it xs hit hxs as ⟨vs, hvs⟩
  step with hpoints' as ⟨it1, hit1⟩
  step with collect.fromIter_spec _ it1 ops hit1 hops as ⟨vp, hvp⟩
  step
  have hys : (core.iter.traits.collect.IntoIteratorVec Clause0_Item).Yields vs xs :=
    hvs ▸ core.iter.traits.collect.IntoIteratorVec_yields vs
  have hyp : (core.iter.traits.collect.IntoIteratorVec
      (Option edwards.EdwardsPoint.«x86_64-no-tables»)).Yields vp ops :=
    hvp ▸ core.iter.traits.collect.IntoIteratorVec_yields vp
  split
  · exact backend.«x86_64-no-tables».straus_optional_multiscalar_mul_spec _ _ _ _ _ xs ops ss hys
      hyp
      hborrow_scalars hss hps hxs hops
  · apply spec_mono
      (backend.«x86_64-no-tables».pippenger_optional_multiscalar_mul_spec _ _ _ _ _ xs ops ss
      hys hyp hborrow_scalars hss hps hxs)
    rintro r ⟨hnone, hsome⟩
    rw [List.take_of_length_le (by rw [← hborrow_scalars.length_eq, hlen])] at hnone
    exact ⟨hnone, hsome⟩

end «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-no-tables»

/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `EdwardsPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; Straus below `190` points, Pippenger from `190` on; unreduced scalars
`< 2^255`); limbs `< 2^26`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
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
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«i686-no-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  unfold optional_multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  step with collect.fromIter_spec _ it xs hit hxs as ⟨vs, hvs⟩
  step with hpoints' as ⟨it1, hit1⟩
  step with collect.fromIter_spec _ it1 ops hit1 hops as ⟨vp, hvp⟩
  step
  have hys : (core.iter.traits.collect.IntoIteratorVec Clause0_Item).Yields vs xs :=
    hvs ▸ core.iter.traits.collect.IntoIteratorVec_yields vs
  have hyp : (core.iter.traits.collect.IntoIteratorVec
      (Option edwards.EdwardsPoint.«i686-no-tables»)).Yields vp ops :=
    hvp ▸ core.iter.traits.collect.IntoIteratorVec_yields vp
  split
  · exact backend.«i686-no-tables».straus_optional_multiscalar_mul_spec _ _ _ _ _ xs ops ss hys
      hyp
      hborrow_scalars hss hps hxs hops
  · apply spec_mono
      (backend.«i686-no-tables».pippenger_optional_multiscalar_mul_spec _ _ _ _ _ xs ops ss
      hys hyp hborrow_scalars hss hps hxs)
    rintro r ⟨hnone, hsome⟩
    rw [List.take_of_length_le (by rw [← hborrow_scalars.length_eq, hlen])] at hnone
    exact ⟨hnone, hsome⟩

end «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.EdwardsPoint.«i686-no-tables».Insts


