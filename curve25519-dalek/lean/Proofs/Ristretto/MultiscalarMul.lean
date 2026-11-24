module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.ToAeneas.Iterator
public import Proofs.Representation.Scalar
import Proofs.Edwards.MultiscalarMul
import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
public section

/-! # `MultiscalarMul for RistrettoPoint`

The patched wrapper collects the borrowed points into a vector and calls the Edwards
`multiscalar_mul` on it, with `Borrow::borrow` of the vector entries. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.ristretto.RistrettoPoint.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulRistrettoPoint64bit-tables»

open edwards.EdwardsPoint.«64bit-tables».Insts in
/-- `MultiscalarMul::multiscalar_mul` for `RistrettoPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item ristretto.RistrettoPoint.«64bit-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List ristretto.RistrettoPoint.«64bit-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«64bit-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 52)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») => r.OnCurve ∧
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
    «Curve25519_dalekTraitsMultiscalarMulEdwardsPoint64bit-tables».multiscalar_mul_spec _ _
      (core.iter.traits.collect.IntoIteratorVec _) (core.borrow.Borrow.Blanket _) scalars v
      xs v.val ss ps hscalars (core.iter.traits.collect.IntoIteratorVec_yields v)
      hborrow_scalars (by rw [hv]; exact List.forall₂_same.mpr fun P _ =>
        core.borrow.Borrow.Blanket.borrow_spec P) hss hps hps_on hxs
      (by rw [hv, ← hpsys]; exact hlen) as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «Curve25519_dalekTraitsMultiscalarMulRistrettoPoint64bit-tables»
end Curve25519Dalek.ristretto.RistrettoPoint.«64bit-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«32bit-tables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulRistrettoPoint32bit-tables»

open edwards.EdwardsPoint.«32bit-tables».Insts in
/-- `MultiscalarMul::multiscalar_mul` for `RistrettoPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item ristretto.RistrettoPoint.«32bit-tables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List ristretto.RistrettoPoint.«32bit-tables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«32bit-tables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 26)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») => r.OnCurve ∧
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
    «Curve25519_dalekTraitsMultiscalarMulEdwardsPoint32bit-tables».multiscalar_mul_spec _ _
      (core.iter.traits.collect.IntoIteratorVec _) (core.borrow.Borrow.Blanket _) scalars v
      xs v.val ss ps hscalars (core.iter.traits.collect.IntoIteratorVec_yields v)
      hborrow_scalars (by rw [hv]; exact List.forall₂_same.mpr fun P _ =>
        core.borrow.Borrow.Blanket.borrow_spec P) hss hps hps_on hxs
      (by rw [hv, ← hpsys]; exact hlen) as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «Curve25519_dalekTraitsMultiscalarMulRistrettoPoint32bit-tables»
end Curve25519Dalek.ristretto.RistrettoPoint.«32bit-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«64bit-notables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulRistrettoPoint64bit-notables»

open edwards.EdwardsPoint.«64bit-notables».Insts in
/-- `MultiscalarMul::multiscalar_mul` for `RistrettoPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item ristretto.RistrettoPoint.«64bit-notables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List ristretto.RistrettoPoint.«64bit-notables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«64bit-notables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 52)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») => r.OnCurve ∧
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
    «Curve25519_dalekTraitsMultiscalarMulEdwardsPoint64bit-notables».multiscalar_mul_spec _ _
      (core.iter.traits.collect.IntoIteratorVec _) (core.borrow.Borrow.Blanket _) scalars v
      xs v.val ss ps hscalars (core.iter.traits.collect.IntoIteratorVec_yields v)
      hborrow_scalars (by rw [hv]; exact List.forall₂_same.mpr fun P _ =>
        core.borrow.Borrow.Blanket.borrow_spec P) hss hps hps_on hxs
      (by rw [hv, ← hpsys]; exact hlen) as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «Curve25519_dalekTraitsMultiscalarMulRistrettoPoint64bit-notables»
end Curve25519Dalek.ristretto.RistrettoPoint.«64bit-notables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«32bit-notables».Insts
namespace «Curve25519_dalekTraitsMultiscalarMulRistrettoPoint32bit-notables»

open edwards.EdwardsPoint.«32bit-notables».Insts in
/-- `MultiscalarMul::multiscalar_mul` for `RistrettoPoint`: `∑ s_i • P_i` over the scalars and
points the two inputs yield, which must be equally many (the patched `assert_eq!`; unreduced
scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem multiscalar_mul_spec
    {I J Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowPointInst : core.borrow.Borrow Clause2_Item ristretto.RistrettoPoint.«32bit-notables»)
    (scalars : I) (points : J) (xs : List Clause0_Item) (ys : List Clause2_Item)
    (ss : List scalar.Scalar) (ps : List ristretto.RistrettoPoint.«32bit-notables»)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ys)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_points : List.Forall₂
      (fun y P => borrowPointInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«32bit-notables») => P' = P ⦄)
      ys ps)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P ∈ ps, P.LimbsLt 26)
    (hps_on : ∀ P ∈ ps, P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ys.length) :
    multiscalar_mul scalarsInst borrowScalarInst pointsInst borrowPointInst scalars points
      ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») => r.OnCurve ∧
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
    «Curve25519_dalekTraitsMultiscalarMulEdwardsPoint32bit-notables».multiscalar_mul_spec _ _
      (core.iter.traits.collect.IntoIteratorVec _) (core.borrow.Borrow.Blanket _) scalars v
      xs v.val ss ps hscalars (core.iter.traits.collect.IntoIteratorVec_yields v)
      hborrow_scalars (by rw [hv]; exact List.forall₂_same.mpr fun P _ =>
        core.borrow.Borrow.Blanket.borrow_spec P) hss hps hps_on hxs
      (by rw [hv, ← hpsys]; exact hlen) as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «Curve25519_dalekTraitsMultiscalarMulRistrettoPoint32bit-notables»
end Curve25519Dalek.ristretto.RistrettoPoint.«32bit-notables».Insts
