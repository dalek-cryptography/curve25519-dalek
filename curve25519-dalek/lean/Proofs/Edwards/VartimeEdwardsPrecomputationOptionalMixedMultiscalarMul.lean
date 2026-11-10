/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import ToAeneas.Iterator
public import Defs.Scalar
public import Defs.ScalarMul
import Proofs.Backend.VartimePrecomputedStrausOptionalMixedMultiscalarMul
import Proofs.Helpers.Optional
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeEdwardsPrecomputation` (static points `ps`): `none` iff some dynamic point is `none`;
otherwise `∑ s_i • ps_i + ∑ d_i • Q_i` (at most `|ps|` static scalars, the missing ones count
as `0`; as many dynamic scalars as dynamic points; unreduced scalars `< 2^255`); limbs
`< 2^52`. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«x86_64-tables») Clause4_IntoIter)
    (self : VartimeEdwardsPrecomputation.«x86_64-tables») (static_scalars : I) (dynamic_scalars : J)
    (dynamic_points : K) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«x86_64-tables»))
    (hself : self.IsValid) (hself_b : self.LimbsLt 54)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 52)
    (hqs_on : ∀ Q, some Q ∈ qops → Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ self.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-tables») => (none ∈ qops → r = none) ∧
        ∀ qs, qops = qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds qs).sum ∧
          R.LimbsLt 52 ⦄ := by
  apply spec_some_of_filterMap
  unfold optional_mixed_multiscalar_mul
  exact backend.«VartimePrecomputedStrausx86_64-tables».optional_mixed_multiscalar_mul_spec
    _ _ _ _ _ self _ _ _ xs ss ys ds qops hself hself_b hstatic_scalars hdynamic_scalars
    hdynamic_points hborrow_static hborrow_dynamic hss hds
    (fun Q hQ => ⟨hqs Q hQ, hqs_on Q hQ⟩) hxs hys hqops hstatic hdynamic

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»

/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeEdwardsPrecomputation` (static points `ps`): `none` iff some dynamic point is `none`;
otherwise `∑ s_i • ps_i + ∑ d_i • Q_i` (at most `|ps|` static scalars, the missing ones count
as `0`; as many dynamic scalars as dynamic points; unreduced scalars `< 2^255`); limbs
`< 2^26`. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«i686-tables») Clause4_IntoIter)
    (self : VartimeEdwardsPrecomputation.«i686-tables») (static_scalars : I) (dynamic_scalars : J)
    (dynamic_points : K) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«i686-tables»))
    (hself : self.IsValid) (hself_b : self.LimbsLt 27)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 26)
    (hqs_on : ∀ Q, some Q ∈ qops → Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ self.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«i686-tables») => (none ∈ qops → r = none) ∧
        ∀ qs, qops = qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds qs).sum ∧
          R.LimbsLt 26 ⦄ := by
  apply spec_some_of_filterMap
  unfold optional_mixed_multiscalar_mul
  exact backend.«VartimePrecomputedStrausi686-tables».optional_mixed_multiscalar_mul_spec
    _ _ _ _ _ self _ _ _ xs ss ys ds qops hself hself_b hstatic_scalars hdynamic_scalars
    hdynamic_points hborrow_static hborrow_dynamic hss hds
    (fun Q hQ => ⟨hqs Q hQ, hqs_on Q hQ⟩) hxs hys hqops hstatic hdynamic

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeEdwardsPrecomputation` (static points `ps`): `none` iff some dynamic point is `none`;
otherwise `∑ s_i • ps_i + ∑ d_i • Q_i` (at most `|ps|` static scalars, the missing ones count
as `0`; as many dynamic scalars as dynamic points; unreduced scalars `< 2^255`); limbs
`< 2^52`. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«x86_64-no-tables») Clause4_IntoIter)
    (self : VartimeEdwardsPrecomputation.«x86_64-no-tables») (static_scalars : I)
        (dynamic_scalars : J)
    (dynamic_points : K) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«x86_64-no-tables»))
    (hself : self.IsValid) (hself_b : self.LimbsLt 54)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 52)
    (hqs_on : ∀ Q, some Q ∈ qops → Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ self.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«x86_64-no-tables») => (none ∈ qops → r = none) ∧
        ∀ qs, qops = qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds qs).sum ∧
          R.LimbsLt 52 ⦄ := by
  apply spec_some_of_filterMap
  unfold optional_mixed_multiscalar_mul
  exact backend.«VartimePrecomputedStrausx86_64-no-tables».optional_mixed_multiscalar_mul_spec
    _ _ _ _ _ self _ _ _ xs ss ys ds qops hself hself_b hstatic_scalars hdynamic_scalars
    hdynamic_points hborrow_static hborrow_dynamic hss hds
    (fun Q hQ => ⟨hqs Q hQ, hqs_on Q hQ⟩) hxs hys hqops hstatic hdynamic

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»

/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeEdwardsPrecomputation` (static points `ps`): `none` iff some dynamic point is `none`;
otherwise `∑ s_i • ps_i + ∑ d_i • Q_i` (at most `|ps|` static scalars, the missing ones count
as `0`; as many dynamic scalars as dynamic points; unreduced scalars `< 2^255`); limbs
`< 2^26`. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«i686-no-tables») Clause4_IntoIter)
    (self : VartimeEdwardsPrecomputation.«i686-no-tables») (static_scalars : I)
        (dynamic_scalars : J)
    (dynamic_points : K) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«i686-no-tables»))
    (hself : self.IsValid) (hself_b : self.LimbsLt 27)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 26)
    (hqs_on : ∀ Q, some Q ∈ qops → Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ self.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«i686-no-tables») => (none ∈ qops → r = none) ∧
        ∀ qs, qops = qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds qs).sum ∧
          R.LimbsLt 26 ⦄ := by
  apply spec_some_of_filterMap
  unfold optional_mixed_multiscalar_mul
  exact backend.«VartimePrecomputedStrausi686-no-tables».optional_mixed_multiscalar_mul_spec
    _ _ _ _ _ self _ _ _ xs ss ys ds qops hself hself_b hstatic_scalars hdynamic_scalars
    hdynamic_points hborrow_static hborrow_dynamic hss hds
    (fun Q hQ => ⟨hqs Q hQ, hqs_on Q hQ⟩) hxs hys hqops hstatic hdynamic

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-no-tables».Insts


