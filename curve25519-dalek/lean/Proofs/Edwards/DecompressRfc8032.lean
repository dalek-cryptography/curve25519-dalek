module
public import Curve25519Dalek.Funs
public import Proofs.Edwards.Decompress
public import Proofs.Edwards.Affine.Compress
public import Proofs.Edwards.CompressedEq
public import Proofs.Edwards.IsIdentity
public import Proofs.Edwards.IsTorsionFree
public import Proofs.Field.Eq
public import Proofs.Backend.Serial.U64.Field.One
public import Proofs.Backend.Serial.U32.Field.One
import Proofs.Helpers.Coords
import Proofs.Helpers.AsNat
import Proofs.Helpers.ToField
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards

namespace CompressedEdwardsY.«64bit-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

theorem decompress_rfc8032_spec (self : CompressedEdwardsY) :
    decompress_rfc8032.«64bit-tables» self ⦃ (r : Option (EdwardsPoint.«64bit-tables»)) =>
      r.map EdwardsPoint.«64bit-tables».toPoint =
        (decodeLenient self.toVector).filter (fun P => decide (encode P = self.toVector)) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 52 ⦄ := by
  unfold decompress_rfc8032.«64bit-tables»
  step with spec_and (decompress_spec self) (decompress_Z_spec self) as ⟨o, hmap, hq, hZ⟩
  rcases o with _ | ep
  · simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
    simp only [bind_ok, spec_ok, Option.map_none, reduceCtorEq, IsEmpty.forall_iff, implies_true,
      and_true]
    rw [← hmap]
    rfl
  · obtain ⟨hon, hb⟩ := hq ep rfl
    have hZ1 := hZ ep rfl
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    simp only [bind_ok]
    step with ONE_spec as ⟨fe, hfe, hfeb⟩
    step as ⟨b, hbe⟩
    have hbt : b = true := hbe.mpr (by
      rw [hfe]; exact toField_eq_natCast_iff.mp (by rw [hZ1]; simp))
    simp only [hbt, massert, ite_true]
    have hx : ep.toPoint.x = ep.X.toField := by
      rw [EdwardsPoint.«64bit-tables».toPoint_x hon, hZ1, div_one]
    have hy : ep.toPoint.y = ep.Y.toField := by
      rw [EdwardsPoint.«64bit-tables».toPoint_y hon, hZ1, div_one]
    have haon : (⟨ep.X, ep.Y⟩ : affine.AffinePoint.«64bit-tables»).OnCurve := by
      change curve25519.edwards.Equation ep.X.toField ep.Y.toField
      rw [← hx, ← hy]
      exact ep.toPoint.equation
    have hapt : (⟨ep.X, ep.Y⟩ : affine.AffinePoint.«64bit-tables»).toPoint = ep.toPoint := by
      simp only [affine.AffinePoint.«64bit-tables».toPoint_def, haon, ↓reduceDIte]
      ext
      · exact hx.symm
      · exact hy.symm
    step with affine.«AffinePoint64bit-tables».compress_spec _ haon as ⟨repr, hrepr⟩
    rw [hapt] at hrepr
    step as ⟨b1, hb1⟩
    have key : b1 = true ↔ encode ep.toPoint = self.toVector := by
      rw [hb1, eq_comm (a := encode _), CompressedEdwardsY.toVector_eq_encode_iff, ← hrepr]
      constructor
      · rintro rfl; rfl
      · intro h
        apply Aeneas.Std.Array.eq_of_asNat_eq
        rw [CompressedEdwardsY.asNat_def, CompressedEdwardsY.asNat_def] at h
        exact h.symm
    simp only [core.bool.Bool.then_some, spec_ok]
    rw [← hmap, Option.map_some, Option.filter_some]
    by_cases h : b1 = true
    · simp only [h, ite_true, Option.map_some, (key.mp h), decide_true]
      exact ⟨trivial, fun q hq => Option.some.inj hq ▸ ⟨hon, hb⟩⟩
    · have h' : ¬ encode ep.toPoint = self.toVector := fun he => h (key.mpr he)
      simp only [Bool.not_eq_true] at h
      simp only [h, h', decide_false]
      exact ⟨rfl, fun q hq => by cases hq⟩

open decompress_nist_full.closure.«64bit-tables».Insts in
theorem decompress_nist_full_spec (self : CompressedEdwardsY) :
    decompress_nist_full.«64bit-tables» self ⦃ (r : Option (EdwardsPoint.«64bit-tables»)) =>
      r.map EdwardsPoint.«64bit-tables».toPoint =
        ((decodeLenient self.toVector).filter (fun P => decide (encode P = self.toVector))).filter
          (fun P => decide (P ≠ 0 ∧ L • P = 0)) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 52 ⦄ := by
  unfold decompress_nist_full.«64bit-tables»
  step with decompress_rfc8032_spec self as ⟨o, hmap, hq⟩
  rcases o with _ | ep
  · simp only [core.option.Option.filter, spec_ok]
    rw [← hmap]
    exact ⟨rfl, fun q hq => by cases hq⟩
  · obtain ⟨hon, hb⟩ := hq ep rfl
    simp only [core.option.Option.filter]
    unfold «CoreOpsFunctionFnOnceTupleShared0EdwardsPoint64bit-tablesBool».call_once
    step with EdwardsPoint.«64bit-tables».is_identity_spec ep hb hon as ⟨i, hi⟩
    rw [← hmap, Option.map_some, Option.filter_some]
    by_cases hi' : i = true
    · have h0 : ep.toPoint = 0 := hi.mp hi'
      simp [hi', h0]
    · have h0 : ep.toPoint ≠ 0 := fun h => hi' (hi.mpr h)
      simp only [Bool.not_eq_true] at hi'
      simp only [hi', Bool.false_eq_true, ite_false]
      step with «EdwardsPoint64bit-tables».is_torsion_free_spec ep hb hon as ⟨t, ht⟩
      by_cases ht' : t = true
      · simp [ht', h0, ht.mp ht', hon, hb]
      · have ht'' : ¬ L • ep.toPoint = 0 := fun h => ht' (ht.mpr h)
        simp only [Bool.not_eq_true] at ht'
        simp [ht', ht'']

end CompressedEdwardsY.«64bit-tables»

namespace CompressedEdwardsY.«32bit-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

theorem decompress_rfc8032_spec (self : CompressedEdwardsY) :
    decompress_rfc8032.«32bit-tables» self ⦃ (r : Option (EdwardsPoint.«32bit-tables»)) =>
      r.map EdwardsPoint.«32bit-tables».toPoint =
        (decodeLenient self.toVector).filter (fun P => decide (encode P = self.toVector)) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 26 ⦄ := by
  unfold decompress_rfc8032.«32bit-tables»
  step with spec_and (decompress_spec self) (decompress_Z_spec self) as ⟨o, hmap, hq, hZ⟩
  rcases o with _ | ep
  · simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
    simp only [bind_ok, spec_ok, Option.map_none, reduceCtorEq, IsEmpty.forall_iff, implies_true,
      and_true]
    rw [← hmap]
    rfl
  · obtain ⟨hon, hb⟩ := hq ep rfl
    have hZ1 := hZ ep rfl
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    simp only [bind_ok]
    step with ONE_spec as ⟨fe, hfe, hfeb⟩
    step as ⟨b, hbe⟩
    have hbt : b = true := hbe.mpr (by
      rw [hfe]; exact toField_eq_natCast_iff.mp (by rw [hZ1]; simp))
    simp only [hbt, massert, ite_true]
    have hx : ep.toPoint.x = ep.X.toField := by
      rw [EdwardsPoint.«32bit-tables».toPoint_x hon, hZ1, div_one]
    have hy : ep.toPoint.y = ep.Y.toField := by
      rw [EdwardsPoint.«32bit-tables».toPoint_y hon, hZ1, div_one]
    have haon : (⟨ep.X, ep.Y⟩ : affine.AffinePoint.«32bit-tables»).OnCurve := by
      change curve25519.edwards.Equation ep.X.toField ep.Y.toField
      rw [← hx, ← hy]
      exact ep.toPoint.equation
    have hapt : (⟨ep.X, ep.Y⟩ : affine.AffinePoint.«32bit-tables»).toPoint = ep.toPoint := by
      simp only [affine.AffinePoint.«32bit-tables».toPoint_def, haon, ↓reduceDIte]
      ext
      · exact hx.symm
      · exact hy.symm
    step with affine.«AffinePoint32bit-tables».compress_spec _ haon as ⟨repr, hrepr⟩
    rw [hapt] at hrepr
    step as ⟨b1, hb1⟩
    have key : b1 = true ↔ encode ep.toPoint = self.toVector := by
      rw [hb1, eq_comm (a := encode _), CompressedEdwardsY.toVector_eq_encode_iff, ← hrepr]
      constructor
      · rintro rfl; rfl
      · intro h
        apply Aeneas.Std.Array.eq_of_asNat_eq
        rw [CompressedEdwardsY.asNat_def, CompressedEdwardsY.asNat_def] at h
        exact h.symm
    simp only [core.bool.Bool.then_some, spec_ok]
    rw [← hmap, Option.map_some, Option.filter_some]
    by_cases h : b1 = true
    · simp only [h, ite_true, Option.map_some, (key.mp h), decide_true]
      exact ⟨trivial, fun q hq => Option.some.inj hq ▸ ⟨hon, hb⟩⟩
    · have h' : ¬ encode ep.toPoint = self.toVector := fun he => h (key.mpr he)
      simp only [Bool.not_eq_true] at h
      simp only [h, h', decide_false]
      exact ⟨rfl, fun q hq => by cases hq⟩

open decompress_nist_full.closure.«32bit-tables».Insts in
theorem decompress_nist_full_spec (self : CompressedEdwardsY) :
    decompress_nist_full.«32bit-tables» self ⦃ (r : Option (EdwardsPoint.«32bit-tables»)) =>
      r.map EdwardsPoint.«32bit-tables».toPoint =
        ((decodeLenient self.toVector).filter (fun P => decide (encode P = self.toVector))).filter
          (fun P => decide (P ≠ 0 ∧ L • P = 0)) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 26 ⦄ := by
  unfold decompress_nist_full.«32bit-tables»
  step with decompress_rfc8032_spec self as ⟨o, hmap, hq⟩
  rcases o with _ | ep
  · simp only [core.option.Option.filter, spec_ok]
    rw [← hmap]
    exact ⟨rfl, fun q hq => by cases hq⟩
  · obtain ⟨hon, hb⟩ := hq ep rfl
    simp only [core.option.Option.filter]
    unfold «CoreOpsFunctionFnOnceTupleShared0EdwardsPoint32bit-tablesBool».call_once
    step with EdwardsPoint.«32bit-tables».is_identity_spec ep hb hon as ⟨i, hi⟩
    rw [← hmap, Option.map_some, Option.filter_some]
    by_cases hi' : i = true
    · have h0 : ep.toPoint = 0 := hi.mp hi'
      simp [hi', h0]
    · have h0 : ep.toPoint ≠ 0 := fun h => hi' (hi.mpr h)
      simp only [Bool.not_eq_true] at hi'
      simp only [hi', Bool.false_eq_true, ite_false]
      step with «EdwardsPoint32bit-tables».is_torsion_free_spec ep hb hon as ⟨t, ht⟩
      by_cases ht' : t = true
      · simp [ht', h0, ht.mp ht', hon, hb]
      · have ht'' : ¬ L • ep.toPoint = 0 := fun h => ht' (ht.mpr h)
        simp only [Bool.not_eq_true] at ht'
        simp [ht', ht'']

end CompressedEdwardsY.«32bit-tables»

namespace CompressedEdwardsY.«64bit-notables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

theorem decompress_rfc8032_spec (self : CompressedEdwardsY) :
    decompress_rfc8032.«64bit-notables» self ⦃ (r : Option (EdwardsPoint.«64bit-notables»)) =>
      r.map EdwardsPoint.«64bit-notables».toPoint =
        (decodeLenient self.toVector).filter (fun P => decide (encode P = self.toVector)) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 52 ⦄ := by
  unfold decompress_rfc8032.«64bit-notables»
  step with spec_and (decompress_spec self) (decompress_Z_spec self) as ⟨o, hmap, hq, hZ⟩
  rcases o with _ | ep
  · simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
    simp only [bind_ok, spec_ok, Option.map_none, reduceCtorEq, IsEmpty.forall_iff, implies_true,
      and_true]
    rw [← hmap]
    rfl
  · obtain ⟨hon, hb⟩ := hq ep rfl
    have hZ1 := hZ ep rfl
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    simp only [bind_ok]
    step with ONE_spec as ⟨fe, hfe, hfeb⟩
    step as ⟨b, hbe⟩
    have hbt : b = true := hbe.mpr (by
      rw [hfe]; exact toField_eq_natCast_iff.mp (by rw [hZ1]; simp))
    simp only [hbt, massert, ite_true]
    have hx : ep.toPoint.x = ep.X.toField := by
      rw [EdwardsPoint.«64bit-notables».toPoint_x hon, hZ1, div_one]
    have hy : ep.toPoint.y = ep.Y.toField := by
      rw [EdwardsPoint.«64bit-notables».toPoint_y hon, hZ1, div_one]
    have haon : (⟨ep.X, ep.Y⟩ : affine.AffinePoint.«64bit-notables»).OnCurve := by
      change curve25519.edwards.Equation ep.X.toField ep.Y.toField
      rw [← hx, ← hy]
      exact ep.toPoint.equation
    have hapt : (⟨ep.X, ep.Y⟩ : affine.AffinePoint.«64bit-notables»).toPoint = ep.toPoint := by
      simp only [affine.AffinePoint.«64bit-notables».toPoint_def, haon, ↓reduceDIte]
      ext
      · exact hx.symm
      · exact hy.symm
    step with affine.«AffinePoint64bit-notables».compress_spec _ haon as ⟨repr, hrepr⟩
    rw [hapt] at hrepr
    step as ⟨b1, hb1⟩
    have key : b1 = true ↔ encode ep.toPoint = self.toVector := by
      rw [hb1, eq_comm (a := encode _), CompressedEdwardsY.toVector_eq_encode_iff, ← hrepr]
      constructor
      · rintro rfl; rfl
      · intro h
        apply Aeneas.Std.Array.eq_of_asNat_eq
        rw [CompressedEdwardsY.asNat_def, CompressedEdwardsY.asNat_def] at h
        exact h.symm
    simp only [core.bool.Bool.then_some, spec_ok]
    rw [← hmap, Option.map_some, Option.filter_some]
    by_cases h : b1 = true
    · simp only [h, ite_true, Option.map_some, (key.mp h), decide_true]
      exact ⟨trivial, fun q hq => Option.some.inj hq ▸ ⟨hon, hb⟩⟩
    · have h' : ¬ encode ep.toPoint = self.toVector := fun he => h (key.mpr he)
      simp only [Bool.not_eq_true] at h
      simp only [h, h', decide_false]
      exact ⟨rfl, fun q hq => by cases hq⟩

open decompress_nist_full.closure.«64bit-notables».Insts in
theorem decompress_nist_full_spec (self : CompressedEdwardsY) :
    decompress_nist_full.«64bit-notables» self ⦃ (r : Option (EdwardsPoint.«64bit-notables»)) =>
      r.map EdwardsPoint.«64bit-notables».toPoint =
        ((decodeLenient self.toVector).filter (fun P => decide (encode P = self.toVector))).filter
          (fun P => decide (P ≠ 0 ∧ L • P = 0)) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 52 ⦄ := by
  unfold decompress_nist_full.«64bit-notables»
  step with decompress_rfc8032_spec self as ⟨o, hmap, hq⟩
  rcases o with _ | ep
  · simp only [core.option.Option.filter, spec_ok]
    rw [← hmap]
    exact ⟨rfl, fun q hq => by cases hq⟩
  · obtain ⟨hon, hb⟩ := hq ep rfl
    simp only [core.option.Option.filter]
    unfold «CoreOpsFunctionFnOnceTupleShared0EdwardsPoint64bit-notablesBool».call_once
    step with EdwardsPoint.«64bit-notables».is_identity_spec ep hb hon as ⟨i, hi⟩
    rw [← hmap, Option.map_some, Option.filter_some]
    by_cases hi' : i = true
    · have h0 : ep.toPoint = 0 := hi.mp hi'
      simp [hi', h0]
    · have h0 : ep.toPoint ≠ 0 := fun h => hi' (hi.mpr h)
      simp only [Bool.not_eq_true] at hi'
      simp only [hi', Bool.false_eq_true, ite_false]
      step with «EdwardsPoint64bit-notables».is_torsion_free_spec ep hb hon as ⟨t, ht⟩
      by_cases ht' : t = true
      · simp [ht', h0, ht.mp ht', hon, hb]
      · have ht'' : ¬ L • ep.toPoint = 0 := fun h => ht' (ht.mpr h)
        simp only [Bool.not_eq_true] at ht'
        simp [ht', ht'']

end CompressedEdwardsY.«64bit-notables»

namespace CompressedEdwardsY.«32bit-notables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

theorem decompress_rfc8032_spec (self : CompressedEdwardsY) :
    decompress_rfc8032.«32bit-notables» self ⦃ (r : Option (EdwardsPoint.«32bit-notables»)) =>
      r.map EdwardsPoint.«32bit-notables».toPoint =
        (decodeLenient self.toVector).filter (fun P => decide (encode P = self.toVector)) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 26 ⦄ := by
  unfold decompress_rfc8032.«32bit-notables»
  step with spec_and (decompress_spec self) (decompress_Z_spec self) as ⟨o, hmap, hq, hZ⟩
  rcases o with _ | ep
  · simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
    simp only [bind_ok, spec_ok, Option.map_none, reduceCtorEq, IsEmpty.forall_iff, implies_true,
      and_true]
    rw [← hmap]
    rfl
  · obtain ⟨hon, hb⟩ := hq ep rfl
    have hZ1 := hZ ep rfl
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    simp only [bind_ok]
    step with ONE_spec as ⟨fe, hfe, hfeb⟩
    step as ⟨b, hbe⟩
    have hbt : b = true := hbe.mpr (by
      rw [hfe]; exact toField_eq_natCast_iff.mp (by rw [hZ1]; simp))
    simp only [hbt, massert, ite_true]
    have hx : ep.toPoint.x = ep.X.toField := by
      rw [EdwardsPoint.«32bit-notables».toPoint_x hon, hZ1, div_one]
    have hy : ep.toPoint.y = ep.Y.toField := by
      rw [EdwardsPoint.«32bit-notables».toPoint_y hon, hZ1, div_one]
    have haon : (⟨ep.X, ep.Y⟩ : affine.AffinePoint.«32bit-notables»).OnCurve := by
      change curve25519.edwards.Equation ep.X.toField ep.Y.toField
      rw [← hx, ← hy]
      exact ep.toPoint.equation
    have hapt : (⟨ep.X, ep.Y⟩ : affine.AffinePoint.«32bit-notables»).toPoint = ep.toPoint := by
      simp only [affine.AffinePoint.«32bit-notables».toPoint_def, haon, ↓reduceDIte]
      ext
      · exact hx.symm
      · exact hy.symm
    step with affine.«AffinePoint32bit-notables».compress_spec _ haon as ⟨repr, hrepr⟩
    rw [hapt] at hrepr
    step as ⟨b1, hb1⟩
    have key : b1 = true ↔ encode ep.toPoint = self.toVector := by
      rw [hb1, eq_comm (a := encode _), CompressedEdwardsY.toVector_eq_encode_iff, ← hrepr]
      constructor
      · rintro rfl; rfl
      · intro h
        apply Aeneas.Std.Array.eq_of_asNat_eq
        rw [CompressedEdwardsY.asNat_def, CompressedEdwardsY.asNat_def] at h
        exact h.symm
    simp only [core.bool.Bool.then_some, spec_ok]
    rw [← hmap, Option.map_some, Option.filter_some]
    by_cases h : b1 = true
    · simp only [h, ite_true, Option.map_some, (key.mp h), decide_true]
      exact ⟨trivial, fun q hq => Option.some.inj hq ▸ ⟨hon, hb⟩⟩
    · have h' : ¬ encode ep.toPoint = self.toVector := fun he => h (key.mpr he)
      simp only [Bool.not_eq_true] at h
      simp only [h, h', decide_false]
      exact ⟨rfl, fun q hq => by cases hq⟩

open decompress_nist_full.closure.«32bit-notables».Insts in
theorem decompress_nist_full_spec (self : CompressedEdwardsY) :
    decompress_nist_full.«32bit-notables» self ⦃ (r : Option (EdwardsPoint.«32bit-notables»)) =>
      r.map EdwardsPoint.«32bit-notables».toPoint =
        ((decodeLenient self.toVector).filter (fun P => decide (encode P = self.toVector))).filter
          (fun P => decide (P ≠ 0 ∧ L • P = 0)) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 26 ⦄ := by
  unfold decompress_nist_full.«32bit-notables»
  step with decompress_rfc8032_spec self as ⟨o, hmap, hq⟩
  rcases o with _ | ep
  · simp only [core.option.Option.filter, spec_ok]
    rw [← hmap]
    exact ⟨rfl, fun q hq => by cases hq⟩
  · obtain ⟨hon, hb⟩ := hq ep rfl
    simp only [core.option.Option.filter]
    unfold «CoreOpsFunctionFnOnceTupleShared0EdwardsPoint32bit-notablesBool».call_once
    step with EdwardsPoint.«32bit-notables».is_identity_spec ep hb hon as ⟨i, hi⟩
    rw [← hmap, Option.map_some, Option.filter_some]
    by_cases hi' : i = true
    · have h0 : ep.toPoint = 0 := hi.mp hi'
      simp [hi', h0]
    · have h0 : ep.toPoint ≠ 0 := fun h => hi' (hi.mpr h)
      simp only [Bool.not_eq_true] at hi'
      simp only [hi', Bool.false_eq_true, ite_false]
      step with «EdwardsPoint32bit-notables».is_torsion_free_spec ep hb hon as ⟨t, ht⟩
      by_cases ht' : t = true
      · simp [ht', h0, ht.mp ht', hon, hb]
      · have ht'' : ¬ L • ep.toPoint = 0 := fun h => ht' (ht.mpr h)
        simp only [Bool.not_eq_true] at ht'
        simp [ht', ht'']

end CompressedEdwardsY.«32bit-notables»

end Curve25519Dalek.edwards
