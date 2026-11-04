/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Edwards
import all Curve25519.Basic
import Proofs.Helpers.TableCertificate2625
public section

/-! # `ED25519_BASEPOINT_TABLE`

Row `i` is the lookup table of `2^(8 i) • B`: entry `j` is the affine Niels form of
`(j + 1) • 2^(8 i) • B`. The constant is reduced to its 768 limb arrays
(`Proofs.Helpers.TableCertificate`), and the content is certified by kernel computation. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models
open Curve25519Dalek.TableCertificate2625
open Curve25519Dalek.TableCertificate (basepointExt onCurve_basepointExt
  toPoint_basepointExt pow2_onCurve toPoint_pow2 odd_smul_eq checkPoint checkPoint_sound rows
  rows_length rows_getElem!_getElem! pow2)

namespace Curve25519Dalek.backend.serial.u32.constants

set_option maxRecDepth 100000 in
collect_limbs_u32 tableLimbs32 from ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN

/-- The table built from its 768 field elements in source order: 32 rows of 8 entries. -/
private def mkTable (fes : List FieldElement2625) : edwards.EdwardsBasepointTable.«i686-tables» :=
  if h : (rows (entries fes)).length = (32#usize).val then
    Array.make 32#usize (rows (entries fes)) h
  else default

private theorem mkTable_get {fes : List FieldElement2625} (hlen : fes.length = 768) {i j : ℕ}
    (hi : i < 32) (hj : j < 8) :
    ((mkTable fes)[i]!)[j]! =
      (⟨fes[24 * i + 3 * j]!, fes[24 * i + 3 * j + 1]!, fes[24 * i + 3 * j + 2]!⟩ :
        AffineNielsPoint.«i686-tables») := by
  have h32 : (rows (entries fes)).length = (32#usize).val := by
    rw [rows_length, entries_length, hlen]
    rfl
  rw [mkTable, dite_eq_left_of_eq_true (eq_true h32),
    Array.getElem!_Nat_eq (Array.make 32#usize (rows (entries fes)) _) i, Array.make_val,
    rows_getElem!_getElem! _ _ _ (by rw [entries_length, hlen]; omega) hj,
    entries_getElem! _ _ (by rw [hlen]; omega), show 3 * (8 * i + j) = 24 * i + 3 * j by ring]

set_option maxRecDepth 100000 in
private theorem inner_eq_bindList : ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN =
    bindList tableLimbs32 (fun fes => ok (mkTable fes)) := by
  kernel_rfl

private theorem inner_eq :
    ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN = ok (mkTable tableLimbs32) := by
  rw [inner_eq_bindList, bindList_eq]

private theorem tableLimbs_length : tableLimbs32.length = 768 := by
  decide +kernel

private theorem table_check : checkTable edwards (basepointExt edwards) tableLimbs32 32 = true := by
  rw [curve25519.Proofs.edwards_eq]
  decide +kernel

private theorem table_bounded :
    tableLimbs32.all (fun a => a.val.all fun l => decide (l.val < 2 ^ 27)) = true := by
  decide +kernel

/-- `ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN`: the radix-`16` basepoint table of `B` (row `i`
is the lookup table of `2^(8 i) • B`); limbs `< 2^27`. -/
@[step]
theorem ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN_spec :
    ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN
      ⦃ (r : edwards.EdwardsBasepointTable.«i686-tables») =>
        r.Represents basepoint ∧ r.LimbsLt 27 ⦄ := by
  rw [inner_eq, spec_ok]
  constructor
  · intro i hi j hj
    rw [mkTable_get tableLimbs_length hi hj]
    have h := checkTable_sound onCurve_basepointExt table_check (by rw [tableLimbs_length]) i hi
      j hj
    rwa [toPoint_basepointExt] at h
  · intro i hi j hj
    rw [mkTable_get tableLimbs_length hi hj]
    refine ⟨limbs_lt_of_all table_bounded (by rw [tableLimbs_length]; omega),
      limbs_lt_of_all table_bounded (by rw [tableLimbs_length]; omega),
      limbs_lt_of_all table_bounded (by rw [tableLimbs_length]; omega)⟩

/-- `ED25519_BASEPOINT_TABLE`: the radix-`16` basepoint table of `B` (row `i` is the lookup
table of `2^(8 i) • B`); limbs `< 2^27`. -/
@[step]
theorem ED25519_BASEPOINT_TABLE_spec :
    ED25519_BASEPOINT_TABLE ⦃ (r : edwards.EdwardsBasepointTable.«i686-tables») =>
      r.Represents basepoint ∧ r.LimbsLt 27 ⦄ := by
  unfold ED25519_BASEPOINT_TABLE
  exact ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN_spec

end Curve25519Dalek.backend.serial.u32.constants
