/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Represents
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Edwards
import all Curve25519.Basic
import Proofs.Helpers.TableCertificate
public section

/-! # `AFFINE_ODD_MULTIPLES_OF_BASEPOINT`

Entry `k` is the affine Niels form of `(2 k + 1) • B`. The constant is reduced to its 192 limb
arrays (`Proofs.Helpers.TableCertificate`), and the content is certified by kernel computation:
the entries are `B, B + 2 B, B + 2 • 2 B, …`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.curve_models
open Curve25519Dalek.TableCertificate

namespace Curve25519Dalek.backend.serial.u64.constants

set_option maxRecDepth 100000 in
collect_limbs oddLimbs from AFFINE_ODD_MULTIPLES_OF_BASEPOINT

/-- The table built from its 192 field elements in source order. -/
private def mkOddTable (fes : List FieldElement51) :
    window.NafLookupTable8 AffineNielsPoint.«x86_64-tables» :=
  if h : (entries fes).length = (64#usize).val then Array.make 64#usize (entries fes) h
  else default

private theorem mkOddTable_get {fes : List FieldElement51} (hlen : fes.length = 192) {k : ℕ}
    (hk : k < 64) :
    (mkOddTable fes)[k]! =
      (⟨fes[3 * k]!, fes[3 * k + 1]!, fes[3 * k + 2]!⟩ : AffineNielsPoint.«x86_64-tables») := by
  have h64 : (entries fes).length = (64#usize).val := by
    rw [entries_length, hlen]
    rfl
  rw [mkOddTable, dite_eq_left_of_eq_true (eq_true h64), Array.getElem!_Nat_eq, Array.make_val,
    entries_getElem! _ _ (by rw [hlen]; omega)]

set_option maxRecDepth 100000 in
private theorem odd_eq_bindList : AFFINE_ODD_MULTIPLES_OF_BASEPOINT =
    bindList oddLimbs (fun fes => ok (mkOddTable fes)) := by
  kernel_rfl

private theorem odd_eq : AFFINE_ODD_MULTIPLES_OF_BASEPOINT = ok (mkOddTable oddLimbs) := by
  rw [odd_eq_bindList, bindList_eq]

private theorem oddLimbs_length : oddLimbs.length = 192 := by
  decide +kernel

private theorem odd_check :
    checkRow edwards (pow2 edwards 1 (basepointExt edwards)) (basepointExt edwards) oddLimbs =
      true := by
  rw [curve25519.Proofs.edwards_eq]
  decide +kernel

private theorem odd_bounded :
    oddLimbs.all (fun a => a.val.all fun l => decide (l.val < 2 ^ 54)) = true := by
  decide +kernel

/-- `AFFINE_ODD_MULTIPLES_OF_BASEPOINT`: entry `k` is the affine Niels form of `(2 k + 1) • B`;
limbs `< 2^54`. -/
@[step]
theorem AFFINE_ODD_MULTIPLES_OF_BASEPOINT_spec :
    AFFINE_ODD_MULTIPLES_OF_BASEPOINT
      ⦃ (r : window.NafLookupTable8 AffineNielsPoint.«x86_64-tables») =>
        r.Represents basepoint ∧ r.LimbsLt 54 ⦄ := by
  rw [odd_eq, spec_ok]
  constructor
  · intro k hk
    rw [mkOddTable_get oddLimbs_length hk]
    have h := checkRow_sound (pow2_onCurve onCurve_basepointExt 1) onCurve_basepointExt odd_check k
      (by rw [oddLimbs_length]; omega)
    rw [toPoint_pow2 onCurve_basepointExt 1, toPoint_basepointExt, pow_one] at h
    have e := odd_smul_eq basepoint 0 k
    simp only [pow_zero, one_smul, zero_add, pow_one] at e
    rwa [e] at h
  · intro k hk
    rw [mkOddTable_get oddLimbs_length hk]
    exact ⟨limbs_lt_of_all odd_bounded (by rw [oddLimbs_length]; omega),
      limbs_lt_of_all odd_bounded (by rw [oddLimbs_length]; omega),
      limbs_lt_of_all odd_bounded (by rw [oddLimbs_length]; omega)⟩

end Curve25519Dalek.backend.serial.u64.constants
