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

/-! # `AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128`

Entry `k` is the projective Niels form of `(2 k + 1) • 2^128 • B`. The constant is reduced to
its 32 limb arrays (`Proofs.Helpers.TableCertificate`), and the content is certified by kernel
computation: the entries are `P, P + 2 P, P + 2 • 2 P, …` for `P = 2^128 • B`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.curve_models
open Curve25519Dalek.TableCertificate

namespace Curve25519Dalek.backend.serial.u64.constants

set_option maxRecDepth 100000 in
collect_limbs odd128Limbs from AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128

/-- The table built from its 32 field elements in source order. -/
private def mkOdd128Table (fes : List FieldElement51) :
    window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables» :=
  if h : (entriesProj fes).length = (8#usize).val then Array.make 8#usize (entriesProj fes) h
  else default

private theorem mkOdd128Table_get {fes : List FieldElement51} (hlen : fes.length = 32) {k : ℕ}
    (hk : k < 8) :
    (mkOdd128Table fes)[k]! =
      (⟨fes[4 * k]!, fes[4 * k + 1]!, fes[4 * k + 2]!, fes[4 * k + 3]!⟩ :
        ProjectiveNielsPoint.«x86_64-tables») := by
  have h8 : (entriesProj fes).length = (8#usize).val := by
    rw [entriesProj_length, hlen]
    rfl
  rw [mkOdd128Table, dite_eq_left_of_eq_true (eq_true h8), Array.getElem!_Nat_eq, Array.make_val,
    entriesProj_getElem! _ _ (by rw [hlen]; omega)]

set_option maxRecDepth 100000 in
private theorem odd128_eq_bindList : AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128 =
    bindList odd128Limbs (fun fes => ok (mkOdd128Table fes)) := by
  kernel_rfl

private theorem odd128_eq :
    AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128 = ok (mkOdd128Table odd128Limbs) := by
  rw [odd128_eq_bindList, bindList_eq]

private theorem odd128Limbs_length : odd128Limbs.length = 32 := by
  decide +kernel

private theorem odd128_check :
    checkRowProj edwards (pow2 edwards 129 (basepointExt edwards))
      (pow2 edwards 128 (basepointExt edwards)) odd128Limbs = true := by
  rw [curve25519.Proofs.edwards_eq]
  decide +kernel

private theorem odd128_bounded :
    odd128Limbs.all (fun a => a.val.all fun l => decide (l.val < 2 ^ 54)) = true := by
  decide +kernel

/-- `AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128`: entry `k` is the projective Niels form of
`(2 k + 1) • 2^128 • B`; limbs `< 2^54`. -/
@[step]
theorem AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128_spec :
    AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128
      ⦃ (r : window.NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables») =>
        r.Represents (2 ^ 128 • basepoint) ∧ r.LimbsLt 54 ⦄ := by
  rw [odd128_eq, spec_ok]
  constructor
  · intro k hk
    rw [mkOdd128Table_get odd128Limbs_length hk]
    have h := checkRowProj_sound (pow2_onCurve onCurve_basepointExt 129)
      (pow2_onCurve onCurve_basepointExt 128) odd128_check k (by rw [odd128Limbs_length]; omega)
    rwa [toPoint_pow2 onCurve_basepointExt 129, toPoint_pow2 onCurve_basepointExt 128,
      toPoint_basepointExt, odd_smul_eq] at h
  · intro k hk
    rw [mkOdd128Table_get odd128Limbs_length hk]
    exact ⟨limbs_lt_of_all odd128_bounded (by rw [odd128Limbs_length]; omega),
      limbs_lt_of_all odd128_bounded (by rw [odd128Limbs_length]; omega),
      limbs_lt_of_all odd128_bounded (by rw [odd128Limbs_length]; omega),
      limbs_lt_of_all odd128_bounded (by rw [odd128Limbs_length]; omega)⟩

end Curve25519Dalek.backend.serial.u64.constants
