/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Montgomery
public import Proofs.Helpers.Backend.U32
public import Proofs.Helpers.Backend.U64
public section

/-! # `differential_add_and_double`

The step of the Montgomery ladder on the `x`-only projective points: `P ↦ xDbl P` and
`Q ↦ XZ.add P Q u(P - Q)`, matching RFC 7748's formulas `MontgomeryModel.XZ.dbl`,
`MontgomeryModel.XZ.add` exactly as field elements. The code's doubling uses
`APLUS2_OVER_FOUR = (A + 2) / 4` with `BB`, the RFC's `a24 = (A - 2) / 4` with `AA = BB + E`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.Backend

variable (B : Backend)

/-- `differential_add_and_double` over a backend. -/
@[expose] def differentialAddAndDoubleBody {P : Type} (mk : B.F → B.F → P)
    (PU PW QU QW affine_PmQ : B.F) : Result (P × P) := do
  let t0 ← B.add PU PW
  let t1 ← B.sub PU PW
  let t2 ← B.add QU QW
  let t3 ← B.sub QU QW
  let t4 ← B.square t0
  let t5 ← B.square t1
  let t6 ← B.sub t4 t5
  let t7 ← B.mul t0 t3
  let t8 ← B.mul t1 t2
  let t9 ← B.add t7 t8
  let t10 ← B.sub t7 t8
  let t11 ← B.square t9
  let t12 ← B.square t10
  let fe ← B.constAplus2OverFour
  let t13 ← B.mul fe t6
  let t14 ← B.mul t4 t5
  let t15 ← B.add t13 t5
  let t16 ← B.mul t6 t15
  let t17 ← B.mul affine_PmQ t12
  ok (mk t14 t16, mk t11 t17)

/-- `APLUS2_OVER_FOUR = (A + 2) / 4` is the RFC's `a24 = (A - 2) / 4` plus one. -/
private theorem aplus2_eq {c : ZMod p} (h : c * 4 = (A : ZMod p) + 2) :
    c = montgomery.a24 + 1 := by
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]
    exact mul_ne_zero two_ne_zero two_ne_zero
  rw [MontgomeryModel.a24, montgomery_A]
  field_simp
  rw [h]
  ring

/-- `differentialAddAndDoubleBody`: `P ↦ xDbl P` and `Q ↦ XZ.add P Q u(P - Q)` exactly. -/
theorem differentialAddAndDoubleBody_spec (hadd : B.AddSpec) (hsub : B.SubSpec)
    (hmul : B.MulSpec) (hsq : B.SquareSpec) (hA : B.Aplus2OverFourSpec) {P : Type}
    (mk : B.F → B.F → P) (PU PW QU QW affine_PmQ : B.F) (hPU : B.Red PU) (hPW : B.Red PW)
    (hQU : B.Red QU) (hQW : B.Red QW) (haff : B.SqIn affine_PmQ) :
    B.differentialAddAndDoubleBody mk PU PW QU QW affine_PmQ ⦃ (P' Q' : P) =>
      ∃ u w u' w', P' = mk u w ∧ Q' = mk u' w' ∧
        (⟨B.toField u, B.toField w⟩ : MontgomeryModel.XZ (ZMod p)) =
          MontgomeryModel.XZ.dbl montgomery.a24 ⟨B.toField PU, B.toField PW⟩ ∧
        (⟨B.toField u', B.toField w'⟩ : MontgomeryModel.XZ (ZMod p)) =
          MontgomeryModel.XZ.add ⟨B.toField PU, B.toField PW⟩ ⟨B.toField QU, B.toField QW⟩
            (B.toField affine_PmQ) ∧
        B.Red u ∧ B.Red w ∧ B.Red u' ∧ B.Red w' ⦄ := by
  unfold differentialAddAndDoubleBody
  step with hadd PU PW hPU hPW as ⟨t0, ht0, ht0b⟩
  step with hsub PU PW (B.red_mulIn hPU) (B.red_mulIn hPW) as ⟨t1, ht1, ht1b⟩
  step with hadd QU QW hQU hQW as ⟨t2, ht2, ht2b⟩
  step with hsub QU QW (B.red_mulIn hQU) (B.red_mulIn hQW) as ⟨t3, ht3, ht3b⟩
  step with hsq t0 (B.sum2_sqIn ht0b) as ⟨t4, ht4, ht4b⟩
  step with hsq t1 (B.red_sqIn ht1b) as ⟨t5, ht5, ht5b⟩
  step with hsub t4 t5 (B.red_mulIn ht4b) (B.red_mulIn ht5b) as ⟨t6, ht6, ht6b⟩
  step with hmul t0 t3 (B.sum2_mulIn ht0b) (B.red_mulIn ht3b) as ⟨t7, ht7, ht7b⟩
  step with hmul t1 t2 (B.red_mulIn ht1b) (B.sum2_mulIn ht2b) as ⟨t8, ht8, ht8b⟩
  step with hadd t7 t8 ht7b ht8b as ⟨t9, ht9, ht9b⟩
  step with hsub t7 t8 (B.red_mulIn ht7b) (B.red_mulIn ht8b) as ⟨t10, ht10, ht10b⟩
  step with hsq t9 (B.sum2_sqIn ht9b) as ⟨t11, ht11, ht11b⟩
  step with hsq t10 (B.red_sqIn ht10b) as ⟨t12, ht12, ht12b⟩
  apply spec_bind hA
  rintro c ⟨hc, hcb⟩
  step with hmul c t6 (B.red_mulIn hcb) (B.red_mulIn ht6b) as ⟨t13, ht13, ht13b⟩
  step with hmul t4 t5 (B.red_mulIn ht4b) (B.red_mulIn ht5b) as ⟨t14, ht14, ht14b⟩
  step with hadd t13 t5 ht13b ht5b as ⟨t15, ht15, ht15b⟩
  step with hmul t6 t15 (B.red_mulIn ht6b) (B.sum2_mulIn ht15b) as ⟨t16, ht16, ht16b⟩
  step with hmul affine_PmQ t12 (B.sqIn_mulIn haff) (B.red_mulIn ht12b) as ⟨t17, ht17, ht17b⟩
  refine ⟨t14, t16, t11, t17, rfl, rfl, ?_, ?_, ht14b, ht16b, ht11b, ht17b⟩
  · simp only [MontgomeryModel.XZ.dbl, ht14, ht16, ht15, ht13, ht6, ht4, ht5, ht0, ht1,
      aplus2_eq hc]
    ring_nf
  · simp only [MontgomeryModel.XZ.add, ht11, ht17, ht12, ht9, ht10, ht7, ht8, ht0, ht1, ht2,
      ht3]
    ring_nf

end Curve25519Dalek.Backend

namespace Curve25519Dalek.montgomery

namespace «x86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

theorem differential_add_and_double_eq (P Q : ProjectivePoint.«x86_64-tables»)
    (affine_PmQ : FieldElement51) :
    differential_add_and_double.«x86_64-tables» P Q affine_PmQ =
      Backend.differentialAddAndDoubleBody Backend.U64
        (fun U W => (⟨U, W⟩ : ProjectivePoint.«x86_64-tables»)) P.U P.W Q.U Q.W affine_PmQ := rfl

/-- `differential_add_and_double`: one step of the ladder on `(U : W)` coordinates,
`P ↦ xDbl P` and `Q ↦ XZ.add P Q u(P - Q)` exactly (RFC 7748 §5); limbs `< 2^52`. -/
@[step]
theorem differential_add_and_double_spec (P Q : ProjectivePoint.«x86_64-tables»)
    (affine_PmQ : FieldElement51) (hP : P.LimbsLt 52) (hQ : Q.LimbsLt 52)
    (haffine_PmQ : affine_PmQ.LimbsLt 54) :
    differential_add_and_double.«x86_64-tables» P Q affine_PmQ
      ⦃ (P' Q' : ProjectivePoint.«x86_64-tables») =>
        P'.toXZ = MontgomeryModel.XZ.dbl montgomery.a24 P.toXZ ∧
        Q'.toXZ = MontgomeryModel.XZ.add P.toXZ Q.toXZ affine_PmQ.toField ∧
        P'.LimbsLt 52 ∧ Q'.LimbsLt 52 ⦄ := by
  obtain ⟨hPU, hPW⟩ := hP
  obtain ⟨hQU, hQW⟩ := hQ
  rw [differential_add_and_double_eq]
  apply spec_mono (Backend.differentialAddAndDoubleBody_spec Backend.U64
    Backend.U64.add_spec Backend.U64.sub_spec Backend.U64.mul_spec Backend.U64.square_spec
    Backend.U64.aplus2OverFour_spec _ _ _ _ _ _ hPU hPW hQU hQW haffine_PmQ)
  rintro ⟨P', Q'⟩ ⟨u, w, u', w', rfl, rfl, h1, h2, b1, b2, b3, b4⟩
  simp only [ProjectivePoint.«x86_64-tables».toXZ_def]
  exact ⟨h1, h2, ⟨b1, b2⟩, ⟨b3, b4⟩⟩

end «x86_64-tables»

namespace «i686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

theorem differential_add_and_double_eq (P Q : ProjectivePoint.«i686-tables»)
    (affine_PmQ : FieldElement2625) :
    differential_add_and_double.«i686-tables» P Q affine_PmQ =
      Backend.differentialAddAndDoubleBody Backend.U32
        (fun U W => (⟨U, W⟩ : ProjectivePoint.«i686-tables»)) P.U P.W Q.U Q.W affine_PmQ := rfl

/-- `differential_add_and_double`: one step of the ladder on `(U : W)` coordinates,
`P ↦ xDbl P` and `Q ↦ XZ.add P Q u(P - Q)` exactly (RFC 7748 §5); limbs `< 2^26`. -/
@[step]
theorem differential_add_and_double_spec (P Q : ProjectivePoint.«i686-tables»)
    (affine_PmQ : FieldElement2625) (hP : P.LimbsLt 26) (hQ : Q.LimbsLt 26)
    (haffine_PmQ : affine_PmQ.LimbsLt 27) :
    differential_add_and_double.«i686-tables» P Q affine_PmQ
      ⦃ (P' Q' : ProjectivePoint.«i686-tables») =>
        P'.toXZ = MontgomeryModel.XZ.dbl montgomery.a24 P.toXZ ∧
        Q'.toXZ = MontgomeryModel.XZ.add P.toXZ Q.toXZ affine_PmQ.toField ∧
        P'.LimbsLt 26 ∧ Q'.LimbsLt 26 ⦄ := by
  obtain ⟨hPU, hPW⟩ := hP
  obtain ⟨hQU, hQW⟩ := hQ
  rw [differential_add_and_double_eq]
  apply spec_mono (Backend.differentialAddAndDoubleBody_spec Backend.U32
    Backend.U32.add_spec Backend.U32.sub_spec Backend.U32.mul_spec Backend.U32.square_spec
    Backend.U32.aplus2OverFour_spec _ _ _ _ _ _ hPU hPW hQU hQW haffine_PmQ)
  rintro ⟨P', Q'⟩ ⟨u, w, u', w', rfl, rfl, h1, h2, b1, b2, b3, b4⟩
  simp only [ProjectivePoint.«i686-tables».toXZ_def]
  exact ⟨h1, h2, ⟨b1, b2⟩, ⟨b3, b4⟩⟩

end «i686-tables»

namespace «x86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

theorem differential_add_and_double_eq (P Q : ProjectivePoint.«x86_64-no-tables»)
    (affine_PmQ : FieldElement51) :
    differential_add_and_double.«x86_64-no-tables» P Q affine_PmQ =
      Backend.differentialAddAndDoubleBody Backend.U64
        (fun U W => (⟨U, W⟩ : ProjectivePoint.«x86_64-no-tables»)) P.U P.W Q.U Q.W affine_PmQ := rfl

/-- `differential_add_and_double`: one step of the ladder on `(U : W)` coordinates,
`P ↦ xDbl P` and `Q ↦ XZ.add P Q u(P - Q)` exactly (RFC 7748 §5); limbs `< 2^52`. -/
@[step]
theorem differential_add_and_double_spec (P Q : ProjectivePoint.«x86_64-no-tables»)
    (affine_PmQ : FieldElement51) (hP : P.LimbsLt 52) (hQ : Q.LimbsLt 52)
    (haffine_PmQ : affine_PmQ.LimbsLt 54) :
    differential_add_and_double.«x86_64-no-tables» P Q affine_PmQ
      ⦃ (P' Q' : ProjectivePoint.«x86_64-no-tables») =>
        P'.toXZ = MontgomeryModel.XZ.dbl montgomery.a24 P.toXZ ∧
        Q'.toXZ = MontgomeryModel.XZ.add P.toXZ Q.toXZ affine_PmQ.toField ∧
        P'.LimbsLt 52 ∧ Q'.LimbsLt 52 ⦄ := by
  obtain ⟨hPU, hPW⟩ := hP
  obtain ⟨hQU, hQW⟩ := hQ
  rw [differential_add_and_double_eq]
  apply spec_mono (Backend.differentialAddAndDoubleBody_spec Backend.U64
    Backend.U64.add_spec Backend.U64.sub_spec Backend.U64.mul_spec Backend.U64.square_spec
    Backend.U64.aplus2OverFour_spec _ _ _ _ _ _ hPU hPW hQU hQW haffine_PmQ)
  rintro ⟨P', Q'⟩ ⟨u, w, u', w', rfl, rfl, h1, h2, b1, b2, b3, b4⟩
  simp only [ProjectivePoint.«x86_64-no-tables».toXZ_def]
  exact ⟨h1, h2, ⟨b1, b2⟩, ⟨b3, b4⟩⟩

end «x86_64-no-tables»

namespace «i686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

theorem differential_add_and_double_eq (P Q : ProjectivePoint.«i686-no-tables»)
    (affine_PmQ : FieldElement2625) :
    differential_add_and_double.«i686-no-tables» P Q affine_PmQ =
      Backend.differentialAddAndDoubleBody Backend.U32
        (fun U W => (⟨U, W⟩ : ProjectivePoint.«i686-no-tables»)) P.U P.W Q.U Q.W affine_PmQ := rfl

/-- `differential_add_and_double`: one step of the ladder on `(U : W)` coordinates,
`P ↦ xDbl P` and `Q ↦ XZ.add P Q u(P - Q)` exactly (RFC 7748 §5); limbs `< 2^26`. -/
@[step]
theorem differential_add_and_double_spec (P Q : ProjectivePoint.«i686-no-tables»)
    (affine_PmQ : FieldElement2625) (hP : P.LimbsLt 26) (hQ : Q.LimbsLt 26)
    (haffine_PmQ : affine_PmQ.LimbsLt 27) :
    differential_add_and_double.«i686-no-tables» P Q affine_PmQ
      ⦃ (P' Q' : ProjectivePoint.«i686-no-tables») =>
        P'.toXZ = MontgomeryModel.XZ.dbl montgomery.a24 P.toXZ ∧
        Q'.toXZ = MontgomeryModel.XZ.add P.toXZ Q.toXZ affine_PmQ.toField ∧
        P'.LimbsLt 26 ∧ Q'.LimbsLt 26 ⦄ := by
  obtain ⟨hPU, hPW⟩ := hP
  obtain ⟨hQU, hQW⟩ := hQ
  rw [differential_add_and_double_eq]
  apply spec_mono (Backend.differentialAddAndDoubleBody_spec Backend.U32
    Backend.U32.add_spec Backend.U32.sub_spec Backend.U32.mul_spec Backend.U32.square_spec
    Backend.U32.aplus2OverFour_spec _ _ _ _ _ _ hPU hPW hQU hQW haffine_PmQ)
  rintro ⟨P', Q'⟩ ⟨u, w, u', w', rfl, rfl, h1, h2, b1, b2, b3, b4⟩
  simp only [ProjectivePoint.«i686-no-tables».toXZ_def]
  exact ⟨h1, h2, ⟨b1, b2⟩, ⟨b3, b4⟩⟩

end «i686-no-tables»

end Curve25519Dalek.montgomery
