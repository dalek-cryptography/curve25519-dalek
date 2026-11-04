/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Iterator
public import Defs.Montgomery
import Proofs.Backend.Serial.U64.Field.FromBytes
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Helpers.Target
import Proofs.Helpers.ToField
import Proofs.Montgomery.DifferentialAddAndDouble
import Proofs.Montgomery.ProjectiveAsAffine
import Proofs.Montgomery.ProjectiveConditionalSelect
import Proofs.Montgomery.ProjectiveIdentity
import Zeroize.Instances
import Proofs.Backend.Serial.U32.Field.FromBytes
import Proofs.Backend.Serial.U32.Field.One
import Proofs.Helpers.ToField2625
public section

/-! # `MontgomeryPoint::mul_bits_be`

The Montgomery ladder over the bits an iterator yields, most significant first:
`u ↦ encodeU (ladderBits bs u)`, RFC 7748 §5's loop body at each bit
(`MontgomeryModel.ladderBits`; it computes `u(n • Q)` for the integer `n` with these big-endian
bits, `MontgomeryModel.ladderBits_eq_xMul`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open MontgomeryModel (XZ)

namespace Curve25519Dalek.montgomery.MontgomeryPoint

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- The loop body of `mul_bits_be` on a yielded bit `cur`: the ladder's loop body. -/
private theorem mul_bits_be.«x86_64-tables_body_cons_spec» {T0 : Type}
    (inst : core.iter.traits.iterator.Iterator T0 Bool) {it it' : T0} {cur : Bool}
    (hnext : inst.next it ⦃ (o : Option Bool) (it1 : T0) => o = some cur ∧ it1 = it' ⦄)
    (affine_u : FieldElement51) (hu : affine_u.LimbsLt 54) (x0 x1 : ProjectivePoint.«x86_64-tables»)
    (prev_bit : Bool) (h0 : x0.LimbsLt 52) (h1 : x1.LimbsLt 52) :
    mul_bits_be.«x86_64-tables_loop».body inst affine_u it x0 x1 prev_bit ⦃ r =>
      ∃ y0 y1 : ProjectivePoint.«x86_64-tables», r = ControlFlow.cont (it', y0, y1, cur) ∧
        y0.LimbsLt 52 ∧ y1.LimbsLt 52 ∧
        (⟨y0.toXZ, y1.toXZ, cur⟩ : XZ.LadderState (ZMod p)) =
          XZ.ladderStep montgomery.a24 affine_u.toField ⟨x0.toXZ, x1.toXZ, prev_bit⟩ cur ⦄ := by
  unfold mul_bits_be.«x86_64-tables_loop».body
  apply spec_bind hnext
  rintro ⟨o, it1⟩ ⟨rfl, rfl⟩
  step as ⟨choice, hchoice⟩
  have hchoice01 : choice = 0#u8 ∨ choice = 1#u8 := by
    cases hbc : prev_bit ^^ cur
    · exact Or.inl (by rw [UScalar.eq_equiv]; simpa [hbc] using hchoice)
    · exact Or.inr (by rw [UScalar.eq_equiv]; simpa [hbc] using hchoice)
  step
  step as ⟨c, hc_valid, hc⟩
  cases hsw : prev_bit ^^ cur
  · have hc0 : c = 0#u8 := by
      rw [hc, UScalar.eq_equiv]
      simpa [hsw] using hchoice
    step with
        ProjectivePoint.«x86_64-tables».Insts.SubtleConditionallySelectable.conditional_swap_spec
      x0 x1 c hc_valid as ⟨x01, x11, hpr0, hpr1⟩
    obtain ⟨hx01, hx11⟩ := hpr0 hc0
    rw [hx01, hx11]
    step with «x86_64-tables».differential_add_and_double_spec x0 x1 affine_u h0 h1 hu
      as ⟨P', Q', hP', hQ', hP'_lt, hQ'_lt⟩
    refine ⟨P', Q', rfl, hP'_lt, hQ'_lt, ?_⟩
    simp only [XZ.ladderStep, hsw, XZ.cswap, Bool.false_eq_true, ↓reduceIte, hP', hQ']
  · have hc1 : c = 1#u8 := by
      rw [hc, UScalar.eq_equiv]
      simpa [hsw] using hchoice
    step with
        ProjectivePoint.«x86_64-tables».Insts.SubtleConditionallySelectable.conditional_swap_spec
      x0 x1 c hc_valid as ⟨x01, x11, hpr0, hpr1⟩
    obtain ⟨hx01, hx11⟩ := hpr1 hc1
    rw [hx01, hx11]
    step with «x86_64-tables».differential_add_and_double_spec x1 x0 affine_u h1 h0 hu
      as ⟨P', Q', hP', hQ', hP'_lt, hQ'_lt⟩
    refine ⟨P', Q', rfl, hP'_lt, hQ'_lt, ?_⟩
    simp only [XZ.ladderStep, hsw, XZ.cswap, ↓reduceIte, hP', hQ']

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- The loop body of `mul_bits_be` on a yielded bit `cur`: the ladder's loop body. -/
private theorem mul_bits_be.«i686-tables_body_cons_spec» {T0 : Type}
    (inst : core.iter.traits.iterator.Iterator T0 Bool) {it it' : T0} {cur : Bool}
    (hnext : inst.next it ⦃ (o : Option Bool) (it1 : T0) => o = some cur ∧ it1 = it' ⦄)
    (affine_u : FieldElement2625) (hu : affine_u.LimbsLt 27) (x0 x1 : ProjectivePoint.«i686-tables»)
    (prev_bit : Bool) (h0 : x0.LimbsLt 26) (h1 : x1.LimbsLt 26) :
    mul_bits_be.«i686-tables_loop».body inst affine_u it x0 x1 prev_bit ⦃ r =>
      ∃ y0 y1 : ProjectivePoint.«i686-tables», r = ControlFlow.cont (it', y0, y1, cur) ∧
        y0.LimbsLt 26 ∧ y1.LimbsLt 26 ∧
        (⟨y0.toXZ, y1.toXZ, cur⟩ : XZ.LadderState (ZMod p)) =
          XZ.ladderStep montgomery.a24 affine_u.toField ⟨x0.toXZ, x1.toXZ, prev_bit⟩ cur ⦄ := by
  unfold mul_bits_be.«i686-tables_loop».body
  apply spec_bind hnext
  rintro ⟨o, it1⟩ ⟨rfl, rfl⟩
  step as ⟨choice, hchoice⟩
  have hchoice01 : choice = 0#u8 ∨ choice = 1#u8 := by
    cases hbc : prev_bit ^^ cur
    · exact Or.inl (by rw [UScalar.eq_equiv]; simpa [hbc] using hchoice)
    · exact Or.inr (by rw [UScalar.eq_equiv]; simpa [hbc] using hchoice)
  step
  step as ⟨c, hc_valid, hc⟩
  cases hsw : prev_bit ^^ cur
  · have hc0 : c = 0#u8 := by
      rw [hc, UScalar.eq_equiv]
      simpa [hsw] using hchoice
    step with
        ProjectivePoint.«i686-tables».Insts.SubtleConditionallySelectable.conditional_swap_spec
      x0 x1 c hc_valid as ⟨x01, x11, hpr0, hpr1⟩
    obtain ⟨hx01, hx11⟩ := hpr0 hc0
    rw [hx01, hx11]
    step with «i686-tables».differential_add_and_double_spec x0 x1 affine_u h0 h1 hu
      as ⟨P', Q', hP', hQ', hP'_lt, hQ'_lt⟩
    refine ⟨P', Q', rfl, hP'_lt, hQ'_lt, ?_⟩
    simp only [XZ.ladderStep, hsw, XZ.cswap, Bool.false_eq_true, ↓reduceIte, hP', hQ']
  · have hc1 : c = 1#u8 := by
      rw [hc, UScalar.eq_equiv]
      simpa [hsw] using hchoice
    step with
        ProjectivePoint.«i686-tables».Insts.SubtleConditionallySelectable.conditional_swap_spec
      x0 x1 c hc_valid as ⟨x01, x11, hpr0, hpr1⟩
    obtain ⟨hx01, hx11⟩ := hpr1 hc1
    rw [hx01, hx11]
    step with «i686-tables».differential_add_and_double_spec x1 x0 affine_u h1 h0 hu
      as ⟨P', Q', hP', hQ', hP'_lt, hQ'_lt⟩
    refine ⟨P', Q', rfl, hP'_lt, hQ'_lt, ?_⟩
    simp only [XZ.ladderStep, hsw, XZ.cswap, ↓reduceIte, hP', hQ']

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- The loop body of `mul_bits_be` when the iterator is exhausted: done. -/
private theorem mul_bits_be.«x86_64-tables_body_nil_spec» {T0 : Type}
    (inst : core.iter.traits.iterator.Iterator T0 Bool) {it : T0}
    (hnext : inst.next it ⦃ (o : Option Bool) (_ : T0) => o = none ⦄)
    (affine_u : FieldElement51) (x0 x1 : ProjectivePoint.«x86_64-tables») (prev_bit : Bool) :
    mul_bits_be.«x86_64-tables_loop».body inst affine_u it x0 x1 prev_bit ⦃ r =>
      r = ControlFlow.done (x0, x1, prev_bit) ⦄ := by
  unfold mul_bits_be.«x86_64-tables_loop».body
  apply spec_bind hnext
  rintro ⟨o, it1⟩ rfl
  exact (spec_ok _).mpr rfl

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- The loop body of `mul_bits_be` when the iterator is exhausted: done. -/
private theorem mul_bits_be.«i686-tables_body_nil_spec» {T0 : Type}
    (inst : core.iter.traits.iterator.Iterator T0 Bool) {it : T0}
    (hnext : inst.next it ⦃ (o : Option Bool) (_ : T0) => o = none ⦄)
    (affine_u : FieldElement2625) (x0 x1 : ProjectivePoint.«i686-tables») (prev_bit : Bool) :
    mul_bits_be.«i686-tables_loop».body inst affine_u it x0 x1 prev_bit ⦃ r =>
      r = ControlFlow.done (x0, x1, prev_bit) ⦄ := by
  unfold mul_bits_be.«i686-tables_loop».body
  apply spec_bind hnext
  rintro ⟨o, it1⟩ rfl
  exact (spec_ok _).mpr rfl

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- The loop of `mul_bits_be`: the ladder's loop body at each yielded bit. -/
@[local step]
private theorem mul_bits_be.«x86_64-tables_loop_spec» {T0 : Type}
    (inst : core.iter.traits.iterator.Iterator T0 Bool) (iter : T0) (bs : List Bool)
    (hiter : inst.Yields iter bs) (affine_u : FieldElement51) (hu : affine_u.LimbsLt 54) :
    ∀ (x0 x1 : ProjectivePoint.«x86_64-tables») (prev_bit : Bool), x0.LimbsLt 52 → x1.LimbsLt 52 →
      mul_bits_be.«x86_64-tables_loop» inst iter affine_u x0 x1 prev_bit
        ⦃ (y0 y1 : ProjectivePoint.«x86_64-tables») (b : Bool) =>
          y0.LimbsLt 52 ∧ y1.LimbsLt 52 ∧
          (⟨y0.toXZ, y1.toXZ, b⟩ : XZ.LadderState (ZMod p)) =
            bs.foldl (XZ.ladderStep montgomery.a24 affine_u.toField)
              ⟨x0.toXZ, x1.toXZ, prev_bit⟩ ⦄ := by
  induction hiter with
  | nil hnext =>
    intro x0 x1 prev_bit h0 h1
    unfold mul_bits_be.«x86_64-tables_loop» loop
    apply spec_bind (mul_bits_be.«x86_64-tables_body_nil_spec» inst hnext affine_u x0 x1 prev_bit)
    rintro r rfl
    exact (spec_ok _).mpr ⟨h0, h1, rfl⟩
  | @cons it it' cur rest hnext _ ih =>
    intro x0 x1 prev_bit h0 h1
    unfold mul_bits_be.«x86_64-tables_loop» loop
    apply spec_bind (mul_bits_be.«x86_64-tables_body_cons_spec» inst hnext affine_u hu x0 x1
        prev_bit h0 h1)
    rintro r ⟨y0, y1, rfl, hy0, hy1, hy⟩
    apply spec_mono (ih y0 y1 cur hy0 hy1)
    rintro ⟨z0, z1, b⟩ ⟨hz0, hz1, hz⟩
    refine ⟨hz0, hz1, ?_⟩
    rw [hz, List.foldl_cons, ← hy]

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- The loop of `mul_bits_be`: the ladder's loop body at each yielded bit. -/
@[local step]
private theorem mul_bits_be.«i686-tables_loop_spec» {T0 : Type}
    (inst : core.iter.traits.iterator.Iterator T0 Bool) (iter : T0) (bs : List Bool)
    (hiter : inst.Yields iter bs) (affine_u : FieldElement2625) (hu : affine_u.LimbsLt 27) :
    ∀ (x0 x1 : ProjectivePoint.«i686-tables») (prev_bit : Bool), x0.LimbsLt 26 → x1.LimbsLt 26 →
      mul_bits_be.«i686-tables_loop» inst iter affine_u x0 x1 prev_bit
        ⦃ (y0 y1 : ProjectivePoint.«i686-tables») (b : Bool) =>
          y0.LimbsLt 26 ∧ y1.LimbsLt 26 ∧
          (⟨y0.toXZ, y1.toXZ, b⟩ : XZ.LadderState (ZMod p)) =
            bs.foldl (XZ.ladderStep montgomery.a24 affine_u.toField)
              ⟨x0.toXZ, x1.toXZ, prev_bit⟩ ⦄ := by
  induction hiter with
  | nil hnext =>
    intro x0 x1 prev_bit h0 h1
    unfold mul_bits_be.«i686-tables_loop» loop
    apply spec_bind (mul_bits_be.«i686-tables_body_nil_spec» inst hnext affine_u x0 x1 prev_bit)
    rintro r rfl
    exact (spec_ok _).mpr ⟨h0, h1, rfl⟩
  | @cons it it' cur rest hnext _ ih =>
    intro x0 x1 prev_bit h0 h1
    unfold mul_bits_be.«i686-tables_loop» loop
    apply spec_bind (mul_bits_be.«i686-tables_body_cons_spec» inst hnext affine_u hu x0 x1
        prev_bit h0 h1)
    rintro r ⟨y0, y1, rfl, hy0, hy1, hy⟩
    apply spec_mono (ih y0 y1 cur hy0 hy1)
    rintro ⟨z0, z1, b⟩ ⟨hz0, hz1, hz⟩
    refine ⟨hz0, hz1, ?_⟩
    rw [hz, List.foldl_cons, ← hy]

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `MontgomeryPoint::mul_bits_be`: the RFC 7748 ladder over the bits `bs` the iterator yields,
most significant first, encoded canonically. -/
@[step]
theorem mul_bits_be.«x86_64-tables_spec» {T0 : Type} (inst : core.iter.traits.iterator.Iterator T0
    Bool)
    (self : MontgomeryPoint) (bits : T0) (bs : List Bool) (hbits : inst.Yields bits bs) :
    mul_bits_be.«x86_64-tables» inst self bits ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladderBits bs self.u) ⦄ := by
  unfold mul_bits_be.«x86_64-tables»
  step as ⟨u, hu, hu_lt⟩
  step as ⟨x0, hx0, hx0_lt⟩
  step as ⟨one, hone, hone_lt⟩
  step with mul_bits_be.«x86_64-tables_loop_spec» inst bits bs hbits u (limbs_lt_of_le (by decide)
      hu_lt)
      x0 { U := u, W := one } false hx0_lt
      ⟨limbs_lt_of_le (by decide) hu_lt, limbs_lt_of_le (by decide) hone_lt⟩
    as ⟨y0, y1, pb, hy0, hy1, hst⟩
  step as ⟨i, hi⟩
  have hi01 : i = 0#u8 ∨ i = 1#u8 := by
    cases pb
    · exact Or.inl (by rw [UScalar.eq_equiv]; simpa using hi)
    · exact Or.inr (by rw [UScalar.eq_equiv]; simpa using hi)
  step as ⟨c, hcv, hc⟩
  step with
      ProjectivePoint.«x86_64-tables».Insts.SubtleConditionallySelectable.conditional_swap_spec
    y0 y1 c hcv as ⟨z0, z1, hz0, hz1⟩
  step
  have hz : z0 = if pb then y1 else y0 := by
    cases pb
    · exact (hz0 (by rw [hc, UScalar.eq_equiv]; simpa using hi)).1
    · exact (hz1 (by rw [hc, UScalar.eq_equiv]; simpa using hi)).1
  have hz_lt : z0.LimbsLt 54 := by
    rw [hz]
    cases pb
    · exact ⟨limbs_lt_of_le (by decide) hy0.1, limbs_lt_of_le (by decide) hy0.2⟩
    · exact ⟨limbs_lt_of_le (by decide) hy1.1, limbs_lt_of_le (by decide) hy1.2⟩
  step with «ProjectivePointx86_64-tables».as_affine_spec z0 hz_lt as ⟨r, hr⟩
  rw [hr, MontgomeryModel.ladderBits, MontgomeryModel.XZ.ladderBits, MontgomeryPoint.u_def, decodeU]
  congr 2
  have hu' : u.toField = ((self.asNat % 2 ^ 255 : ℕ) : ZMod p) := by
    rw [toField_def, hu, MontgomeryPoint.asNat_def]
  rw [← hu', MontgomeryModel.XZ.ladderBitsXZ]
  rw [show (⟨⟨1, 0⟩, ⟨u.toField, 1⟩, false⟩ : XZ.LadderState (ZMod p)) =
      ⟨x0.toXZ, ({ U := u, W := one } : ProjectivePoint.«x86_64-tables»).toXZ, false⟩ by
    rw [hx0, ProjectivePoint.«x86_64-tables».toXZ_def, toField_eq_one_of_asNat hone], ← hst, hz]
  cases pb <;> rfl

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- `MontgomeryPoint::mul_bits_be`: the RFC 7748 ladder over the bits `bs` the iterator yields,
most significant first, encoded canonically. -/
@[step]
theorem mul_bits_be.«i686-tables_spec» {T0 : Type} (inst : core.iter.traits.iterator.Iterator T0
    Bool)
    (self : MontgomeryPoint) (bits : T0) (bs : List Bool) (hbits : inst.Yields bits bs) :
    mul_bits_be.«i686-tables» inst self bits ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladderBits bs self.u) ⦄ := by
  unfold mul_bits_be.«i686-tables»
  step as ⟨u, hu, hu_lt⟩
  step as ⟨x0, hx0, hx0_lt⟩
  step as ⟨one, hone, hone_lt⟩
  step with mul_bits_be.«i686-tables_loop_spec» inst bits bs hbits u (limbs_lt_of_le (by decide)
      hu_lt)
      x0 { U := u, W := one } false hx0_lt
      ⟨limbs_lt_of_le (by decide) hu_lt, limbs_lt_of_le (by decide) hone_lt⟩
    as ⟨y0, y1, pb, hy0, hy1, hst⟩
  step as ⟨i, hi⟩
  have hi01 : i = 0#u8 ∨ i = 1#u8 := by
    cases pb
    · exact Or.inl (by rw [UScalar.eq_equiv]; simpa using hi)
    · exact Or.inr (by rw [UScalar.eq_equiv]; simpa using hi)
  step as ⟨c, hcv, hc⟩
  step with
      ProjectivePoint.«i686-tables».Insts.SubtleConditionallySelectable.conditional_swap_spec
    y0 y1 c hcv as ⟨z0, z1, hz0, hz1⟩
  step
  have hz : z0 = if pb then y1 else y0 := by
    cases pb
    · exact (hz0 (by rw [hc, UScalar.eq_equiv]; simpa using hi)).1
    · exact (hz1 (by rw [hc, UScalar.eq_equiv]; simpa using hi)).1
  have hz_lt : z0.LimbsLt 27 := by
    rw [hz]
    cases pb
    · exact ⟨limbs_lt_of_le (by decide) hy0.1, limbs_lt_of_le (by decide) hy0.2⟩
    · exact ⟨limbs_lt_of_le (by decide) hy1.1, limbs_lt_of_le (by decide) hy1.2⟩
  step with «ProjectivePointi686-tables».as_affine_spec z0 hz_lt as ⟨r, hr⟩
  rw [hr, MontgomeryModel.ladderBits, MontgomeryModel.XZ.ladderBits, MontgomeryPoint.u_def, decodeU]
  congr 2
  have hu' : u.toField = ((self.asNat % 2 ^ 255 : ℕ) : ZMod p) := by
    rw [toField_def, MontgomeryPoint.asNat_def]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hu
  rw [← hu', MontgomeryModel.XZ.ladderBitsXZ]
  rw [show (⟨⟨1, 0⟩, ⟨u.toField, 1⟩, false⟩ : XZ.LadderState (ZMod p)) =
      ⟨x0.toXZ, ({ U := u, W := one } : ProjectivePoint.«i686-tables»).toXZ, false⟩ by
    rw [hx0, ProjectivePoint.«i686-tables».toXZ_def, toField_eq_one_of_asNat hone], ← hst, hz]
  cases pb <;> rfl

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- The loop body of `mul_bits_be` on a yielded bit `cur`: the ladder's loop body. -/
private theorem mul_bits_be.«x86_64-no-tables_body_cons_spec» {T0 : Type}
    (inst : core.iter.traits.iterator.Iterator T0 Bool) {it it' : T0} {cur : Bool}
    (hnext : inst.next it ⦃ (o : Option Bool) (it1 : T0) => o = some cur ∧ it1 = it' ⦄)
    (affine_u : FieldElement51) (hu : affine_u.LimbsLt 54) (x0 x1 :
        ProjectivePoint.«x86_64-no-tables»)
    (prev_bit : Bool) (h0 : x0.LimbsLt 52) (h1 : x1.LimbsLt 52) :
    mul_bits_be.«x86_64-no-tables_loop».body inst affine_u it x0 x1 prev_bit ⦃ r =>
      ∃ y0 y1 : ProjectivePoint.«x86_64-no-tables», r = ControlFlow.cont (it', y0, y1, cur) ∧
        y0.LimbsLt 52 ∧ y1.LimbsLt 52 ∧
        (⟨y0.toXZ, y1.toXZ, cur⟩ : XZ.LadderState (ZMod p)) =
          XZ.ladderStep montgomery.a24 affine_u.toField ⟨x0.toXZ, x1.toXZ, prev_bit⟩ cur ⦄ := by
  unfold mul_bits_be.«x86_64-no-tables_loop».body
  apply spec_bind hnext
  rintro ⟨o, it1⟩ ⟨rfl, rfl⟩
  step as ⟨choice, hchoice⟩
  have hchoice01 : choice = 0#u8 ∨ choice = 1#u8 := by
    cases hbc : prev_bit ^^ cur
    · exact Or.inl (by rw [UScalar.eq_equiv]; simpa [hbc] using hchoice)
    · exact Or.inr (by rw [UScalar.eq_equiv]; simpa [hbc] using hchoice)
  step
  step as ⟨c, hc_valid, hc⟩
  cases hsw : prev_bit ^^ cur
  · have hc0 : c = 0#u8 := by
      rw [hc, UScalar.eq_equiv]
      simpa [hsw] using hchoice
    step with
        ProjectivePoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable.conditional_swap_spec
      x0 x1 c hc_valid as ⟨x01, x11, hpr0, hpr1⟩
    obtain ⟨hx01, hx11⟩ := hpr0 hc0
    rw [hx01, hx11]
    step with «x86_64-no-tables».differential_add_and_double_spec x0 x1 affine_u h0 h1 hu
      as ⟨P', Q', hP', hQ', hP'_lt, hQ'_lt⟩
    refine ⟨P', Q', rfl, hP'_lt, hQ'_lt, ?_⟩
    simp only [XZ.ladderStep, hsw, XZ.cswap, Bool.false_eq_true, ↓reduceIte, hP', hQ']
  · have hc1 : c = 1#u8 := by
      rw [hc, UScalar.eq_equiv]
      simpa [hsw] using hchoice
    step with
        ProjectivePoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable.conditional_swap_spec
      x0 x1 c hc_valid as ⟨x01, x11, hpr0, hpr1⟩
    obtain ⟨hx01, hx11⟩ := hpr1 hc1
    rw [hx01, hx11]
    step with «x86_64-no-tables».differential_add_and_double_spec x1 x0 affine_u h1 h0 hu
      as ⟨P', Q', hP', hQ', hP'_lt, hQ'_lt⟩
    refine ⟨P', Q', rfl, hP'_lt, hQ'_lt, ?_⟩
    simp only [XZ.ladderStep, hsw, XZ.cswap, ↓reduceIte, hP', hQ']

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- The loop body of `mul_bits_be` on a yielded bit `cur`: the ladder's loop body. -/
private theorem mul_bits_be.«i686-no-tables_body_cons_spec» {T0 : Type}
    (inst : core.iter.traits.iterator.Iterator T0 Bool) {it it' : T0} {cur : Bool}
    (hnext : inst.next it ⦃ (o : Option Bool) (it1 : T0) => o = some cur ∧ it1 = it' ⦄)
    (affine_u : FieldElement2625) (hu : affine_u.LimbsLt 27) (x0 x1 :
        ProjectivePoint.«i686-no-tables»)
    (prev_bit : Bool) (h0 : x0.LimbsLt 26) (h1 : x1.LimbsLt 26) :
    mul_bits_be.«i686-no-tables_loop».body inst affine_u it x0 x1 prev_bit ⦃ r =>
      ∃ y0 y1 : ProjectivePoint.«i686-no-tables», r = ControlFlow.cont (it', y0, y1, cur) ∧
        y0.LimbsLt 26 ∧ y1.LimbsLt 26 ∧
        (⟨y0.toXZ, y1.toXZ, cur⟩ : XZ.LadderState (ZMod p)) =
          XZ.ladderStep montgomery.a24 affine_u.toField ⟨x0.toXZ, x1.toXZ, prev_bit⟩ cur ⦄ := by
  unfold mul_bits_be.«i686-no-tables_loop».body
  apply spec_bind hnext
  rintro ⟨o, it1⟩ ⟨rfl, rfl⟩
  step as ⟨choice, hchoice⟩
  have hchoice01 : choice = 0#u8 ∨ choice = 1#u8 := by
    cases hbc : prev_bit ^^ cur
    · exact Or.inl (by rw [UScalar.eq_equiv]; simpa [hbc] using hchoice)
    · exact Or.inr (by rw [UScalar.eq_equiv]; simpa [hbc] using hchoice)
  step
  step as ⟨c, hc_valid, hc⟩
  cases hsw : prev_bit ^^ cur
  · have hc0 : c = 0#u8 := by
      rw [hc, UScalar.eq_equiv]
      simpa [hsw] using hchoice
    step with
        ProjectivePoint.«i686-no-tables».Insts.SubtleConditionallySelectable.conditional_swap_spec
      x0 x1 c hc_valid as ⟨x01, x11, hpr0, hpr1⟩
    obtain ⟨hx01, hx11⟩ := hpr0 hc0
    rw [hx01, hx11]
    step with «i686-no-tables».differential_add_and_double_spec x0 x1 affine_u h0 h1 hu
      as ⟨P', Q', hP', hQ', hP'_lt, hQ'_lt⟩
    refine ⟨P', Q', rfl, hP'_lt, hQ'_lt, ?_⟩
    simp only [XZ.ladderStep, hsw, XZ.cswap, Bool.false_eq_true, ↓reduceIte, hP', hQ']
  · have hc1 : c = 1#u8 := by
      rw [hc, UScalar.eq_equiv]
      simpa [hsw] using hchoice
    step with
        ProjectivePoint.«i686-no-tables».Insts.SubtleConditionallySelectable.conditional_swap_spec
      x0 x1 c hc_valid as ⟨x01, x11, hpr0, hpr1⟩
    obtain ⟨hx01, hx11⟩ := hpr1 hc1
    rw [hx01, hx11]
    step with «i686-no-tables».differential_add_and_double_spec x1 x0 affine_u h1 h0 hu
      as ⟨P', Q', hP', hQ', hP'_lt, hQ'_lt⟩
    refine ⟨P', Q', rfl, hP'_lt, hQ'_lt, ?_⟩
    simp only [XZ.ladderStep, hsw, XZ.cswap, ↓reduceIte, hP', hQ']

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- The loop body of `mul_bits_be` when the iterator is exhausted: done. -/
private theorem mul_bits_be.«x86_64-no-tables_body_nil_spec» {T0 : Type}
    (inst : core.iter.traits.iterator.Iterator T0 Bool) {it : T0}
    (hnext : inst.next it ⦃ (o : Option Bool) (_ : T0) => o = none ⦄)
    (affine_u : FieldElement51) (x0 x1 : ProjectivePoint.«x86_64-no-tables») (prev_bit : Bool) :
    mul_bits_be.«x86_64-no-tables_loop».body inst affine_u it x0 x1 prev_bit ⦃ r =>
      r = ControlFlow.done (x0, x1, prev_bit) ⦄ := by
  unfold mul_bits_be.«x86_64-no-tables_loop».body
  apply spec_bind hnext
  rintro ⟨o, it1⟩ rfl
  exact (spec_ok _).mpr rfl

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- The loop body of `mul_bits_be` when the iterator is exhausted: done. -/
private theorem mul_bits_be.«i686-no-tables_body_nil_spec» {T0 : Type}
    (inst : core.iter.traits.iterator.Iterator T0 Bool) {it : T0}
    (hnext : inst.next it ⦃ (o : Option Bool) (_ : T0) => o = none ⦄)
    (affine_u : FieldElement2625) (x0 x1 : ProjectivePoint.«i686-no-tables») (prev_bit : Bool) :
    mul_bits_be.«i686-no-tables_loop».body inst affine_u it x0 x1 prev_bit ⦃ r =>
      r = ControlFlow.done (x0, x1, prev_bit) ⦄ := by
  unfold mul_bits_be.«i686-no-tables_loop».body
  apply spec_bind hnext
  rintro ⟨o, it1⟩ rfl
  exact (spec_ok _).mpr rfl

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- The loop of `mul_bits_be`: the ladder's loop body at each yielded bit. -/
@[local step]
private theorem mul_bits_be.«x86_64-no-tables_loop_spec» {T0 : Type}
    (inst : core.iter.traits.iterator.Iterator T0 Bool) (iter : T0) (bs : List Bool)
    (hiter : inst.Yields iter bs) (affine_u : FieldElement51) (hu : affine_u.LimbsLt 54) :
    ∀ (x0 x1 : ProjectivePoint.«x86_64-no-tables») (prev_bit : Bool), x0.LimbsLt 52 → x1.LimbsLt 52
    →
      mul_bits_be.«x86_64-no-tables_loop» inst iter affine_u x0 x1 prev_bit
        ⦃ (y0 y1 : ProjectivePoint.«x86_64-no-tables») (b : Bool) =>
          y0.LimbsLt 52 ∧ y1.LimbsLt 52 ∧
          (⟨y0.toXZ, y1.toXZ, b⟩ : XZ.LadderState (ZMod p)) =
            bs.foldl (XZ.ladderStep montgomery.a24 affine_u.toField)
              ⟨x0.toXZ, x1.toXZ, prev_bit⟩ ⦄ := by
  induction hiter with
  | nil hnext =>
    intro x0 x1 prev_bit h0 h1
    unfold mul_bits_be.«x86_64-no-tables_loop» loop
    apply spec_bind (mul_bits_be.«x86_64-no-tables_body_nil_spec» inst hnext affine_u x0 x1
        prev_bit)
    rintro r rfl
    exact (spec_ok _).mpr ⟨h0, h1, rfl⟩
  | @cons it it' cur rest hnext _ ih =>
    intro x0 x1 prev_bit h0 h1
    unfold mul_bits_be.«x86_64-no-tables_loop» loop
    apply spec_bind (mul_bits_be.«x86_64-no-tables_body_cons_spec» inst hnext affine_u hu x0 x1
        prev_bit h0 h1)
    rintro r ⟨y0, y1, rfl, hy0, hy1, hy⟩
    apply spec_mono (ih y0 y1 cur hy0 hy1)
    rintro ⟨z0, z1, b⟩ ⟨hz0, hz1, hz⟩
    refine ⟨hz0, hz1, ?_⟩
    rw [hz, List.foldl_cons, ← hy]

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- The loop of `mul_bits_be`: the ladder's loop body at each yielded bit. -/
@[local step]
private theorem mul_bits_be.«i686-no-tables_loop_spec» {T0 : Type}
    (inst : core.iter.traits.iterator.Iterator T0 Bool) (iter : T0) (bs : List Bool)
    (hiter : inst.Yields iter bs) (affine_u : FieldElement2625) (hu : affine_u.LimbsLt 27) :
    ∀ (x0 x1 : ProjectivePoint.«i686-no-tables») (prev_bit : Bool), x0.LimbsLt 26 → x1.LimbsLt 26
    →
      mul_bits_be.«i686-no-tables_loop» inst iter affine_u x0 x1 prev_bit
        ⦃ (y0 y1 : ProjectivePoint.«i686-no-tables») (b : Bool) =>
          y0.LimbsLt 26 ∧ y1.LimbsLt 26 ∧
          (⟨y0.toXZ, y1.toXZ, b⟩ : XZ.LadderState (ZMod p)) =
            bs.foldl (XZ.ladderStep montgomery.a24 affine_u.toField)
              ⟨x0.toXZ, x1.toXZ, prev_bit⟩ ⦄ := by
  induction hiter with
  | nil hnext =>
    intro x0 x1 prev_bit h0 h1
    unfold mul_bits_be.«i686-no-tables_loop» loop
    apply spec_bind (mul_bits_be.«i686-no-tables_body_nil_spec» inst hnext affine_u x0 x1
        prev_bit)
    rintro r rfl
    exact (spec_ok _).mpr ⟨h0, h1, rfl⟩
  | @cons it it' cur rest hnext _ ih =>
    intro x0 x1 prev_bit h0 h1
    unfold mul_bits_be.«i686-no-tables_loop» loop
    apply spec_bind (mul_bits_be.«i686-no-tables_body_cons_spec» inst hnext affine_u hu x0 x1
        prev_bit h0 h1)
    rintro r ⟨y0, y1, rfl, hy0, hy1, hy⟩
    apply spec_mono (ih y0 y1 cur hy0 hy1)
    rintro ⟨z0, z1, b⟩ ⟨hz0, hz1, hz⟩
    refine ⟨hz0, hz1, ?_⟩
    rw [hz, List.foldl_cons, ← hy]

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `MontgomeryPoint::mul_bits_be`: the RFC 7748 ladder over the bits `bs` the iterator yields,
most significant first, encoded canonically. -/
@[step]
theorem mul_bits_be.«x86_64-no-tables_spec» {T0 : Type} (inst : core.iter.traits.iterator.Iterator
    T0 Bool)
    (self : MontgomeryPoint) (bits : T0) (bs : List Bool) (hbits : inst.Yields bits bs) :
    mul_bits_be.«x86_64-no-tables» inst self bits ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladderBits bs self.u) ⦄ := by
  unfold mul_bits_be.«x86_64-no-tables»
  step as ⟨u, hu, hu_lt⟩
  step as ⟨x0, hx0, hx0_lt⟩
  step as ⟨one, hone, hone_lt⟩
  step with mul_bits_be.«x86_64-no-tables_loop_spec» inst bits bs hbits u (limbs_lt_of_le (by
      decide) hu_lt)
      x0 { U := u, W := one } false hx0_lt
      ⟨limbs_lt_of_le (by decide) hu_lt, limbs_lt_of_le (by decide) hone_lt⟩
    as ⟨y0, y1, pb, hy0, hy1, hst⟩
  step as ⟨i, hi⟩
  have hi01 : i = 0#u8 ∨ i = 1#u8 := by
    cases pb
    · exact Or.inl (by rw [UScalar.eq_equiv]; simpa using hi)
    · exact Or.inr (by rw [UScalar.eq_equiv]; simpa using hi)
  step as ⟨c, hcv, hc⟩
  step with
      ProjectivePoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable.conditional_swap_spec
    y0 y1 c hcv as ⟨z0, z1, hz0, hz1⟩
  step
  have hz : z0 = if pb then y1 else y0 := by
    cases pb
    · exact (hz0 (by rw [hc, UScalar.eq_equiv]; simpa using hi)).1
    · exact (hz1 (by rw [hc, UScalar.eq_equiv]; simpa using hi)).1
  have hz_lt : z0.LimbsLt 54 := by
    rw [hz]
    cases pb
    · exact ⟨limbs_lt_of_le (by decide) hy0.1, limbs_lt_of_le (by decide) hy0.2⟩
    · exact ⟨limbs_lt_of_le (by decide) hy1.1, limbs_lt_of_le (by decide) hy1.2⟩
  step with «ProjectivePointx86_64-no-tables».as_affine_spec z0 hz_lt as ⟨r, hr⟩
  rw [hr, MontgomeryModel.ladderBits, MontgomeryModel.XZ.ladderBits, MontgomeryPoint.u_def, decodeU]
  congr 2
  have hu' : u.toField = ((self.asNat % 2 ^ 255 : ℕ) : ZMod p) := by
    rw [toField_def, hu, MontgomeryPoint.asNat_def]
  rw [← hu', MontgomeryModel.XZ.ladderBitsXZ]
  rw [show (⟨⟨1, 0⟩, ⟨u.toField, 1⟩, false⟩ : XZ.LadderState (ZMod p)) =
      ⟨x0.toXZ, ({ U := u, W := one } : ProjectivePoint.«x86_64-no-tables»).toXZ, false⟩ by
    rw [hx0, ProjectivePoint.«x86_64-no-tables».toXZ_def, toField_eq_one_of_asNat hone], ← hst, hz]
  cases pb <;> rfl

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- `MontgomeryPoint::mul_bits_be`: the RFC 7748 ladder over the bits `bs` the iterator yields,
most significant first, encoded canonically. -/
@[step]
theorem mul_bits_be.«i686-no-tables_spec» {T0 : Type} (inst : core.iter.traits.iterator.Iterator
    T0 Bool)
    (self : MontgomeryPoint) (bits : T0) (bs : List Bool) (hbits : inst.Yields bits bs) :
    mul_bits_be.«i686-no-tables» inst self bits ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladderBits bs self.u) ⦄ := by
  unfold mul_bits_be.«i686-no-tables»
  step as ⟨u, hu, hu_lt⟩
  step as ⟨x0, hx0, hx0_lt⟩
  step as ⟨one, hone, hone_lt⟩
  step with mul_bits_be.«i686-no-tables_loop_spec» inst bits bs hbits u (limbs_lt_of_le (by
      decide) hu_lt)
      x0 { U := u, W := one } false hx0_lt
      ⟨limbs_lt_of_le (by decide) hu_lt, limbs_lt_of_le (by decide) hone_lt⟩
    as ⟨y0, y1, pb, hy0, hy1, hst⟩
  step as ⟨i, hi⟩
  have hi01 : i = 0#u8 ∨ i = 1#u8 := by
    cases pb
    · exact Or.inl (by rw [UScalar.eq_equiv]; simpa using hi)
    · exact Or.inr (by rw [UScalar.eq_equiv]; simpa using hi)
  step as ⟨c, hcv, hc⟩
  step with
      ProjectivePoint.«i686-no-tables».Insts.SubtleConditionallySelectable.conditional_swap_spec
    y0 y1 c hcv as ⟨z0, z1, hz0, hz1⟩
  step
  have hz : z0 = if pb then y1 else y0 := by
    cases pb
    · exact (hz0 (by rw [hc, UScalar.eq_equiv]; simpa using hi)).1
    · exact (hz1 (by rw [hc, UScalar.eq_equiv]; simpa using hi)).1
  have hz_lt : z0.LimbsLt 27 := by
    rw [hz]
    cases pb
    · exact ⟨limbs_lt_of_le (by decide) hy0.1, limbs_lt_of_le (by decide) hy0.2⟩
    · exact ⟨limbs_lt_of_le (by decide) hy1.1, limbs_lt_of_le (by decide) hy1.2⟩
  step with «ProjectivePointi686-no-tables».as_affine_spec z0 hz_lt as ⟨r, hr⟩
  rw [hr, MontgomeryModel.ladderBits, MontgomeryModel.XZ.ladderBits, MontgomeryPoint.u_def, decodeU]
  congr 2
  have hu' : u.toField = ((self.asNat % 2 ^ 255 : ℕ) : ZMod p) := by
    rw [toField_def, MontgomeryPoint.asNat_def]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hu
  rw [← hu', MontgomeryModel.XZ.ladderBitsXZ]
  rw [show (⟨⟨1, 0⟩, ⟨u.toField, 1⟩, false⟩ : XZ.LadderState (ZMod p)) =
      ⟨x0.toXZ, ({ U := u, W := one } : ProjectivePoint.«i686-no-tables»).toXZ, false⟩ by
    rw [hx0, ProjectivePoint.«i686-no-tables».toXZ_def, toField_eq_one_of_asNat hone], ← hst, hz]
  cases pb <;> rfl

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `MontgomeryPoint::mul_bits_be`: the RFC 7748 ladder over the bits `bs` the iterator yields,
most significant first, encoded canonically (x86_64 targets). -/
@[step]
theorem mul_bits_be_spec {T0 : Type} (inst : core.iter.traits.iterator.Iterator T0 Bool)
    (self : MontgomeryPoint) (bits : T0) (bs : List Bool) (hbits : inst.Yields bits bs) :
    mul_bits_be inst self bits ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladderBits bs self.u) ⦄ := by
  unfold mul_bits_be
  exact dispatch_all_spec
    (mul_bits_be.«x86_64-tables_spec» inst self bits bs hbits)
    (mul_bits_be.«x86_64-no-tables_spec» inst self bits bs hbits)
    (mul_bits_be.«i686-tables_spec» inst self bits bs hbits)
    (mul_bits_be.«i686-no-tables_spec» inst self bits bs hbits)

end Curve25519Dalek.montgomery.MontgomeryPoint
