/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Montgomery
public import Defs.Scalar
public import Proofs.Helpers.Backend.U32
public import Proofs.Helpers.Backend.U64
import Proofs.Backend.Serial.U64.Field.FromBytes
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Helpers.AsNat
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Target
import Proofs.Helpers.ToField
import Proofs.Montgomery.DifferentialAddAndDouble
import Proofs.Montgomery.ProjectiveAsAffine
import Proofs.Montgomery.ProjectiveConditionalSelect
import Proofs.Montgomery.ProjectiveIdentity
import Proofs.Scalar.AsBytes
import Zeroize.Instances
import Proofs.Backend.Serial.U32.Field.FromBytes
import Proofs.Backend.Serial.U32.Field.One
import Proofs.Helpers.ToField2625
public section

/-! # `Mul<&Scalar> for &MontgomeryPoint`

The Montgomery ladder on the low `255` bits of the scalar (the code skips bit `255`), from the
top: `u ↦ encodeU (ladder 255 (s mod 2^255) u)` exactly, RFC 7748 §5's ladder on curve25519's
`a24`. The translation patch replaces `scalar.bits_le().rev().skip(1)` by an index loop reading
bit `i - 1` of the bytes for `i = 255, …, 1`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open MontgomeryModel (XZ)

namespace Curve25519Dalek.montgomery

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- The ladder loop over `t` bits only reads the bits below `t`. -/
private theorem ladderLoop_congr (a24 x₁ : ZMod p) {k k' : ℕ} :
    ∀ (t : ℕ) (s : XZ.LadderState (ZMod p)), (∀ t' < t, k.testBit t' = k'.testBit t') →
      XZ.ladderLoop a24 x₁ k t s = XZ.ladderLoop a24 x₁ k' t s
  | 0, _, _ => rfl
  | t + 1, s, h => by
    rw [XZ.ladderLoop, XZ.ladderLoop, h t (Nat.lt_succ_self t)]
    exact ladderLoop_congr a24 x₁ t _ fun t' ht' => h t' (Nat.lt_succ_of_lt ht')

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- The ladder over `255` bits does not see bit `255` and above. -/
private theorem ladderXZ_mod (a24 u : ZMod p) (k : ℕ) :
    XZ.ladderXZ a24 255 (k % 2 ^ 255) u = XZ.ladderXZ a24 255 k u := by
  have h := ladderLoop_congr a24 u (k := k % 2 ^ 255) (k' := k) 255 ⟨⟨1, 0⟩, ⟨u, 1⟩, false⟩
    fun t' ht' => by rw [Nat.testBit_mod_two_pow, decide_eq_true ht', Bool.true_and]
  simp only [XZ.ladderXZ, h]

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- Bit `j` of the little-endian value of the bytes is bit `j % 8` of byte `j / 8`. -/
private theorem testBit_asNat (bytes : Array U8 32#usize) (j : ℕ) :
    (bytes.asNat 8).testBit j = bytes[j / 8]!.val.testBit (j % 8) := by
  rw [← Array.asNat_div_pow_mod 8 bytes (fun i _ => bytes[i]!.hBounds) (j / 8),
    Nat.testBit_mod_two_pow, decide_eq_true (Nat.mod_lt j (by norm_num)), Bool.true_and,
    Nat.testBit_div_two_pow]
  congr 1
  omega

end Curve25519Dalek.montgomery

namespace Curve25519Dalek.Backend

variable (B : Backend)

open ControlFlow

/-- The loop body of `Mul<&Scalar> for &MontgomeryPoint` over a backend: `swap` is
`conditional_swap` and `dad` is `differential_add_and_double` on the projective points `P`. -/
@[expose] def mulLadderBody {P : Type} (swap : P → P → subtle.Choice → Result (P × P))
    (dad : P → P → B.F → Result (P × P)) (bytes : Array U8 32#usize) (affine_u : B.F)
    (x0 x1 : P) (prev_bit : Bool) (i : Usize) :
    Result (ControlFlow (P × P × Bool × Usize) (P × P × Bool)) := do
  if i > 0#usize
  then
    let i1 ← i - 1#usize
    let i2 ← i1 >>> 3#i32
    let i3 ← Array.index_usize bytes i2
    let i4 ← lift (i1 &&& 7#usize)
    let i5 ← i3 >>> i4
    let i6 ← lift (i5 &&& 1#u8)
    let choice ← lift (UScalar.cast_fromBool .U8 (prev_bit ^^ (i6 = 1#u8)))
    massert ((choice = 0#u8) || (choice = 1#u8))
    let c ← core.convert.IntoFrom.into subtle.Choice.Insts.CoreConvertFromU8 choice
    let (x01, x11) ← swap x0 x1 c
    let (x02, x12) ← dad x01 x11 affine_u
    ok (cont (x02, x12, i6 = 1#u8, i1))
  else ok (done (x0, x1, prev_bit))

/-- The loop of `Mul<&Scalar> for &MontgomeryPoint` over a backend. -/
@[expose] def mulLadder {P : Type} (swap : P → P → subtle.Choice → Result (P × P))
    (dad : P → P → B.F → Result (P × P)) (bytes : Array U8 32#usize) (affine_u : B.F)
    (x0 x1 : P) (prev_bit : Bool) (i : Usize) : Result (P × P × Bool) := do
  loop (fun (x01, x11, prev_bit1, i1) =>
      B.mulLadderBody swap dad bytes affine_u x01 x11 prev_bit1 i1)
    (x0, x1, prev_bit, i)

open scoped Helpers.IndexStep in
/-- `mulLadder`: from bit `i - 1` down to bit `0`, the ladder's loop body, for points with
coordinates `toXZ` and bounds `Bnd` preserved by `dad`. -/
private theorem mulLadder_spec {P : Type} (toXZ : P → XZ (ZMod p)) (Bnd : P → Prop)
    (swap : P → P → subtle.Choice → Result (P × P)) (dad : P → P → B.F → Result (P × P))
    (hswap : ∀ a b (c : subtle.Choice), c.IsValid →
      swap a b c ⦃ (r : P × P) => (c = 0#u8 → r = (a, b)) ∧ (c = 1#u8 → r = (b, a)) ⦄)
    (hdad : ∀ a b u, Bnd a → Bnd b → B.SqIn u → dad a b u ⦃ (a' b' : P) =>
      toXZ a' = XZ.dbl montgomery.a24 (toXZ a) ∧ toXZ b' = XZ.add (toXZ a) (toXZ b) (B.toField u) ∧
        Bnd a' ∧ Bnd b' ⦄)
    (bytes : Array U8 32#usize) (affine_u : B.F) (x0 x1 : P) (prev_bit : Bool) (i : Usize)
    (hi : i.val ≤ 255) (hu : B.SqIn affine_u) (h0 : Bnd x0) (h1 : Bnd x1) :
    B.mulLadder swap dad bytes affine_u x0 x1 prev_bit i ⦃ (y0 y1 : P) (b : Bool) =>
      Bnd y0 ∧ Bnd y1 ∧
      (⟨toXZ y0, toXZ y1, b⟩ : XZ.LadderState (ZMod p)) =
        XZ.ladderLoop montgomery.a24 (B.toField affine_u) (bytes.asNat 8) i.val
          ⟨toXZ x0, toXZ x1, prev_bit⟩ ⦄ := by
  unfold mulLadder
  apply loop.spec_decr_nat (measure := fun (_, _, _, j) => j.val)
    (inv := fun (y0, y1, b, j) => j.val ≤ 255 ∧ Bnd y0 ∧ Bnd y1 ∧
      XZ.ladderLoop montgomery.a24 (B.toField affine_u) (bytes.asNat 8) j.val
          ⟨toXZ y0, toXZ y1, b⟩ =
        XZ.ladderLoop montgomery.a24 (B.toField affine_u) (bytes.asNat 8) i.val
          ⟨toXZ x0, toXZ x1, prev_bit⟩)
  · rintro ⟨y0, y1, b, j⟩ ⟨hj, hy0, hy1, hinv⟩
    simp only
    unfold mulLadderBody
    split
    next hgt =>
      have hpos : 0 < j.val := by scalar_tac
      step as ⟨j1, hj1, _⟩
      step as ⟨q, hq, _⟩
      · rcases System.Platform.numBits_eq with h | h <;> simp [h]
      step as ⟨byte, hbyte⟩
      step as ⟨r, hr, _⟩
      have hr8 : r.val < 8 := by
        rw [hr, UScalar.val_and]
        exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
      step as ⟨sh, hsh, _⟩
      step as ⟨bit, hbit, _⟩
      -- the bit read is bit `j - 1` of the scalar
      have hcur : decide (bit = 1#u8) = (bytes.asNat 8).testBit j1.val := by
        rw [montgomery.testBit_asNat, Nat.testBit_eq_decide_div_mod_eq]
        have hq' : q.val = j1.val / 8 := by rw [hq, Nat.shiftRight_eq_div_pow]
        have hr' : r.val = j1.val % 8 := by
          rw [hr, UScalar.val_and, show (7#usize).val = 2 ^ 3 - 1 from rfl,
              Nat.and_two_pow_sub_one_eq_mod]
        have hbit' : bit.val = byte.val / 2 ^ (j1.val % 8) % 2 := by
          rw [hbit, UScalar.val_and, show (1#u8).val = 2 ^ 1 - 1 from rfl,
            Nat.and_two_pow_sub_one_eq_mod, hsh, Nat.shiftRight_eq_div_pow, hr', pow_one]
        rw [hbyte, hq'] at hbit'
        rw [← hbit']
        cases hb : decide (bit = 1#u8) <;> simp_all [UScalar.eq_equiv]
      generalize hcurdef : decide (bit = 1#u8) = cur at hcur ⊢
      step as ⟨choice, hchoice⟩
      have hchoice01 : choice = 0#u8 ∨ choice = 1#u8 := by
        cases hbc : b ^^ cur <;> simp [hbc] at hchoice <;> scalar_tac
      step
      step as ⟨c, hc_valid, hc⟩
      have hj' : j.val = j1.val + 1 := by scalar_tac
      cases hsw : b ^^ cur
      · have hc0 : c = 0#u8 := by
          rw [hc, UScalar.eq_equiv]
          simpa [hsw] using hchoice
        step with hswap y0 y1 c hc_valid as ⟨x01, x11, hpr0, hpr1⟩
        obtain ⟨hx01, hx11⟩ := hpr0 hc0
        rw [hx01, hx11]
        step with hdad y0 y1 affine_u hy0 hy1 hu as ⟨P', Q', hP', hQ', hP'_lt, hQ'_lt⟩
        refine ⟨by omega, hP'_lt, hQ'_lt, ?_, by omega⟩
        rw [← hinv, hj', XZ.ladderLoop, ← hcur]
        simp only [XZ.ladderStep, hsw, XZ.cswap, Bool.false_eq_true, ↓reduceIte, hP', hQ']
      · have hc1 : c = 1#u8 := by
          rw [hc, UScalar.eq_equiv]
          simpa [hsw] using hchoice
        step with hswap y0 y1 c hc_valid as ⟨x01, x11, hpr0, hpr1⟩
        obtain ⟨hx01, hx11⟩ := hpr1 hc1
        rw [hx01, hx11]
        step with hdad y1 y0 affine_u hy1 hy0 hu as ⟨P', Q', hP', hQ', hP'_lt, hQ'_lt⟩
        refine ⟨by omega, hP'_lt, hQ'_lt, ?_, by omega⟩
        rw [← hinv, hj', XZ.ladderLoop, ← hcur]
        simp only [XZ.ladderStep, hsw, XZ.cswap, ↓reduceIte, hP', hQ']
    next hgt =>
      simp only [WP.spec_ok]
      have hj0 : j.val = 0 := by scalar_tac
      rw [hj0, XZ.ladderLoop] at hinv
      exact ⟨hy0, hy1, hinv⟩
  · exact ⟨hi, h0, h1, rfl⟩

end Curve25519Dalek.Backend

namespace Curve25519Dalek.montgomery

namespace MulShared1MontgomeryPointShared0ScalarMontgomeryPoint

open scoped Helpers.IndexStep in
open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
open ProjectivePoint.«x86_64-tables».Insts in
/-- The loop of `mul`: from bit `i - 1` down to bit `0`, the ladder's loop body. -/
@[local step]
private theorem mul.«x86_64-tables_loop_spec» (bytes : Array U8 32#usize)
    (affine_u : FieldElement51)
    (x0 x1 : ProjectivePoint.«x86_64-tables») (prev_bit : Bool) (i : Usize) (hi : i.val ≤ 255)
    (hu : affine_u.LimbsLt 54) (h0 : x0.LimbsLt 52) (h1 : x1.LimbsLt 52) :
    mul.«x86_64-tables_loop» bytes affine_u x0 x1 prev_bit i
      ⦃ (y0 y1 : ProjectivePoint.«x86_64-tables») (b : Bool) =>
        y0.LimbsLt 52 ∧ y1.LimbsLt 52 ∧
        (⟨y0.toXZ, y1.toXZ, b⟩ : XZ.LadderState (ZMod p)) =
          XZ.ladderLoop montgomery.a24 affine_u.toField (bytes.asNat 8) i.val
            ⟨x0.toXZ, x1.toXZ, prev_bit⟩ ⦄ := by
  rw [show mul.«x86_64-tables_loop» bytes affine_u x0 x1 prev_bit i =
      Backend.U64.mulLadder
        (subtle.ConditionallySelectable.conditional_swap.default SubtleConditionallySelectable)
        differential_add_and_double.«x86_64-tables» bytes affine_u x0 x1 prev_bit i from rfl]
  exact Backend.mulLadder_spec Backend.U64 ProjectivePoint.«x86_64-tables».toXZ
    (·.LimbsLt 52) _ _ SubtleConditionallySelectable.conditional_swap_spec
    «x86_64-tables».differential_add_and_double_spec bytes affine_u x0 x1 prev_bit i hi hu h0 h1

open scoped Helpers.IndexStep in
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
open ProjectivePoint.«i686-tables».Insts in
/-- The loop of `mul`: from bit `i - 1` down to bit `0`, the ladder's loop body. -/
@[local step]
private theorem mul.«i686-tables_loop_spec» (bytes : Array U8 32#usize)
    (affine_u : FieldElement2625)
    (x0 x1 : ProjectivePoint.«i686-tables») (prev_bit : Bool) (i : Usize) (hi : i.val ≤ 255)
    (hu : affine_u.LimbsLt 27) (h0 : x0.LimbsLt 26) (h1 : x1.LimbsLt 26) :
    mul.«i686-tables_loop» bytes affine_u x0 x1 prev_bit i
      ⦃ (y0 y1 : ProjectivePoint.«i686-tables») (b : Bool) =>
        y0.LimbsLt 26 ∧ y1.LimbsLt 26 ∧
        (⟨y0.toXZ, y1.toXZ, b⟩ : XZ.LadderState (ZMod p)) =
          XZ.ladderLoop montgomery.a24 affine_u.toField (bytes.asNat 8) i.val
            ⟨x0.toXZ, x1.toXZ, prev_bit⟩ ⦄ := by
  rw [show mul.«i686-tables_loop» bytes affine_u x0 x1 prev_bit i =
      Backend.U32.mulLadder
        (subtle.ConditionallySelectable.conditional_swap.default SubtleConditionallySelectable)
        differential_add_and_double.«i686-tables» bytes affine_u x0 x1 prev_bit i from rfl]
  exact Backend.mulLadder_spec Backend.U32 ProjectivePoint.«i686-tables».toXZ
    (·.LimbsLt 26) _ _ SubtleConditionallySelectable.conditional_swap_spec
    «i686-tables».differential_add_and_double_spec bytes affine_u x0 x1 prev_bit i hi hu h0 h1

open scoped Helpers.IndexStep in
open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `Mul<&Scalar> for &MontgomeryPoint`: the RFC 7748 ladder on the low `255` bits of the
scalar, encoded canonically. -/
@[step]
theorem mul.«x86_64-tables_spec» (self : MontgomeryPoint) (s : scalar.Scalar) :
    mul.«x86_64-tables» self s ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (s.asNat % 2 ^ 255) self.u) ⦄ := by
  unfold mul.«x86_64-tables»
  step as ⟨bytes, hbytes⟩
  step as ⟨u, hu, hu_lt⟩
  step as ⟨x0, hx0, hx0_lt⟩
  step as ⟨one, hone, hone_lt⟩
  step with mul.«x86_64-tables_loop_spec» bytes u x0 { U := u, W := one } false 255#usize
      (by decide) (limbs_lt_of_le (by decide) hu_lt) hx0_lt
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
  rw [hr, MontgomeryModel.ladder, MontgomeryModel.XZ.ladder, ladderXZ_mod, MontgomeryPoint.u_def,
    decodeU]
  congr 2
  have hu' : u.toField = ((self.asNat % 2 ^ 255 : ℕ) : ZMod p) := by
    rw [toField_def, hu, MontgomeryPoint.asNat_def]
  rw [← hu', MontgomeryModel.XZ.ladderXZ, scalar.Scalar.asNat_def, ← hbytes]
  rw [show (⟨⟨1, 0⟩, ⟨u.toField, 1⟩, false⟩ : XZ.LadderState (ZMod p)) =
      ⟨x0.toXZ, ({ U := u, W := one } : ProjectivePoint.«x86_64-tables»).toXZ, false⟩ by
    rw [hx0, ProjectivePoint.«x86_64-tables».toXZ_def, toField_eq_one_of_asNat hone], ← hst, hz]
  cases pb <;> rfl

open scoped Helpers.IndexStep in
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- `Mul<&Scalar> for &MontgomeryPoint`: the RFC 7748 ladder on the low `255` bits of the
scalar, encoded canonically. -/
@[step]
theorem mul.«i686-tables_spec» (self : MontgomeryPoint) (s : scalar.Scalar) :
    mul.«i686-tables» self s ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (s.asNat % 2 ^ 255) self.u) ⦄ := by
  unfold mul.«i686-tables»
  step as ⟨bytes, hbytes⟩
  step as ⟨u, hu, hu_lt⟩
  step as ⟨x0, hx0, hx0_lt⟩
  step as ⟨one, hone, hone_lt⟩
  step with mul.«i686-tables_loop_spec» bytes u x0 { U := u, W := one } false 255#usize
      (by decide) (limbs_lt_of_le (by decide) hu_lt) hx0_lt
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
  rw [hr, MontgomeryModel.ladder, MontgomeryModel.XZ.ladder, ladderXZ_mod, MontgomeryPoint.u_def,
    decodeU]
  congr 2
  have hu' : u.toField = ((self.asNat % 2 ^ 255 : ℕ) : ZMod p) := by
    rw [toField_def, MontgomeryPoint.asNat_def]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hu
  rw [← hu', MontgomeryModel.XZ.ladderXZ, scalar.Scalar.asNat_def, ← hbytes]
  rw [show (⟨⟨1, 0⟩, ⟨u.toField, 1⟩, false⟩ : XZ.LadderState (ZMod p)) =
      ⟨x0.toXZ, ({ U := u, W := one } : ProjectivePoint.«i686-tables»).toXZ, false⟩ by
    rw [hx0, ProjectivePoint.«i686-tables».toXZ_def, toField_eq_one_of_asNat hone], ← hst, hz]
  cases pb <;> rfl

open scoped Helpers.IndexStep in
open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
open ProjectivePoint.«x86_64-no-tables».Insts in
/-- The loop of `mul`: from bit `i - 1` down to bit `0`, the ladder's loop body. -/
@[local step]
private theorem mul.«x86_64-no-tables_loop_spec» (bytes : Array U8 32#usize)
    (affine_u : FieldElement51)
    (x0 x1 : ProjectivePoint.«x86_64-no-tables») (prev_bit : Bool) (i : Usize) (hi : i.val ≤ 255)
    (hu : affine_u.LimbsLt 54) (h0 : x0.LimbsLt 52) (h1 : x1.LimbsLt 52) :
    mul.«x86_64-no-tables_loop» bytes affine_u x0 x1 prev_bit i
      ⦃ (y0 y1 : ProjectivePoint.«x86_64-no-tables») (b : Bool) =>
        y0.LimbsLt 52 ∧ y1.LimbsLt 52 ∧
        (⟨y0.toXZ, y1.toXZ, b⟩ : XZ.LadderState (ZMod p)) =
          XZ.ladderLoop montgomery.a24 affine_u.toField (bytes.asNat 8) i.val
            ⟨x0.toXZ, x1.toXZ, prev_bit⟩ ⦄ := by
  rw [show mul.«x86_64-no-tables_loop» bytes affine_u x0 x1 prev_bit i =
      Backend.U64.mulLadder
        (subtle.ConditionallySelectable.conditional_swap.default SubtleConditionallySelectable)
        differential_add_and_double.«x86_64-no-tables» bytes affine_u x0 x1 prev_bit i from rfl]
  exact Backend.mulLadder_spec Backend.U64 ProjectivePoint.«x86_64-no-tables».toXZ
    (·.LimbsLt 52) _ _ SubtleConditionallySelectable.conditional_swap_spec
    «x86_64-no-tables».differential_add_and_double_spec bytes affine_u x0 x1 prev_bit i hi hu h0 h1

open scoped Helpers.IndexStep in
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
open ProjectivePoint.«i686-no-tables».Insts in
/-- The loop of `mul`: from bit `i - 1` down to bit `0`, the ladder's loop body. -/
@[local step]
private theorem mul.«i686-no-tables_loop_spec» (bytes : Array U8 32#usize)
    (affine_u : FieldElement2625)
    (x0 x1 : ProjectivePoint.«i686-no-tables») (prev_bit : Bool) (i : Usize) (hi : i.val ≤ 255)
    (hu : affine_u.LimbsLt 27) (h0 : x0.LimbsLt 26) (h1 : x1.LimbsLt 26) :
    mul.«i686-no-tables_loop» bytes affine_u x0 x1 prev_bit i
      ⦃ (y0 y1 : ProjectivePoint.«i686-no-tables») (b : Bool) =>
        y0.LimbsLt 26 ∧ y1.LimbsLt 26 ∧
        (⟨y0.toXZ, y1.toXZ, b⟩ : XZ.LadderState (ZMod p)) =
          XZ.ladderLoop montgomery.a24 affine_u.toField (bytes.asNat 8) i.val
            ⟨x0.toXZ, x1.toXZ, prev_bit⟩ ⦄ := by
  rw [show mul.«i686-no-tables_loop» bytes affine_u x0 x1 prev_bit i =
      Backend.U32.mulLadder
        (subtle.ConditionallySelectable.conditional_swap.default SubtleConditionallySelectable)
        differential_add_and_double.«i686-no-tables» bytes affine_u x0 x1 prev_bit i from rfl]
  exact Backend.mulLadder_spec Backend.U32 ProjectivePoint.«i686-no-tables».toXZ
    (·.LimbsLt 26) _ _ SubtleConditionallySelectable.conditional_swap_spec
    «i686-no-tables».differential_add_and_double_spec bytes affine_u x0 x1 prev_bit i hi hu h0 h1

open scoped Helpers.IndexStep in
open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `Mul<&Scalar> for &MontgomeryPoint`: the RFC 7748 ladder on the low `255` bits of the
scalar, encoded canonically. -/
@[step]
theorem mul.«x86_64-no-tables_spec» (self : MontgomeryPoint) (s : scalar.Scalar) :
    mul.«x86_64-no-tables» self s ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (s.asNat % 2 ^ 255) self.u) ⦄ := by
  unfold mul.«x86_64-no-tables»
  step as ⟨bytes, hbytes⟩
  step as ⟨u, hu, hu_lt⟩
  step as ⟨x0, hx0, hx0_lt⟩
  step as ⟨one, hone, hone_lt⟩
  step with mul.«x86_64-no-tables_loop_spec» bytes u x0 { U := u, W := one } false 255#usize
      (by decide) (limbs_lt_of_le (by decide) hu_lt) hx0_lt
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
  rw [hr, MontgomeryModel.ladder, MontgomeryModel.XZ.ladder, ladderXZ_mod, MontgomeryPoint.u_def,
    decodeU]
  congr 2
  have hu' : u.toField = ((self.asNat % 2 ^ 255 : ℕ) : ZMod p) := by
    rw [toField_def, hu, MontgomeryPoint.asNat_def]
  rw [← hu', MontgomeryModel.XZ.ladderXZ, scalar.Scalar.asNat_def, ← hbytes]
  rw [show (⟨⟨1, 0⟩, ⟨u.toField, 1⟩, false⟩ : XZ.LadderState (ZMod p)) =
      ⟨x0.toXZ, ({ U := u, W := one } : ProjectivePoint.«x86_64-no-tables»).toXZ, false⟩ by
    rw [hx0, ProjectivePoint.«x86_64-no-tables».toXZ_def, toField_eq_one_of_asNat hone], ← hst, hz]
  cases pb <;> rfl

open scoped Helpers.IndexStep in
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- `Mul<&Scalar> for &MontgomeryPoint`: the RFC 7748 ladder on the low `255` bits of the
scalar, encoded canonically. -/
@[step]
theorem mul.«i686-no-tables_spec» (self : MontgomeryPoint) (s : scalar.Scalar) :
    mul.«i686-no-tables» self s ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (s.asNat % 2 ^ 255) self.u) ⦄ := by
  unfold mul.«i686-no-tables»
  step as ⟨bytes, hbytes⟩
  step as ⟨u, hu, hu_lt⟩
  step as ⟨x0, hx0, hx0_lt⟩
  step as ⟨one, hone, hone_lt⟩
  step with mul.«i686-no-tables_loop_spec» bytes u x0 { U := u, W := one } false 255#usize
      (by decide) (limbs_lt_of_le (by decide) hu_lt) hx0_lt
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
  rw [hr, MontgomeryModel.ladder, MontgomeryModel.XZ.ladder, ladderXZ_mod, MontgomeryPoint.u_def,
    decodeU]
  congr 2
  have hu' : u.toField = ((self.asNat % 2 ^ 255 : ℕ) : ZMod p) := by
    rw [toField_def, MontgomeryPoint.asNat_def]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hu
  rw [← hu', MontgomeryModel.XZ.ladderXZ, scalar.Scalar.asNat_def, ← hbytes]
  rw [show (⟨⟨1, 0⟩, ⟨u.toField, 1⟩, false⟩ : XZ.LadderState (ZMod p)) =
      ⟨x0.toXZ, ({ U := u, W := one } : ProjectivePoint.«i686-no-tables»).toXZ, false⟩ by
    rw [hx0, ProjectivePoint.«i686-no-tables».toXZ_def, toField_eq_one_of_asNat hone], ← hst, hz]
  cases pb <;> rfl

end MulShared1MontgomeryPointShared0ScalarMontgomeryPoint

end Curve25519Dalek.montgomery

namespace Curve25519Dalek

namespace Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `Mul<&Scalar> for &MontgomeryPoint`: the RFC 7748 ladder on the low `255` bits of the
scalar, encoded canonically (x86_64 targets). -/
@[step]
theorem mul_spec (self : montgomery.MontgomeryPoint) (s : scalar.Scalar) :
    mul self s ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (s.asNat % 2 ^ 255) self.u) ⦄ := by
  unfold mul
  exact dispatch_all_spec
    (montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul.«x86_64-tables_spec» self
        s)
    (montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul.«x86_64-no-tables_spec»
        self s)
    (montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul.«i686-tables_spec» self
        s)
    (montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul.«i686-no-tables_spec»
        self s)

end Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint

namespace montgomery.MontgomeryPoint.Insts.CoreOpsArithMulSharedBScalarMontgomeryPoint

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `Mul<Scalar> for MontgomeryPoint` (by-value forms): as `&MontgomeryPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : montgomery.MontgomeryPoint) (rhs : scalar.Scalar) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (rhs.asNat % 2 ^ 255) self.u) ⦄ := by
  unfold mul
  exact Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint.mul_spec self rhs
     

end montgomery.MontgomeryPoint.Insts.CoreOpsArithMulSharedBScalarMontgomeryPoint

namespace SharedAMontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `Mul<Scalar> for MontgomeryPoint` (by-value forms): as `&MontgomeryPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : montgomery.MontgomeryPoint) (rhs : scalar.Scalar) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (rhs.asNat % 2 ^ 255) self.u) ⦄ := by
  unfold mul
  exact Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint.mul_spec self rhs
     

end SharedAMontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint

namespace montgomery.MontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `Mul<Scalar> for MontgomeryPoint` (by-value forms): as `&MontgomeryPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : montgomery.MontgomeryPoint) (rhs : scalar.Scalar) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (rhs.asNat % 2 ^ 255) self.u) ⦄ := by
  unfold mul
  exact Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint.mul_spec self rhs
     

end montgomery.MontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint

namespace Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `Mul<MontgomeryPoint> for Scalar`: as `&MontgomeryPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : montgomery.MontgomeryPoint) :
    mul self point ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (self.asNat % 2 ^ 255) point.u) ⦄ := by
  unfold mul
  exact Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint.mul_spec point self
     

end Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint

namespace scalar.Scalar.Insts.CoreOpsArithMulSharedBMontgomeryPointMontgomeryPoint

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `Mul<MontgomeryPoint> for Scalar`: as `&MontgomeryPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : montgomery.MontgomeryPoint) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (self.asNat % 2 ^ 255) rhs.u) ⦄ := by
  unfold mul
  exact Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint.mul_spec self rhs
     

end scalar.Scalar.Insts.CoreOpsArithMulSharedBMontgomeryPointMontgomeryPoint

namespace SharedAScalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `Mul<MontgomeryPoint> for Scalar`: as `&MontgomeryPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : montgomery.MontgomeryPoint) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (self.asNat % 2 ^ 255) rhs.u) ⦄ := by
  unfold mul
  exact Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint.mul_spec self rhs
     

end SharedAScalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint

namespace scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `Mul<MontgomeryPoint> for Scalar`: as `&MontgomeryPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : montgomery.MontgomeryPoint) :
    mul self rhs ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (self.asNat % 2 ^ 255) rhs.u) ⦄ := by
  unfold mul
  exact Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint.mul_spec self rhs
     

end scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint

end Curve25519Dalek
