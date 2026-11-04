/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
import Proofs.Edwards.Identity
import Proofs.Edwards.MulByPow2
import Proofs.Helpers.BasepointTable
import Proofs.Scalar.AsRadix2w
import Proofs.Window.LookupTableSelect
import Proofs.Window.LookupTableRadix32Select
import Proofs.Window.LookupTableRadix64Select
import Proofs.Window.LookupTableRadix128Select
import Proofs.Window.LookupTableRadix256Select
public section

/-! # `BasepointTable::mul_base` (the five basepoint tables)

The radix-`2^w` digits `a[i]` of the scalar (`as_radix_2w`): the odd digits are added first,
`a[i]` selected from row `(i - 1) / 2` (`a[i] 2^(w (i - 1)) • P`), then the sum is multiplied by
`2^w` and the even digits are added (`basepointTable.mulBaseLoop_spec`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.curve_models
open AffineNielsPoint.«x86_64-tables».Insts
open Curve25519Dalek.«Shared0AffineNielsPointx86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTable.«x86_64-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 54) (hP : self.Represents P)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 4 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 4)
    (hz : ∀ j : ℕ, j < 64 → 64 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«x86_64-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 64#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«x86_64-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 4 * k)) • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.mulBaseLoop_spec 64#usize (by decide)
    (window.LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointx86_64-tables»))
    a self P 4 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 8 * (i / 2) = 2 * 4 * (i / 2) by ring] at h
      exact window.«LookupTableAffineNielsPointx86_64-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 4 = 16 by norm_num] at this
          omega))
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTable.«x86_64-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 54) (hP : self.Represents P)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 4 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 4)
    (hz : ∀ j : ℕ, j < 64 → 64 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«x86_64-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 64#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«x86_64-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 4 * k)) • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.mulBaseLoop_spec 64#usize (by decide)
    (window.LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointx86_64-tables»))
    a self P 4 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 8 * (i / 2) = 2 * 4 * (i / 2) by ring] at h
      exact window.«LookupTableAffineNielsPointx86_64-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 4 = 16 by norm_num] at this
          omega))
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^4`): `s • P` for the point `P` the table represents
(unreduced, `s.asNat < 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTable.«x86_64-tables») (s : scalar.Scalar)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 4#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 64 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self P hself hP ha hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPointx86_64-tables».mul_by_pow_2_spec P1 4#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self P hself hP ha hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts
open AffineNielsPoint.«i686-tables».Insts
open Curve25519Dalek.«Shared0AffineNielsPointi686-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTable.«i686-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 27) (hP : self.Represents P)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 4 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 4)
    (hz : ∀ j : ℕ, j < 64 → 64 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«i686-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 64#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«i686-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 4 * k)) • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.i686.mulBaseLoop_spec 64#usize (by decide)
    (window.LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointi686-tables»))
    a self P 4 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 8 * (i / 2) = 2 * 4 * (i / 2) by ring] at h
      exact window.«LookupTableAffineNielsPointi686-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 4 = 16 by norm_num] at this
          omega))
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTable.«i686-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 27) (hP : self.Represents P)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 4 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 4)
    (hz : ∀ j : ℕ, j < 64 → 64 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«i686-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 64#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«i686-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 4 * k)) • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.i686.mulBaseLoop_spec 64#usize (by decide)
    (window.LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointi686-tables»))
    a self P 4 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 8 * (i / 2) = 2 * 4 * (i / 2) by ring] at h
      exact window.«LookupTableAffineNielsPointi686-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 4 = 16 by norm_num] at this
          omega))
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^4`): `s • P` for the point `P` the table represents
(unreduced, `s.asNat < 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTable.«i686-tables») (s : scalar.Scalar)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 4#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 64 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self P hself hP ha hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPointi686-tables».mul_by_pow_2_spec P1 4#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self P hself hP ha hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix32.«x86_64-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 54) (hP : self.Represents P)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 5 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 5)
    (hz : ∀ j : ℕ, j < 64 → 52 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«x86_64-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 52#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«x86_64-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 5 * k)) • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.mulBaseLoop_spec 52#usize (by decide)
    (window.LookupTableRadix32.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointx86_64-tables»))
    a self P 5 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 10 * (i / 2) = 2 * 5 * (i / 2) by ring] at h
      exact window.«LookupTableRadix32AffineNielsPointx86_64-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 5 = 32 by norm_num] at this
          omega))
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix32.«x86_64-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 54) (hP : self.Represents P)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 5 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 5)
    (hz : ∀ j : ℕ, j < 64 → 52 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«x86_64-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 52#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«x86_64-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 5 * k)) • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.mulBaseLoop_spec 52#usize (by decide)
    (window.LookupTableRadix32.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointx86_64-tables»))
    a self P 5 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 10 * (i / 2) = 2 * 5 * (i / 2) by ring] at h
      exact window.«LookupTableRadix32AffineNielsPointx86_64-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 5 = 32 by norm_num] at this
          omega))
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^5`): `s • P` for the point `P` the table represents
(unreduced, `s.asNat < 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTableRadix32.«x86_64-tables») (s : scalar.Scalar)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 5#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 52 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self P hself hP ha hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPointx86_64-tables».mul_by_pow_2_spec P1 5#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self P hself hP ha hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts
open AffineNielsPoint.«i686-tables».Insts
open Curve25519Dalek.«Shared0AffineNielsPointi686-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix32.«i686-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 27) (hP : self.Represents P)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 5 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 5)
    (hz : ∀ j : ℕ, j < 64 → 52 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«i686-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 52#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«i686-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 5 * k)) • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.i686.mulBaseLoop_spec 52#usize (by decide)
    (window.LookupTableRadix32.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointi686-tables»))
    a self P 5 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 10 * (i / 2) = 2 * 5 * (i / 2) by ring] at h
      exact window.«LookupTableRadix32AffineNielsPointi686-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 5 = 32 by norm_num] at this
          omega))
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix32.«i686-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 27) (hP : self.Represents P)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 5 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 5)
    (hz : ∀ j : ℕ, j < 64 → 52 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«i686-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 52#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«i686-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 5 * k)) • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.i686.mulBaseLoop_spec 52#usize (by decide)
    (window.LookupTableRadix32.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointi686-tables»))
    a self P 5 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 10 * (i / 2) = 2 * 5 * (i / 2) by ring] at h
      exact window.«LookupTableRadix32AffineNielsPointi686-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 5 = 32 by norm_num] at this
          omega))
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^5`): `s • P` for the point `P` the table represents
(unreduced, `s.asNat < 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTableRadix32.«i686-tables») (s : scalar.Scalar)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 5#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 52 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self P hself hP ha hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPointi686-tables».mul_by_pow_2_spec P1 5#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self P hself hP ha hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix64.«x86_64-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 54) (hP : self.Represents P)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 6 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 6)
    (hz : ∀ j : ℕ, j < 64 → 43 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«x86_64-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 43#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«x86_64-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 6 * k)) • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.mulBaseLoop_spec 43#usize (by decide)
    (window.LookupTableRadix64.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointx86_64-tables»))
    a self P 6 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 12 * (i / 2) = 2 * 6 * (i / 2) by ring] at h
      exact window.«LookupTableRadix64AffineNielsPointx86_64-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 6 = 64 by norm_num] at this
          omega))
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix64.«x86_64-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 54) (hP : self.Represents P)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 6 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 6)
    (hz : ∀ j : ℕ, j < 64 → 43 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«x86_64-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 43#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«x86_64-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 6 * k)) • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.mulBaseLoop_spec 43#usize (by decide)
    (window.LookupTableRadix64.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointx86_64-tables»))
    a self P 6 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 12 * (i / 2) = 2 * 6 * (i / 2) by ring] at h
      exact window.«LookupTableRadix64AffineNielsPointx86_64-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 6 = 64 by norm_num] at this
          omega))
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^6`): `s • P` for the point `P` the table represents
(unreduced, `s.asNat < 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTableRadix64.«x86_64-tables») (s : scalar.Scalar)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 6#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 43 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self P hself hP ha hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPointx86_64-tables».mul_by_pow_2_spec P1 6#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self P hself hP ha hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts
open AffineNielsPoint.«i686-tables».Insts
open Curve25519Dalek.«Shared0AffineNielsPointi686-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix64.«i686-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 27) (hP : self.Represents P)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 6 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 6)
    (hz : ∀ j : ℕ, j < 64 → 43 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«i686-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 43#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«i686-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 6 * k)) • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.i686.mulBaseLoop_spec 43#usize (by decide)
    (window.LookupTableRadix64.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointi686-tables»))
    a self P 6 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 12 * (i / 2) = 2 * 6 * (i / 2) by ring] at h
      exact window.«LookupTableRadix64AffineNielsPointi686-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 6 = 64 by norm_num] at this
          omega))
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix64.«i686-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 27) (hP : self.Represents P)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 6 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 6)
    (hz : ∀ j : ℕ, j < 64 → 43 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«i686-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 43#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«i686-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 6 * k)) • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.i686.mulBaseLoop_spec 43#usize (by decide)
    (window.LookupTableRadix64.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointi686-tables»))
    a self P 6 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 12 * (i / 2) = 2 * 6 * (i / 2) by ring] at h
      exact window.«LookupTableRadix64AffineNielsPointi686-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 6 = 64 by norm_num] at this
          omega))
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^6`): `s • P` for the point `P` the table represents
(unreduced, `s.asNat < 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTableRadix64.«i686-tables») (s : scalar.Scalar)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 6#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 43 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self P hself hP ha hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPointi686-tables».mul_by_pow_2_spec P1 6#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self P hself hP ha hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix128.«x86_64-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 54) (hP : self.Represents P)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 7 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 7)
    (hz : ∀ j : ℕ, j < 64 → 37 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«x86_64-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 37#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«x86_64-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 7 * k)) • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.mulBaseLoop_spec 37#usize (by decide)
    (window.LookupTableRadix128.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointx86_64-tables»))
    a self P 7 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 14 * (i / 2) = 2 * 7 * (i / 2) by ring] at h
      exact window.«LookupTableRadix128AffineNielsPointx86_64-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 7 = 128 by norm_num] at this
          omega))
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix128.«x86_64-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 54) (hP : self.Represents P)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 7 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 7)
    (hz : ∀ j : ℕ, j < 64 → 37 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«x86_64-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 37#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«x86_64-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 7 * k)) • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.mulBaseLoop_spec 37#usize (by decide)
    (window.LookupTableRadix128.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointx86_64-tables»))
    a self P 7 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 14 * (i / 2) = 2 * 7 * (i / 2) by ring] at h
      exact window.«LookupTableRadix128AffineNielsPointx86_64-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 7 = 128 by norm_num] at this
          omega))
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^7`): `s • P` for the point `P` the table represents
(unreduced, `s.asNat < 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTableRadix128.«x86_64-tables») (s : scalar.Scalar)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 7#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 37 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self P hself hP ha hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPointx86_64-tables».mul_by_pow_2_spec P1 7#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self P hself hP ha hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts
open AffineNielsPoint.«i686-tables».Insts
open Curve25519Dalek.«Shared0AffineNielsPointi686-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix128.«i686-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 27) (hP : self.Represents P)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 7 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 7)
    (hz : ∀ j : ℕ, j < 64 → 37 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«i686-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 37#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«i686-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 7 * k)) • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.i686.mulBaseLoop_spec 37#usize (by decide)
    (window.LookupTableRadix128.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointi686-tables»))
    a self P 7 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 14 * (i / 2) = 2 * 7 * (i / 2) by ring] at h
      exact window.«LookupTableRadix128AffineNielsPointi686-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 7 = 128 by norm_num] at this
          omega))
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix128.«i686-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 27) (hP : self.Represents P)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 7 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 7)
    (hz : ∀ j : ℕ, j < 64 → 37 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«i686-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 37#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«i686-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 7 * k)) • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.i686.mulBaseLoop_spec 37#usize (by decide)
    (window.LookupTableRadix128.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointi686-tables»))
    a self P 7 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 14 * (i / 2) = 2 * 7 * (i / 2) by ring] at h
      exact window.«LookupTableRadix128AffineNielsPointi686-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 7 = 128 by norm_num] at this
          omega))
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^7`): `s • P` for the point `P` the table represents
(unreduced, `s.asNat < 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTableRadix128.«i686-tables») (s : scalar.Scalar)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 7#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 37 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self P hself hP ha hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPointi686-tables».mul_by_pow_2_spec P1 7#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self P hself hP ha hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix256.«x86_64-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hz : ∀ j : ℕ, j < 64 → 33 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«x86_64-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 33#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«x86_64-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 8 * k)) • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.mulBaseLoop_spec 33#usize (by decide)
    (window.LookupTableRadix256.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointx86_64-tables»))
    a self P 8 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 16 * (i / 2) = 2 * 8 * (i / 2) by ring] at h
      exact window.«LookupTableRadix256AffineNielsPointx86_64-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h)
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix256.«x86_64-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hz : ∀ j : ℕ, j < 64 → 33 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«x86_64-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 33#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«x86_64-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 8 * k)) • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.mulBaseLoop_spec 33#usize (by decide)
    (window.LookupTableRadix256.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointx86_64-tables»))
    a self P 8 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 16 * (i / 2) = 2 * 8 * (i / 2) by ring] at h
      exact window.«LookupTableRadix256AffineNielsPointx86_64-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h)
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^8`): `s • P` for the point `P` the table represents
(unreduced, `s.asNat < 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTableRadix256.«x86_64-tables») (s : scalar.Scalar)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 8#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 33 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self P hself hP hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPointx86_64-tables».mul_by_pow_2_spec P1 8#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self P hself hP hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts
open AffineNielsPoint.«i686-tables».Insts
open Curve25519Dalek.«Shared0AffineNielsPointi686-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix256.«i686-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hz : ∀ j : ℕ, j < 64 → 33 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«i686-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 33#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«i686-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 8 * k)) • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.i686.mulBaseLoop_spec 33#usize (by decide)
    (window.LookupTableRadix256.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointi686-tables»))
    a self P 8 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 16 * (i / 2) = 2 * 8 * (i / 2) by ring] at h
      exact window.«LookupTableRadix256AffineNielsPointi686-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h)
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix256.«i686-tables») (P : curve25519.edwards.Point)
    (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hz : ∀ j : ℕ, j < 64 → 33 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«i686-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 33#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«i686-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 8 * k)) • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.i686.mulBaseLoop_spec 33#usize (by decide)
    (window.LookupTableRadix256.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointi686-tables»))
    a self P 8 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 16 * (i / 2) = 2 * 8 * (i / 2) by ring] at h
      exact window.«LookupTableRadix256AffineNielsPointi686-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h)
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^8`): `s • P` for the point `P` the table represents
(unreduced, `s.asNat < 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTableRadix256.«i686-tables») (s : scalar.Scalar)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 8#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 33 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self P hself hP hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPointi686-tables».mul_by_pow_2_spec P1 8#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self P hself hP hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

