module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
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
open AffineNielsPoint.«64bit-tables».Insts
open Curve25519Dalek.«Shared0AffineNielsPoint64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTable.«64bit-tables»)
    (hself : self.LimbsLt 54) (hP : self.IsTable)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 4 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 4)
    (hz : ∀ j : ℕ, j < 64 → 64 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«64bit-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 64#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«64bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 4 * k)) • self.point ∧ r.LimbsLt
            52 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.mulBaseLoop_spec 64#usize (by decide)
    (window.LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint64bit-tables»))
    a self self.point 4 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 8 * (i / 2) = 2 * 4 * (i / 2) by ring] at h
      exact window.«LookupTableAffineNielsPoint64bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 4 = 16 by norm_num] at this
          omega))
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTable.«64bit-tables»)
    (hself : self.LimbsLt 54) (hP : self.IsTable)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 4 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 4)
    (hz : ∀ j : ℕ, j < 64 → 64 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«64bit-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 64#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«64bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 4 * k)) • self.point ∧ r.LimbsLt
            52 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.mulBaseLoop_spec 64#usize (by decide)
    (window.LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint64bit-tables»))
    a self self.point 4 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 8 * (i / 2) = 2 * 4 * (i / 2) by ring] at h
      exact window.«LookupTableAffineNielsPoint64bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 4 = 16 by norm_num] at this
          omega))
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^4`): `s • self.point` (unreduced,
`s.asNat < 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTable.«64bit-tables») (s : scalar.Scalar)
    (hself : self.LimbsLt 54) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 4#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 64 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self hself hP ha hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPoint64bit-tables».mul_by_pow_2_spec P1 4#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self hself hP ha hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«32bit-tables».Insts
open AffineNielsPoint.«32bit-tables».Insts
open Curve25519Dalek.«Shared0AffineNielsPoint32bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTable.«32bit-tables»)
    (hself : self.LimbsLt 27) (hP : self.IsTable)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 4 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 4)
    (hz : ∀ j : ℕ, j < 64 → 64 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«32bit-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 64#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«32bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 4 * k)) • self.point ∧ r.LimbsLt
            26 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.bits32.mulBaseLoop_spec 64#usize (by decide)
    (window.LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint32bit-tables»))
    a self self.point 4 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 8 * (i / 2) = 2 * 4 * (i / 2) by ring] at h
      exact window.«LookupTableAffineNielsPoint32bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 4 = 16 by norm_num] at this
          omega))
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTable.«32bit-tables»)
    (hself : self.LimbsLt 27) (hP : self.IsTable)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 4 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 4)
    (hz : ∀ j : ℕ, j < 64 → 64 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«32bit-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 64#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«32bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 4 * k)) • self.point ∧ r.LimbsLt
            26 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.bits32.mulBaseLoop_spec 64#usize (by decide)
    (window.LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint32bit-tables»))
    a self self.point 4 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 8 * (i / 2) = 2 * 4 * (i / 2) by ring] at h
      exact window.«LookupTableAffineNielsPoint32bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 4 = 16 by norm_num] at this
          omega))
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^4`): `s • self.point` (unreduced,
`s.asNat < 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTable.«32bit-tables») (s : scalar.Scalar)
    (hself : self.LimbsLt 27) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 4#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 64 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self hself hP ha hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPoint32bit-tables».mul_by_pow_2_spec P1 4#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self hself hP ha hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix32.«64bit-tables»)
    (hself : self.LimbsLt 54) (hP : self.IsTable)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 5 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 5)
    (hz : ∀ j : ℕ, j < 64 → 52 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«64bit-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 52#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«64bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 5 * k)) • self.point ∧ r.LimbsLt
            52 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.mulBaseLoop_spec 52#usize (by decide)
    (window.LookupTableRadix32.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint64bit-tables»))
    a self self.point 5 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 10 * (i / 2) = 2 * 5 * (i / 2) by ring] at h
      exact window.«LookupTableRadix32AffineNielsPoint64bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 5 = 32 by norm_num] at this
          omega))
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix32.«64bit-tables»)
    (hself : self.LimbsLt 54) (hP : self.IsTable)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 5 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 5)
    (hz : ∀ j : ℕ, j < 64 → 52 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«64bit-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 52#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«64bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 5 * k)) • self.point ∧ r.LimbsLt
            52 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.mulBaseLoop_spec 52#usize (by decide)
    (window.LookupTableRadix32.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint64bit-tables»))
    a self self.point 5 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 10 * (i / 2) = 2 * 5 * (i / 2) by ring] at h
      exact window.«LookupTableRadix32AffineNielsPoint64bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 5 = 32 by norm_num] at this
          omega))
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^5`): `s • self.point` (unreduced,
`s.asNat < 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTableRadix32.«64bit-tables»)
    (s : scalar.Scalar) (hself : self.LimbsLt 54) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 5#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 52 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self hself hP ha hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPoint64bit-tables».mul_by_pow_2_spec P1 5#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self hself hP ha hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«32bit-tables».Insts
open AffineNielsPoint.«32bit-tables».Insts
open Curve25519Dalek.«Shared0AffineNielsPoint32bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix32.«32bit-tables»)
    (hself : self.LimbsLt 27) (hP : self.IsTable)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 5 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 5)
    (hz : ∀ j : ℕ, j < 64 → 52 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«32bit-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 52#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«32bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 5 * k)) • self.point ∧ r.LimbsLt
            26 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.bits32.mulBaseLoop_spec 52#usize (by decide)
    (window.LookupTableRadix32.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint32bit-tables»))
    a self self.point 5 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 10 * (i / 2) = 2 * 5 * (i / 2) by ring] at h
      exact window.«LookupTableRadix32AffineNielsPoint32bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 5 = 32 by norm_num] at this
          omega))
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix32.«32bit-tables»)
    (hself : self.LimbsLt 27) (hP : self.IsTable)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 5 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 5)
    (hz : ∀ j : ℕ, j < 64 → 52 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«32bit-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 52#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«32bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 5 * k)) • self.point ∧ r.LimbsLt
            26 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.bits32.mulBaseLoop_spec 52#usize (by decide)
    (window.LookupTableRadix32.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint32bit-tables»))
    a self self.point 5 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 10 * (i / 2) = 2 * 5 * (i / 2) by ring] at h
      exact window.«LookupTableRadix32AffineNielsPoint32bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 5 = 32 by norm_num] at this
          omega))
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^5`): `s • self.point` (unreduced,
`s.asNat < 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTableRadix32.«32bit-tables») (s : scalar.Scalar)
    (hself : self.LimbsLt 27) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 5#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 52 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self hself hP ha hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPoint32bit-tables».mul_by_pow_2_spec P1 5#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self hself hP ha hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix64.«64bit-tables»)
    (hself : self.LimbsLt 54) (hP : self.IsTable)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 6 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 6)
    (hz : ∀ j : ℕ, j < 64 → 43 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«64bit-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 43#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«64bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 6 * k)) • self.point ∧ r.LimbsLt
            52 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.mulBaseLoop_spec 43#usize (by decide)
    (window.LookupTableRadix64.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint64bit-tables»))
    a self self.point 6 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 12 * (i / 2) = 2 * 6 * (i / 2) by ring] at h
      exact window.«LookupTableRadix64AffineNielsPoint64bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 6 = 64 by norm_num] at this
          omega))
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix64.«64bit-tables»)
    (hself : self.LimbsLt 54) (hP : self.IsTable)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 6 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 6)
    (hz : ∀ j : ℕ, j < 64 → 43 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«64bit-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 43#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«64bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 6 * k)) • self.point ∧ r.LimbsLt
            52 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.mulBaseLoop_spec 43#usize (by decide)
    (window.LookupTableRadix64.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint64bit-tables»))
    a self self.point 6 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 12 * (i / 2) = 2 * 6 * (i / 2) by ring] at h
      exact window.«LookupTableRadix64AffineNielsPoint64bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 6 = 64 by norm_num] at this
          omega))
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^6`): `s • self.point` (unreduced,
`s.asNat < 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTableRadix64.«64bit-tables»)
    (s : scalar.Scalar) (hself : self.LimbsLt 54) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 6#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 43 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self hself hP ha hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPoint64bit-tables».mul_by_pow_2_spec P1 6#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self hself hP ha hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«32bit-tables».Insts
open AffineNielsPoint.«32bit-tables».Insts
open Curve25519Dalek.«Shared0AffineNielsPoint32bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix64.«32bit-tables»)
    (hself : self.LimbsLt 27) (hP : self.IsTable)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 6 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 6)
    (hz : ∀ j : ℕ, j < 64 → 43 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«32bit-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 43#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«32bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 6 * k)) • self.point ∧ r.LimbsLt
            26 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.bits32.mulBaseLoop_spec 43#usize (by decide)
    (window.LookupTableRadix64.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint32bit-tables»))
    a self self.point 6 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 12 * (i / 2) = 2 * 6 * (i / 2) by ring] at h
      exact window.«LookupTableRadix64AffineNielsPoint32bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 6 = 64 by norm_num] at this
          omega))
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix64.«32bit-tables»)
    (hself : self.LimbsLt 27) (hP : self.IsTable)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 6 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 6)
    (hz : ∀ j : ℕ, j < 64 → 43 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«32bit-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 43#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«32bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 6 * k)) • self.point ∧ r.LimbsLt
            26 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.bits32.mulBaseLoop_spec 43#usize (by decide)
    (window.LookupTableRadix64.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint32bit-tables»))
    a self self.point 6 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 12 * (i / 2) = 2 * 6 * (i / 2) by ring] at h
      exact window.«LookupTableRadix64AffineNielsPoint32bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 6 = 64 by norm_num] at this
          omega))
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^6`): `s • self.point` (unreduced,
`s.asNat < 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTableRadix64.«32bit-tables») (s : scalar.Scalar)
    (hself : self.LimbsLt 27) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 6#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 43 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self hself hP ha hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPoint32bit-tables».mul_by_pow_2_spec P1 6#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self hself hP ha hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix128.«64bit-tables»)
    (hself : self.LimbsLt 54) (hP : self.IsTable)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 7 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 7)
    (hz : ∀ j : ℕ, j < 64 → 37 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«64bit-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 37#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«64bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 7 * k)) • self.point ∧ r.LimbsLt
            52 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.mulBaseLoop_spec 37#usize (by decide)
    (window.LookupTableRadix128.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint64bit-tables»))
    a self self.point 7 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 14 * (i / 2) = 2 * 7 * (i / 2) by ring] at h
      exact window.«LookupTableRadix128AffineNielsPoint64bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 7 = 128 by norm_num] at this
          omega))
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix128.«64bit-tables»)
    (hself : self.LimbsLt 54) (hP : self.IsTable)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 7 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 7)
    (hz : ∀ j : ℕ, j < 64 → 37 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«64bit-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 37#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«64bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 7 * k)) • self.point ∧ r.LimbsLt
            52 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.mulBaseLoop_spec 37#usize (by decide)
    (window.LookupTableRadix128.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint64bit-tables»))
    a self self.point 7 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 14 * (i / 2) = 2 * 7 * (i / 2) by ring] at h
      exact window.«LookupTableRadix128AffineNielsPoint64bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 7 = 128 by norm_num] at this
          omega))
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^7`): `s • self.point` (unreduced,
`s.asNat < 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTableRadix128.«64bit-tables»)
    (s : scalar.Scalar) (hself : self.LimbsLt 54) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 7#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 37 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self hself hP ha hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPoint64bit-tables».mul_by_pow_2_spec P1 7#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self hself hP ha hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«32bit-tables».Insts
open AffineNielsPoint.«32bit-tables».Insts
open Curve25519Dalek.«Shared0AffineNielsPoint32bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix128.«32bit-tables»)
    (hself : self.LimbsLt 27) (hP : self.IsTable)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 7 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 7)
    (hz : ∀ j : ℕ, j < 64 → 37 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«32bit-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 37#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«32bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 7 * k)) • self.point ∧ r.LimbsLt
            26 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.bits32.mulBaseLoop_spec 37#usize (by decide)
    (window.LookupTableRadix128.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint32bit-tables»))
    a self self.point 7 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 14 * (i / 2) = 2 * 7 * (i / 2) by ring] at h
      exact window.«LookupTableRadix128AffineNielsPoint32bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 7 = 128 by norm_num] at this
          omega))
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix128.«32bit-tables»)
    (hself : self.LimbsLt 27) (hP : self.IsTable)
    (ha : ∀ i : ℕ, i < 64 → -2 ^ 7 ≤ 2 * a[i]!.val ∧ 2 * a[i]!.val ≤ 2 ^ 7)
    (hz : ∀ j : ℕ, j < 64 → 37 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«32bit-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 37#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«32bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 7 * k)) • self.point ∧ r.LimbsLt
            26 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.bits32.mulBaseLoop_spec 37#usize (by decide)
    (window.LookupTableRadix128.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint32bit-tables»))
    a self self.point 7 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 14 * (i / 2) = 2 * 7 * (i / 2) by ring] at h
      exact window.«LookupTableRadix128AffineNielsPoint32bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h
        (by
          have := ha i (by scalar_tac)
          rw [show (2 : ℤ) ^ 7 = 128 by norm_num] at this
          omega))
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^7`): `s • self.point` (unreduced,
`s.asNat < 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTableRadix128.«32bit-tables») (s : scalar.Scalar)
    (hself : self.LimbsLt 27) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 7#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 37 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self hself hP ha hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPoint32bit-tables».mul_by_pow_2_spec P1 7#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self hself hP ha hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix256.«64bit-tables»)
    (hself : self.LimbsLt 54) (hP : self.IsTable)
    (hz : ∀ j : ℕ, j < 64 → 33 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«64bit-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 33#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«64bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 8 * k)) • self.point ∧ r.LimbsLt
            52 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.mulBaseLoop_spec 33#usize (by decide)
    (window.LookupTableRadix256.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint64bit-tables»))
    a self self.point 8 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 16 * (i / 2) = 2 * 8 * (i / 2) by ring] at h
      exact window.«LookupTableRadix256AffineNielsPoint64bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h)
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix256.«64bit-tables»)
    (hself : self.LimbsLt 54) (hP : self.IsTable)
    (hz : ∀ j : ℕ, j < 64 → 33 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«64bit-tables»)
    (hQ : Q.LimbsLt 52) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 33#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«64bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 8 * k)) • self.point ∧ r.LimbsLt
            52 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.mulBaseLoop_spec 33#usize (by decide)
    (window.LookupTableRadix256.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint64bit-tables»))
    a self self.point 8 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 16 * (i / 2) = 2 * 8 * (i / 2) by ring] at h
      exact window.«LookupTableRadix256AffineNielsPoint64bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h)
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^8`): `s • self.point` (unreduced,
`s.asNat < 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTableRadix256.«64bit-tables»)
    (s : scalar.Scalar) (hself : self.LimbsLt 54) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 8#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 33 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self hself hP hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPoint64bit-tables».mul_by_pow_2_spec P1 8#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self hself hP hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«32bit-tables».Insts
open AffineNielsPoint.«32bit-tables».Insts
open Curve25519Dalek.«Shared0AffineNielsPoint32bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»

/-- Loop 0 of `mul_base`: the digits `1 + 2 k`. -/
@[local step]
private theorem mul_base_loop0_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix256.«32bit-tables»)
    (hself : self.LimbsLt 27) (hP : self.IsTable)
    (hz : ∀ j : ℕ, j < 64 → 33 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«32bit-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop0
      { iter := { start := 1#usize, «end» := 33#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«32bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[1 + 2 * k]!.val * 2 ^ (2 * 8 * k)) • self.point ∧ r.LimbsLt
            26 ⦄ := by
  unfold mul_base_loop0
  exact basepointTable.bits32.mulBaseLoop_spec 33#usize (by decide)
    (window.LookupTableRadix256.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint32bit-tables»))
    a self self.point 8 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 16 * (i / 2) = 2 * 8 * (i / 2) by ring] at h
      exact window.«LookupTableRadix256AffineNielsPoint32bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h)
    hz 1#usize (by decide) (by decide) Q hQ hon

/-- Loop 1 of `mul_base`: the digits `0 + 2 k`. -/
@[local step]
private theorem mul_base_loop1_spec (a : Array I8 64#usize)
    (self : EdwardsBasepointTableRadix256.«32bit-tables»)
    (hself : self.LimbsLt 27) (hP : self.IsTable)
    (hz : ∀ j : ℕ, j < 64 → 33 ≤ j → a[j]!.val = 0) (Q : EdwardsPoint.«32bit-tables»)
    (hQ : Q.LimbsLt 26) (hon : Q.OnCurve) :
    mul_base_loop1
      { iter := { start := 0#usize, «end» := 33#usize }, step_by := 2#usize } a self Q
      ⦃ (r : EdwardsPoint.«32bit-tables») => r.OnCurve ∧
      r.toPoint = Q.toPoint +
        (∑ k ∈ Finset.range 32, a[0 + 2 * k]!.val * 2 ^ (2 * 8 * k)) • self.point ∧ r.LimbsLt
            26 ⦄ := by
  unfold mul_base_loop1
  exact basepointTable.bits32.mulBaseLoop_spec 33#usize (by decide)
    (window.LookupTableRadix256.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint32bit-tables»))
    a self self.point 8 (fun i hi => by
      have h := hP (i / 2) (by scalar_tac)
      rw [show 16 * (i / 2) = 2 * 8 * (i / 2) by ring] at h
      exact window.«LookupTableRadix256AffineNielsPoint32bit-tables».select_spec _ _ _
        (hself (i / 2) (by scalar_tac)) h)
    hz 0#usize (by decide) (by decide) Q hQ hon

/-- `BasepointTable::mul_base` (radix `2^8`): `s • self.point` (unreduced,
`s.asNat < 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_base_spec (self : EdwardsBasepointTableRadix256.«32bit-tables») (s : scalar.Scalar)
    (hself : self.LimbsLt 27) (hP : self.IsTable)
    (hs : s.asNat < 2 ^ 255) :
    mul_base self s ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = s.asNat • self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_base
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,
    show ¬(2#usize).val = 0 by decide, ite_false, bind_ok]
  step with scalar.Scalar.as_radix_2w_spec s 8#usize (by decide) hs as ⟨a, haval, hlow, ha, hz⟩
  have hz' : ∀ j : ℕ, j < 64 → 33 ≤ j → a[j]!.val = 0 := fun j hj hj' =>
    hz j hj (by omega)
  step with EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨P0, hP0on, hP0, hP0b⟩
  step with mul_base_loop0_spec a self hself hP hz' P0 hP0b hP0on as ⟨P1, hP1on, hP1, hP1b⟩
  step with «EdwardsPoint32bit-tables».mul_by_pow_2_spec P1 8#u32 hP1b hP1on (by decide)
    as ⟨P2, hP2on, hP2, hP2b⟩
  step with mul_base_loop1_spec a self hself hP hz' P2 hP2b hP2on as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hP2, hP1, hP0, zero_add, basepointTable.pow_nsmul_add_zsmul,
    ← basepointTable.asInt_eq_even_add_odd, haval, natCast_zsmul]

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«32bit-tables».Insts

