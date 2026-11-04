/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Edwards.Torsion
public import Defs.Edwards
import Proofs.Backend.Serial.U64.Constants.EightTorsion
import Proofs.Edwards.Add
import Proofs.Helpers.Array
import Proofs.Backend.Serial.U32.Constants.EightTorsion
public section

/-! # `RistrettoPoint::coset4` (private, for debugging)

The coset `P + E[4]`: `P` and `P` plus the 4-torsion points `eightTorsion 2, 4, 6`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.ristretto

namespace «RistrettoPointx86_64-tables»

open edwards.EdwardsPoint.«x86_64-tables».Insts in
/-- `RistrettoPoint::coset4`: `[P, P + T₂, P + T₄, P + T₆]` for the 8-torsion points `Tᵢ`
(`eightTorsion i`); limbs `< 2^52`. -/
theorem coset4_spec (self : RistrettoPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    coset4 self ⦃ (r : Array edwards.EdwardsPoint.«x86_64-tables» 4#usize) =>
      r[0]! = self ∧ ∀ i : Fin 3, r[i.val + 1]!.OnCurve ∧
        r[i.val + 1]!.toPoint = self.toPoint + eightTorsion ⟨2 * (i.val + 1), by omega⟩ ∧
        r[i.val + 1]!.LimbsLt 52 ⦄ := by
  unfold coset4
  step with backend.serial.u64.constants.«x86_64-tables».EIGHT_TORSION_spec_point as ⟨a, ha⟩
  step with Array.index_usize_getElem!_spec as ⟨t2, ht2⟩
  obtain ⟨h2on, h2, h2b⟩ := ht2 ▸ ha 2
  step with «CoreOpsArithAddEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».add_spec_point
    self t2 hself h2b hon h2on as ⟨p1, hp1on, hp1, hp1b⟩
  step with Array.index_usize_getElem!_spec as ⟨t4, ht4⟩
  obtain ⟨h4on, h4, h4b⟩ := ht4 ▸ ha 4
  step with «CoreOpsArithAddEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».add_spec_point
    self t4 hself h4b hon h4on as ⟨p2, hp2on, hp2, hp2b⟩
  step with Array.index_usize_getElem!_spec as ⟨t6, ht6⟩
  obtain ⟨h6on, h6, h6b⟩ := ht6 ▸ ha 6
  step with «CoreOpsArithAddEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».add_spec_point
    self t6 hself h6b hon h6on as ⟨p3, hp3on, hp3, hp3b⟩
  refine ⟨by simp, fun i => ?_⟩
  fin_cases i
  · simpa [hp1, h2] using ⟨hp1on, hp1b⟩
  · simpa [hp2, h4] using ⟨hp2on, hp2b⟩
  · simpa [hp3, h6] using ⟨hp3on, hp3b⟩

end «RistrettoPointx86_64-tables»

namespace «RistrettoPointi686-tables»

open edwards.EdwardsPoint.«i686-tables».Insts in
/-- `RistrettoPoint::coset4`: `[P, P + T₂, P + T₄, P + T₆]` for the 8-torsion points `Tᵢ`
(`eightTorsion i`); limbs `< 2^26`. -/
theorem coset4_spec (self : RistrettoPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    coset4 self ⦃ (r : Array edwards.EdwardsPoint.«i686-tables» 4#usize) =>
      r[0]! = self ∧ ∀ i : Fin 3, r[i.val + 1]!.OnCurve ∧
        r[i.val + 1]!.toPoint = self.toPoint + eightTorsion ⟨2 * (i.val + 1), by omega⟩ ∧
        r[i.val + 1]!.LimbsLt 26 ⦄ := by
  unfold coset4
  step with backend.serial.u32.constants.«i686-tables».EIGHT_TORSION_spec_point as ⟨a, ha⟩
  step with Array.index_usize_getElem!_spec as ⟨t2, ht2⟩
  obtain ⟨h2on, h2, h2b⟩ := ht2 ▸ ha 2
  step with «CoreOpsArithAddEdwardsPointi686-tablesEdwardsPointi686-tables».add_spec_point
    self t2 hself h2b hon h2on as ⟨p1, hp1on, hp1, hp1b⟩
  step with Array.index_usize_getElem!_spec as ⟨t4, ht4⟩
  obtain ⟨h4on, h4, h4b⟩ := ht4 ▸ ha 4
  step with «CoreOpsArithAddEdwardsPointi686-tablesEdwardsPointi686-tables».add_spec_point
    self t4 hself h4b hon h4on as ⟨p2, hp2on, hp2, hp2b⟩
  step with Array.index_usize_getElem!_spec as ⟨t6, ht6⟩
  obtain ⟨h6on, h6, h6b⟩ := ht6 ▸ ha 6
  step with «CoreOpsArithAddEdwardsPointi686-tablesEdwardsPointi686-tables».add_spec_point
    self t6 hself h6b hon h6on as ⟨p3, hp3on, hp3, hp3b⟩
  refine ⟨by simp, fun i => ?_⟩
  fin_cases i
  · simpa [hp1, h2] using ⟨hp1on, hp1b⟩
  · simpa [hp2, h4] using ⟨hp2on, hp2b⟩
  · simpa [hp3, h6] using ⟨hp3on, hp3b⟩

end «RistrettoPointi686-tables»

namespace «RistrettoPointx86_64-no-tables»

open edwards.EdwardsPoint.«x86_64-no-tables».Insts in
/-- `RistrettoPoint::coset4`: `[P, P + T₂, P + T₄, P + T₆]` for the 8-torsion points `Tᵢ`
(`eightTorsion i`); limbs `< 2^52`. -/
theorem coset4_spec (self : RistrettoPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    coset4 self ⦃ (r : Array edwards.EdwardsPoint.«x86_64-no-tables» 4#usize) =>
      r[0]! = self ∧ ∀ i : Fin 3, r[i.val + 1]!.OnCurve ∧
        r[i.val + 1]!.toPoint = self.toPoint + eightTorsion ⟨2 * (i.val + 1), by omega⟩ ∧
        r[i.val + 1]!.LimbsLt 52 ⦄ := by
  unfold coset4
  step with backend.serial.u64.constants.«x86_64-no-tables».EIGHT_TORSION_spec_point as ⟨a, ha⟩
  step with Array.index_usize_getElem!_spec as ⟨t2, ht2⟩
  obtain ⟨h2on, h2, h2b⟩ := ht2 ▸ ha 2
  step with «CoreOpsArithAddEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables».add_spec_point
    self t2 hself h2b hon h2on as ⟨p1, hp1on, hp1, hp1b⟩
  step with Array.index_usize_getElem!_spec as ⟨t4, ht4⟩
  obtain ⟨h4on, h4, h4b⟩ := ht4 ▸ ha 4
  step with «CoreOpsArithAddEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables».add_spec_point
    self t4 hself h4b hon h4on as ⟨p2, hp2on, hp2, hp2b⟩
  step with Array.index_usize_getElem!_spec as ⟨t6, ht6⟩
  obtain ⟨h6on, h6, h6b⟩ := ht6 ▸ ha 6
  step with «CoreOpsArithAddEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables».add_spec_point
    self t6 hself h6b hon h6on as ⟨p3, hp3on, hp3, hp3b⟩
  refine ⟨by simp, fun i => ?_⟩
  fin_cases i
  · simpa [hp1, h2] using ⟨hp1on, hp1b⟩
  · simpa [hp2, h4] using ⟨hp2on, hp2b⟩
  · simpa [hp3, h6] using ⟨hp3on, hp3b⟩

end «RistrettoPointx86_64-no-tables»

namespace «RistrettoPointi686-no-tables»

open edwards.EdwardsPoint.«i686-no-tables».Insts in
/-- `RistrettoPoint::coset4`: `[P, P + T₂, P + T₄, P + T₆]` for the 8-torsion points `Tᵢ`
(`eightTorsion i`); limbs `< 2^26`. -/
theorem coset4_spec (self : RistrettoPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    coset4 self ⦃ (r : Array edwards.EdwardsPoint.«i686-no-tables» 4#usize) =>
      r[0]! = self ∧ ∀ i : Fin 3, r[i.val + 1]!.OnCurve ∧
        r[i.val + 1]!.toPoint = self.toPoint + eightTorsion ⟨2 * (i.val + 1), by omega⟩ ∧
        r[i.val + 1]!.LimbsLt 26 ⦄ := by
  unfold coset4
  step with backend.serial.u32.constants.«i686-no-tables».EIGHT_TORSION_spec_point as ⟨a, ha⟩
  step with Array.index_usize_getElem!_spec as ⟨t2, ht2⟩
  obtain ⟨h2on, h2, h2b⟩ := ht2 ▸ ha 2
  step with «CoreOpsArithAddEdwardsPointi686-no-tablesEdwardsPointi686-no-tables».add_spec_point
    self t2 hself h2b hon h2on as ⟨p1, hp1on, hp1, hp1b⟩
  step with Array.index_usize_getElem!_spec as ⟨t4, ht4⟩
  obtain ⟨h4on, h4, h4b⟩ := ht4 ▸ ha 4
  step with «CoreOpsArithAddEdwardsPointi686-no-tablesEdwardsPointi686-no-tables».add_spec_point
    self t4 hself h4b hon h4on as ⟨p2, hp2on, hp2, hp2b⟩
  step with Array.index_usize_getElem!_spec as ⟨t6, ht6⟩
  obtain ⟨h6on, h6, h6b⟩ := ht6 ▸ ha 6
  step with «CoreOpsArithAddEdwardsPointi686-no-tablesEdwardsPointi686-no-tables».add_spec_point
    self t6 hself h6b hon h6on as ⟨p3, hp3on, hp3, hp3b⟩
  refine ⟨by simp, fun i => ?_⟩
  fin_cases i
  · simpa [hp1, h2] using ⟨hp1on, hp1b⟩
  · simpa [hp2, h4] using ⟨hp2on, hp2b⟩
  · simpa [hp3, h6] using ⟨hp3on, hp3b⟩

end «RistrettoPointi686-no-tables»

end Curve25519Dalek.ristretto
