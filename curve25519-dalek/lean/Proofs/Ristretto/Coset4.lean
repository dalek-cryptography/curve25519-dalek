module
public import Curve25519Dalek.Funs
public import Proofs.Curve25519.Edwards.Torsion
public import Proofs.Representation.Edwards
import Proofs.Backend.Serial.U64.Constants.EightTorsion
import Proofs.Edwards.Add
import Proofs.Helpers.Array
import Proofs.Backend.Serial.U32.Constants.EightTorsion
public section

/-! # `RistrettoPoint::coset4` (private, for debugging)

The coset `P + E[4]`: `P` and `P` plus the 4-torsion points `2 • torsion8`, `4 • torsion8`, `6 •
    torsion8`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.ristretto

namespace «RistrettoPoint64bit-tables»

open edwards.EdwardsPoint.«64bit-tables».Insts in
/-- `RistrettoPoint::coset4`: `[P, P + T₂, P + T₄, P + T₆]` for the 8-torsion points `Tᵢ`
(`i • torsion8`); limbs `< 2^52`. -/
theorem coset4_spec (self : RistrettoPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    coset4 self ⦃ (r : Array edwards.EdwardsPoint.«64bit-tables» 4#usize) =>
      r[0]! = self ∧ ∀ i : Fin 3, r[i.val + 1]!.OnCurve ∧
        r[i.val + 1]!.toPoint = self.toPoint + (2 * (i.val + 1)) • torsion8 ∧
        r[i.val + 1]!.LimbsLt 52 ⦄ := by
  unfold coset4
  step with backend.serial.u64.constants.«64bit-tables».EIGHT_TORSION_spec as ⟨a, ha⟩
  step with Array.index_usize_getElem!_spec as ⟨t2, ht2⟩
  obtain ⟨h2on, h2, h2b⟩ := ht2 ▸ ha 2
  step with «CoreOpsArithAddEdwardsPoint64bit-tablesEdwardsPoint64bit-tables».add_spec
    self t2 hself h2b hon h2on as ⟨p1, hp1on, hp1, hp1b⟩
  step with Array.index_usize_getElem!_spec as ⟨t4, ht4⟩
  obtain ⟨h4on, h4, h4b⟩ := ht4 ▸ ha 4
  step with «CoreOpsArithAddEdwardsPoint64bit-tablesEdwardsPoint64bit-tables».add_spec
    self t4 hself h4b hon h4on as ⟨p2, hp2on, hp2, hp2b⟩
  step with Array.index_usize_getElem!_spec as ⟨t6, ht6⟩
  obtain ⟨h6on, h6, h6b⟩ := ht6 ▸ ha 6
  step with «CoreOpsArithAddEdwardsPoint64bit-tablesEdwardsPoint64bit-tables».add_spec
    self t6 hself h6b hon h6on as ⟨p3, hp3on, hp3, hp3b⟩
  refine ⟨by simp, fun i => ?_⟩
  fin_cases i
  · simpa [hp1, h2] using ⟨hp1on, hp1b⟩
  · simpa [hp2, h4] using ⟨hp2on, hp2b⟩
  · simpa [hp3, h6] using ⟨hp3on, hp3b⟩

end «RistrettoPoint64bit-tables»

namespace «RistrettoPoint32bit-tables»

open edwards.EdwardsPoint.«32bit-tables».Insts in
/-- `RistrettoPoint::coset4`: `[P, P + T₂, P + T₄, P + T₆]` for the 8-torsion points `Tᵢ`
(`i • torsion8`); limbs `< 2^26`. -/
theorem coset4_spec (self : RistrettoPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    coset4 self ⦃ (r : Array edwards.EdwardsPoint.«32bit-tables» 4#usize) =>
      r[0]! = self ∧ ∀ i : Fin 3, r[i.val + 1]!.OnCurve ∧
        r[i.val + 1]!.toPoint = self.toPoint + (2 * (i.val + 1)) • torsion8 ∧
        r[i.val + 1]!.LimbsLt 26 ⦄ := by
  unfold coset4
  step with backend.serial.u32.constants.«32bit-tables».EIGHT_TORSION_spec as ⟨a, ha⟩
  step with Array.index_usize_getElem!_spec as ⟨t2, ht2⟩
  obtain ⟨h2on, h2, h2b⟩ := ht2 ▸ ha 2
  step with «CoreOpsArithAddEdwardsPoint32bit-tablesEdwardsPoint32bit-tables».add_spec
    self t2 hself h2b hon h2on as ⟨p1, hp1on, hp1, hp1b⟩
  step with Array.index_usize_getElem!_spec as ⟨t4, ht4⟩
  obtain ⟨h4on, h4, h4b⟩ := ht4 ▸ ha 4
  step with «CoreOpsArithAddEdwardsPoint32bit-tablesEdwardsPoint32bit-tables».add_spec
    self t4 hself h4b hon h4on as ⟨p2, hp2on, hp2, hp2b⟩
  step with Array.index_usize_getElem!_spec as ⟨t6, ht6⟩
  obtain ⟨h6on, h6, h6b⟩ := ht6 ▸ ha 6
  step with «CoreOpsArithAddEdwardsPoint32bit-tablesEdwardsPoint32bit-tables».add_spec
    self t6 hself h6b hon h6on as ⟨p3, hp3on, hp3, hp3b⟩
  refine ⟨by simp, fun i => ?_⟩
  fin_cases i
  · simpa [hp1, h2] using ⟨hp1on, hp1b⟩
  · simpa [hp2, h4] using ⟨hp2on, hp2b⟩
  · simpa [hp3, h6] using ⟨hp3on, hp3b⟩

end «RistrettoPoint32bit-tables»

namespace «RistrettoPoint64bit-notables»

open edwards.EdwardsPoint.«64bit-notables».Insts in
/-- `RistrettoPoint::coset4`: `[P, P + T₂, P + T₄, P + T₆]` for the 8-torsion points `Tᵢ`
(`i • torsion8`); limbs `< 2^52`. -/
theorem coset4_spec (self : RistrettoPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    coset4 self ⦃ (r : Array edwards.EdwardsPoint.«64bit-notables» 4#usize) =>
      r[0]! = self ∧ ∀ i : Fin 3, r[i.val + 1]!.OnCurve ∧
        r[i.val + 1]!.toPoint = self.toPoint + (2 * (i.val + 1)) • torsion8 ∧
        r[i.val + 1]!.LimbsLt 52 ⦄ := by
  unfold coset4
  step with backend.serial.u64.constants.«64bit-notables».EIGHT_TORSION_spec as ⟨a, ha⟩
  step with Array.index_usize_getElem!_spec as ⟨t2, ht2⟩
  obtain ⟨h2on, h2, h2b⟩ := ht2 ▸ ha 2
  step with «CoreOpsArithAddEdwardsPoint64bit-notablesEdwardsPoint64bit-notables».add_spec
    self t2 hself h2b hon h2on as ⟨p1, hp1on, hp1, hp1b⟩
  step with Array.index_usize_getElem!_spec as ⟨t4, ht4⟩
  obtain ⟨h4on, h4, h4b⟩ := ht4 ▸ ha 4
  step with «CoreOpsArithAddEdwardsPoint64bit-notablesEdwardsPoint64bit-notables».add_spec
    self t4 hself h4b hon h4on as ⟨p2, hp2on, hp2, hp2b⟩
  step with Array.index_usize_getElem!_spec as ⟨t6, ht6⟩
  obtain ⟨h6on, h6, h6b⟩ := ht6 ▸ ha 6
  step with «CoreOpsArithAddEdwardsPoint64bit-notablesEdwardsPoint64bit-notables».add_spec
    self t6 hself h6b hon h6on as ⟨p3, hp3on, hp3, hp3b⟩
  refine ⟨by simp, fun i => ?_⟩
  fin_cases i
  · simpa [hp1, h2] using ⟨hp1on, hp1b⟩
  · simpa [hp2, h4] using ⟨hp2on, hp2b⟩
  · simpa [hp3, h6] using ⟨hp3on, hp3b⟩

end «RistrettoPoint64bit-notables»

namespace «RistrettoPoint32bit-notables»

open edwards.EdwardsPoint.«32bit-notables».Insts in
/-- `RistrettoPoint::coset4`: `[P, P + T₂, P + T₄, P + T₆]` for the 8-torsion points `Tᵢ`
(`i • torsion8`); limbs `< 2^26`. -/
theorem coset4_spec (self : RistrettoPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    coset4 self ⦃ (r : Array edwards.EdwardsPoint.«32bit-notables» 4#usize) =>
      r[0]! = self ∧ ∀ i : Fin 3, r[i.val + 1]!.OnCurve ∧
        r[i.val + 1]!.toPoint = self.toPoint + (2 * (i.val + 1)) • torsion8 ∧
        r[i.val + 1]!.LimbsLt 26 ⦄ := by
  unfold coset4
  step with backend.serial.u32.constants.«32bit-notables».EIGHT_TORSION_spec as ⟨a, ha⟩
  step with Array.index_usize_getElem!_spec as ⟨t2, ht2⟩
  obtain ⟨h2on, h2, h2b⟩ := ht2 ▸ ha 2
  step with «CoreOpsArithAddEdwardsPoint32bit-notablesEdwardsPoint32bit-notables».add_spec
    self t2 hself h2b hon h2on as ⟨p1, hp1on, hp1, hp1b⟩
  step with Array.index_usize_getElem!_spec as ⟨t4, ht4⟩
  obtain ⟨h4on, h4, h4b⟩ := ht4 ▸ ha 4
  step with «CoreOpsArithAddEdwardsPoint32bit-notablesEdwardsPoint32bit-notables».add_spec
    self t4 hself h4b hon h4on as ⟨p2, hp2on, hp2, hp2b⟩
  step with Array.index_usize_getElem!_spec as ⟨t6, ht6⟩
  obtain ⟨h6on, h6, h6b⟩ := ht6 ▸ ha 6
  step with «CoreOpsArithAddEdwardsPoint32bit-notablesEdwardsPoint32bit-notables».add_spec
    self t6 hself h6b hon h6on as ⟨p3, hp3on, hp3, hp3b⟩
  refine ⟨by simp, fun i => ?_⟩
  fin_cases i
  · simpa [hp1, h2] using ⟨hp1on, hp1b⟩
  · simpa [hp2, h4] using ⟨hp2on, hp2b⟩
  · simpa [hp3, h6] using ⟨hp3on, hp3b⟩

end «RistrettoPoint32bit-notables»

end Curve25519Dalek.ristretto
