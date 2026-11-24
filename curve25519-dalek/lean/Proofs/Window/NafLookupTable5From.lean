module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Backend.Serial.CurveModels.AddProjectiveNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Edwards.AsProjectiveNiels
import Proofs.Edwards.Double
import Proofs.Helpers.Array
import Proofs.Helpers.Window
public section

/-! # `From<&EdwardsPoint> for NafLookupTable5<T>`

One impl per entry type and configuration; each fills the table by the generic loop
`window.fromLoop_spec` (`Proofs/Helpers/Window.lean`):
entry `k` represents the odd multiple `(2 k + 1) • A`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.window

section
open «Shared0EdwardsPoint64bit-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint64bit-tablesCompletedPoint64bit-tables»
  (add add_spec)
open «CompletedPoint64bit-tables» (as_extended as_extended_spec)
open edwards.«EdwardsPoint64bit-tables»
  (as_projective_niels as_projective_niels_spec double_spec)

namespace «NafLookupTable5ProjectiveNielsPoint64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPoint64bit-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (A2 : edwards.EdwardsPoint.«64bit-tables»)
    (x : ProjectiveNielsPoint.«64bit-tables») (hA2 : A2.LimbsLt 52) (hA2on : A2.OnCurve)
    (hx : x.LimbsLt 54) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 7#usize } (Array.repeat 8#usize x) A2
      ⦃ (r : Array ProjectiveNielsPoint.«64bit-tables» 8#usize) => ∀ k : ℕ, k < 8 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • A2.toPoint ∧ r[k]!.LimbsLt 54 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 8#usize) (add A2) as_extended as_projective_niels A2.toPoint
    (fun q hq hqon => add_spec A2 q hA2 hq hA2on hqon)
    (fun c hc hcon => as_extended_spec c hc hcon)
    (fun e he heon => as_projective_niels_spec e he heon)
    { start := 0#usize, «end» := 7#usize } rfl rfl (Array.repeat 8#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for NafLookupTable5<ProjectiveNielsPoint>`: entry `k` represents
`(2 k + 1) • A`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem from_spec (A : edwards.EdwardsPoint.«64bit-tables») (hA : A.LimbsLt 52) (hon : A.OnCurve) :
    «from» A ⦃ (r : NafLookupTable5 ProjectiveNielsPoint.«64bit-tables») =>
      r.Represents A.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step with as_projective_niels_spec as ⟨x, hxon, hxp, hxb⟩
  step with double_spec as ⟨A2, hA2on, hA2p, hA2b⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, hA2p, smul_smul, add_comm, add_smul, one_smul, mul_comm]

end «CoreConvertFromSharedAEdwardsPoint64bit-tables»
end «NafLookupTable5ProjectiveNielsPoint64bit-tables».Insts

end

section
open «Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint32bit-tablesCompletedPoint32bit-tables»
  (add add_spec)
open «CompletedPoint32bit-tables» (as_extended as_extended_spec)
open edwards.«EdwardsPoint32bit-tables»
  (as_projective_niels as_projective_niels_spec double_spec)

namespace «NafLookupTable5ProjectiveNielsPoint32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPoint32bit-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (A2 : edwards.EdwardsPoint.«32bit-tables»)
    (x : ProjectiveNielsPoint.«32bit-tables») (hA2 : A2.LimbsLt 26) (hA2on : A2.OnCurve)
    (hx : x.LimbsLt 27) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 7#usize } (Array.repeat 8#usize x) A2
      ⦃ (r : Array ProjectiveNielsPoint.«32bit-tables» 8#usize) => ∀ k : ℕ, k < 8 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • A2.toPoint ∧ r[k]!.LimbsLt 27 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 8#usize) (add A2) as_extended as_projective_niels A2.toPoint
    (fun q hq hqon => add_spec A2 q hA2 hq hA2on hqon)
    (fun c hc hcon => as_extended_spec c hc hcon)
    (fun e he heon => as_projective_niels_spec e he heon)
    { start := 0#usize, «end» := 7#usize } rfl rfl (Array.repeat 8#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for NafLookupTable5<ProjectiveNielsPoint>`: entry `k` represents
`(2 k + 1) • A`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem from_spec (A : edwards.EdwardsPoint.«32bit-tables») (hA : A.LimbsLt 26) (hon : A.OnCurve) :
    «from» A ⦃ (r : NafLookupTable5 ProjectiveNielsPoint.«32bit-tables») =>
      r.Represents A.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step with as_projective_niels_spec as ⟨x, hxon, hxp, hxb⟩
  step with double_spec as ⟨A2, hA2on, hA2p, hA2b⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, hA2p, smul_smul, add_comm, add_smul, one_smul, mul_comm]

end «CoreConvertFromSharedAEdwardsPoint32bit-tables»
end «NafLookupTable5ProjectiveNielsPoint32bit-tables».Insts

end

section
open «Shared0EdwardsPoint64bit-notables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint64bit-notablesCompletedPoint64bit-notables»
  (add add_spec)
open «CompletedPoint64bit-notables» (as_extended as_extended_spec)
open edwards.«EdwardsPoint64bit-notables»
  (as_projective_niels as_projective_niels_spec double_spec)

namespace «NafLookupTable5ProjectiveNielsPoint64bit-notables».Insts
namespace «CoreConvertFromSharedAEdwardsPoint64bit-notables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (A2 : edwards.EdwardsPoint.«64bit-notables»)
    (x : ProjectiveNielsPoint.«64bit-notables») (hA2 : A2.LimbsLt 52) (hA2on : A2.OnCurve)
    (hx : x.LimbsLt 54) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 7#usize } (Array.repeat 8#usize x) A2
      ⦃ (r : Array ProjectiveNielsPoint.«64bit-notables» 8#usize) => ∀ k : ℕ, k < 8 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • A2.toPoint ∧ r[k]!.LimbsLt 54 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 8#usize) (add A2) as_extended as_projective_niels A2.toPoint
    (fun q hq hqon => add_spec A2 q hA2 hq hA2on hqon)
    (fun c hc hcon => as_extended_spec c hc hcon)
    (fun e he heon => as_projective_niels_spec e he heon)
    { start := 0#usize, «end» := 7#usize } rfl rfl (Array.repeat 8#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for NafLookupTable5<ProjectiveNielsPoint>`: entry `k` represents
`(2 k + 1) • A`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem from_spec (A : edwards.EdwardsPoint.«64bit-notables») (hA : A.LimbsLt 52)
    (hon : A.OnCurve) :
    «from» A ⦃ (r : NafLookupTable5 ProjectiveNielsPoint.«64bit-notables») =>
      r.Represents A.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step with as_projective_niels_spec as ⟨x, hxon, hxp, hxb⟩
  step with double_spec as ⟨A2, hA2on, hA2p, hA2b⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, hA2p, smul_smul, add_comm, add_smul, one_smul, mul_comm]

end «CoreConvertFromSharedAEdwardsPoint64bit-notables»
end «NafLookupTable5ProjectiveNielsPoint64bit-notables».Insts

end

section
open «Shared0EdwardsPoint32bit-notables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint32bit-notablesCompletedPoint32bit-notables»
  (add add_spec)
open «CompletedPoint32bit-notables» (as_extended as_extended_spec)
open edwards.«EdwardsPoint32bit-notables»
  (as_projective_niels as_projective_niels_spec double_spec)

namespace «NafLookupTable5ProjectiveNielsPoint32bit-notables».Insts
namespace «CoreConvertFromSharedAEdwardsPoint32bit-notables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (A2 : edwards.EdwardsPoint.«32bit-notables»)
    (x : ProjectiveNielsPoint.«32bit-notables») (hA2 : A2.LimbsLt 26) (hA2on : A2.OnCurve)
    (hx : x.LimbsLt 27) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 7#usize } (Array.repeat 8#usize x) A2
      ⦃ (r : Array ProjectiveNielsPoint.«32bit-notables» 8#usize) => ∀ k : ℕ, k < 8 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • A2.toPoint ∧ r[k]!.LimbsLt 27 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 8#usize) (add A2) as_extended as_projective_niels A2.toPoint
    (fun q hq hqon => add_spec A2 q hA2 hq hA2on hqon)
    (fun c hc hcon => as_extended_spec c hc hcon)
    (fun e he heon => as_projective_niels_spec e he heon)
    { start := 0#usize, «end» := 7#usize } rfl rfl (Array.repeat 8#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for NafLookupTable5<ProjectiveNielsPoint>`: entry `k` represents
`(2 k + 1) • A`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem from_spec (A : edwards.EdwardsPoint.«32bit-notables») (hA : A.LimbsLt 26)
    (hon : A.OnCurve) :
    «from» A ⦃ (r : NafLookupTable5 ProjectiveNielsPoint.«32bit-notables») =>
      r.Represents A.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step with as_projective_niels_spec as ⟨x, hxon, hxp, hxb⟩
  step with double_spec as ⟨A2, hA2on, hA2p, hA2b⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, hA2p, smul_smul, add_comm, add_smul, one_smul, mul_comm]

end «CoreConvertFromSharedAEdwardsPoint32bit-notables»
end «NafLookupTable5ProjectiveNielsPoint32bit-notables».Insts

end

end Curve25519Dalek.window
