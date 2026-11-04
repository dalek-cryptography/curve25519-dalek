/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
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
open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
  (add add_spec_point)
open «CompletedPointx86_64-tables» (as_extended as_extended_spec_point)
open edwards.«EdwardsPointx86_64-tables»
  (as_projective_niels as_projective_niels_spec_point double_spec_point)

namespace «NafLookupTable5ProjectiveNielsPointx86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPointx86_64-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (A2 : edwards.EdwardsPoint.«x86_64-tables»)
    (x : ProjectiveNielsPoint.«x86_64-tables») (hA2 : A2.LimbsLt 52) (hA2on : A2.OnCurve)
    (hx : x.LimbsLt 54) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 7#usize } (Array.repeat 8#usize x) A2
      ⦃ (r : Array ProjectiveNielsPoint.«x86_64-tables» 8#usize) => ∀ k : ℕ, k < 8 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • A2.toPoint ∧ r[k]!.LimbsLt 54 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 8#usize) (add A2) as_extended as_projective_niels A2.toPoint
    (fun q hq hqon => add_spec_point A2 q hA2 hq hA2on hqon)
    (fun c hc hcon => as_extended_spec_point c hc hcon)
    (fun e he heon => as_projective_niels_spec_point e he heon)
    { start := 0#usize, «end» := 7#usize } rfl rfl (Array.repeat 8#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for NafLookupTable5<ProjectiveNielsPoint>`: entry `k` represents
`(2 k + 1) • A`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem from_spec (A : edwards.EdwardsPoint.«x86_64-tables») (hA : A.LimbsLt 52) (hon : A.OnCurve) :
    «from» A ⦃ (r : NafLookupTable5 ProjectiveNielsPoint.«x86_64-tables») =>
      r.Represents A.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step with as_projective_niels_spec_point as ⟨x, hxon, hxp, hxb⟩
  step with double_spec_point as ⟨A2, hA2on, hA2p, hA2b⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, hA2p, smul_smul, add_comm, add_smul, one_smul, mul_comm]

end «CoreConvertFromSharedAEdwardsPointx86_64-tables»
end «NafLookupTable5ProjectiveNielsPointx86_64-tables».Insts

end

section
open «Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-tablesCompletedPointi686-tables»
  (add add_spec_point)
open «CompletedPointi686-tables» (as_extended as_extended_spec_point)
open edwards.«EdwardsPointi686-tables»
  (as_projective_niels as_projective_niels_spec_point double_spec_point)

namespace «NafLookupTable5ProjectiveNielsPointi686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPointi686-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (A2 : edwards.EdwardsPoint.«i686-tables»)
    (x : ProjectiveNielsPoint.«i686-tables») (hA2 : A2.LimbsLt 26) (hA2on : A2.OnCurve)
    (hx : x.LimbsLt 27) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 7#usize } (Array.repeat 8#usize x) A2
      ⦃ (r : Array ProjectiveNielsPoint.«i686-tables» 8#usize) => ∀ k : ℕ, k < 8 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • A2.toPoint ∧ r[k]!.LimbsLt 27 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 8#usize) (add A2) as_extended as_projective_niels A2.toPoint
    (fun q hq hqon => add_spec_point A2 q hA2 hq hA2on hqon)
    (fun c hc hcon => as_extended_spec_point c hc hcon)
    (fun e he heon => as_projective_niels_spec_point e he heon)
    { start := 0#usize, «end» := 7#usize } rfl rfl (Array.repeat 8#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for NafLookupTable5<ProjectiveNielsPoint>`: entry `k` represents
`(2 k + 1) • A`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem from_spec (A : edwards.EdwardsPoint.«i686-tables») (hA : A.LimbsLt 26) (hon : A.OnCurve) :
    «from» A ⦃ (r : NafLookupTable5 ProjectiveNielsPoint.«i686-tables») =>
      r.Represents A.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step with as_projective_niels_spec_point as ⟨x, hxon, hxp, hxb⟩
  step with double_spec_point as ⟨A2, hA2on, hA2p, hA2b⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, hA2p, smul_smul, add_comm, add_smul, one_smul, mul_comm]

end «CoreConvertFromSharedAEdwardsPointi686-tables»
end «NafLookupTable5ProjectiveNielsPointi686-tables».Insts

end

section
open «Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-no-tablesCompletedPointx86_64-no-tables»
  (add add_spec_point)
open «CompletedPointx86_64-no-tables» (as_extended as_extended_spec_point)
open edwards.«EdwardsPointx86_64-no-tables»
  (as_projective_niels as_projective_niels_spec_point double_spec_point)

namespace «NafLookupTable5ProjectiveNielsPointx86_64-no-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPointx86_64-no-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (A2 : edwards.EdwardsPoint.«x86_64-no-tables»)
    (x : ProjectiveNielsPoint.«x86_64-no-tables») (hA2 : A2.LimbsLt 52) (hA2on : A2.OnCurve)
    (hx : x.LimbsLt 54) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 7#usize } (Array.repeat 8#usize x) A2
      ⦃ (r : Array ProjectiveNielsPoint.«x86_64-no-tables» 8#usize) => ∀ k : ℕ, k < 8 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • A2.toPoint ∧ r[k]!.LimbsLt 54 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 8#usize) (add A2) as_extended as_projective_niels A2.toPoint
    (fun q hq hqon => add_spec_point A2 q hA2 hq hA2on hqon)
    (fun c hc hcon => as_extended_spec_point c hc hcon)
    (fun e he heon => as_projective_niels_spec_point e he heon)
    { start := 0#usize, «end» := 7#usize } rfl rfl (Array.repeat 8#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for NafLookupTable5<ProjectiveNielsPoint>`: entry `k` represents
`(2 k + 1) • A`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem from_spec (A : edwards.EdwardsPoint.«x86_64-no-tables») (hA : A.LimbsLt 52)
    (hon : A.OnCurve) :
    «from» A ⦃ (r : NafLookupTable5 ProjectiveNielsPoint.«x86_64-no-tables») =>
      r.Represents A.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step with as_projective_niels_spec_point as ⟨x, hxon, hxp, hxb⟩
  step with double_spec_point as ⟨A2, hA2on, hA2p, hA2b⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, hA2p, smul_smul, add_comm, add_smul, one_smul, mul_comm]

end «CoreConvertFromSharedAEdwardsPointx86_64-no-tables»
end «NafLookupTable5ProjectiveNielsPointx86_64-no-tables».Insts

end

section
open «Shared0EdwardsPointi686-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»
  (add add_spec_point)
open «CompletedPointi686-no-tables» (as_extended as_extended_spec_point)
open edwards.«EdwardsPointi686-no-tables»
  (as_projective_niels as_projective_niels_spec_point double_spec_point)

namespace «NafLookupTable5ProjectiveNielsPointi686-no-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPointi686-no-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (A2 : edwards.EdwardsPoint.«i686-no-tables»)
    (x : ProjectiveNielsPoint.«i686-no-tables») (hA2 : A2.LimbsLt 26) (hA2on : A2.OnCurve)
    (hx : x.LimbsLt 27) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 7#usize } (Array.repeat 8#usize x) A2
      ⦃ (r : Array ProjectiveNielsPoint.«i686-no-tables» 8#usize) => ∀ k : ℕ, k < 8 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • A2.toPoint ∧ r[k]!.LimbsLt 27 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 8#usize) (add A2) as_extended as_projective_niels A2.toPoint
    (fun q hq hqon => add_spec_point A2 q hA2 hq hA2on hqon)
    (fun c hc hcon => as_extended_spec_point c hc hcon)
    (fun e he heon => as_projective_niels_spec_point e he heon)
    { start := 0#usize, «end» := 7#usize } rfl rfl (Array.repeat 8#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for NafLookupTable5<ProjectiveNielsPoint>`: entry `k` represents
`(2 k + 1) • A`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem from_spec (A : edwards.EdwardsPoint.«i686-no-tables») (hA : A.LimbsLt 26)
    (hon : A.OnCurve) :
    «from» A ⦃ (r : NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables») =>
      r.Represents A.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step with as_projective_niels_spec_point as ⟨x, hxon, hxp, hxb⟩
  step with double_spec_point as ⟨A2, hA2on, hA2p, hA2b⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, hA2p, smul_smul, add_comm, add_smul, one_smul, mul_comm]

end «CoreConvertFromSharedAEdwardsPointi686-no-tables»
end «NafLookupTable5ProjectiveNielsPointi686-no-tables».Insts

end

end Curve25519Dalek.window
