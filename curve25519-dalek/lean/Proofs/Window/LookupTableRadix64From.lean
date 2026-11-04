/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Backend.Serial.CurveModels.AddAffineNiels
import Proofs.Backend.Serial.CurveModels.AddProjectiveNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Edwards.AsAffineNiels
import Proofs.Edwards.AsProjectiveNiels
import Proofs.Helpers.Array
import Proofs.Helpers.Window
public section

/-! # `From<&EdwardsPoint> for LookupTableRadix64<T>`

One impl per entry type and configuration; each fills the table by the generic loop
`window.fromLoop_spec` (`Proofs/Helpers/Window.lean`):
entry `j` represents `(j + 1) • P`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.window

section
open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointx86_64-tablesCompletedPointx86_64-tables»
  (add add_spec_point)
open «CompletedPointx86_64-tables» (as_extended as_extended_spec_point)
open edwards.«EdwardsPointx86_64-tables»
  (as_projective_niels as_projective_niels_spec_point)

namespace «LookupTableRadix64ProjectiveNielsPointx86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPointx86_64-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (P : edwards.EdwardsPoint.«x86_64-tables»)
    (x : ProjectiveNielsPoint.«x86_64-tables») (hP : P.LimbsLt 52) (hon : P.OnCurve)
    (hx : x.LimbsLt 54) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 31#usize } P (Array.repeat 32#usize x)
      ⦃ (r : Array ProjectiveNielsPoint.«x86_64-tables» 32#usize) => ∀ k : ℕ, k < 32 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • P.toPoint ∧ r[k]!.LimbsLt 54 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 32#usize) (add P) as_extended as_projective_niels P.toPoint
    (fun q hq hqon => add_spec_point P q hP hq hon hqon)
    (fun c hc hcon => as_extended_spec_point c hc hcon)
    (fun e he heon => as_projective_niels_spec_point e he heon)
    { start := 0#usize, «end» := 31#usize } rfl rfl (Array.repeat 32#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for LookupTableRadix64<ProjectiveNielsPoint>`: entry `j` represents
`(j + 1) • P`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem from_spec (P : edwards.EdwardsPoint.«x86_64-tables») (hP : P.LimbsLt 52) (hon : P.OnCurve) :
    «from» P ⦃ (r : LookupTableRadix64 ProjectiveNielsPoint.«x86_64-tables») =>
      r.Represents P.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step with as_projective_niels_spec_point as ⟨x, hxon, hxp, hxb⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, add_comm, add_smul, one_smul]

end «CoreConvertFromSharedAEdwardsPointx86_64-tables»
end «LookupTableRadix64ProjectiveNielsPointx86_64-tables».Insts

end

section
open «Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-tablesCompletedPointi686-tables»
  (add add_spec_point)
open «CompletedPointi686-tables» (as_extended as_extended_spec_point)
open edwards.«EdwardsPointi686-tables»
  (as_projective_niels as_projective_niels_spec_point)

namespace «LookupTableRadix64ProjectiveNielsPointi686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPointi686-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (P : edwards.EdwardsPoint.«i686-tables»)
    (x : ProjectiveNielsPoint.«i686-tables») (hP : P.LimbsLt 26) (hon : P.OnCurve)
    (hx : x.LimbsLt 27) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 31#usize } P (Array.repeat 32#usize x)
      ⦃ (r : Array ProjectiveNielsPoint.«i686-tables» 32#usize) => ∀ k : ℕ, k < 32 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • P.toPoint ∧ r[k]!.LimbsLt 27 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 32#usize) (add P) as_extended as_projective_niels P.toPoint
    (fun q hq hqon => add_spec_point P q hP hq hon hqon)
    (fun c hc hcon => as_extended_spec_point c hc hcon)
    (fun e he heon => as_projective_niels_spec_point e he heon)
    { start := 0#usize, «end» := 31#usize } rfl rfl (Array.repeat 32#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for LookupTableRadix64<ProjectiveNielsPoint>`: entry `j` represents
`(j + 1) • P`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem from_spec (P : edwards.EdwardsPoint.«i686-tables») (hP : P.LimbsLt 26) (hon : P.OnCurve) :
    «from» P ⦃ (r : LookupTableRadix64 ProjectiveNielsPoint.«i686-tables») =>
      r.Represents P.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step with as_projective_niels_spec_point as ⟨x, hxon, hxp, hxb⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, add_comm, add_smul, one_smul]

end «CoreConvertFromSharedAEdwardsPointi686-tables»
end «LookupTableRadix64ProjectiveNielsPointi686-tables».Insts

end

section
open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPointx86_64-tablesCompletedPointx86_64-tables»
  (add add_spec_point)
open «CompletedPointx86_64-tables» (as_extended as_extended_spec_point)
open edwards.«EdwardsPointx86_64-tables»
  (as_affine_niels as_affine_niels_spec_point)

namespace «LookupTableRadix64AffineNielsPointx86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPointx86_64-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (P : edwards.EdwardsPoint.«x86_64-tables»)
    (x : AffineNielsPoint.«x86_64-tables») (hP : P.LimbsLt 52) (hon : P.OnCurve)
    (hx : x.LimbsLt 54) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 31#usize } P (Array.repeat 32#usize x)
      ⦃ (r : Array AffineNielsPoint.«x86_64-tables» 32#usize) => ∀ k : ℕ, k < 32 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • P.toPoint ∧ r[k]!.LimbsLt 54 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 32#usize) (add P) as_extended as_affine_niels P.toPoint
    (fun q hq hqon => add_spec_point P q hP hq hon hqon)
    (fun c hc hcon => as_extended_spec_point c hc hcon)
    (fun e he heon => as_affine_niels_spec_point e he heon)
    { start := 0#usize, «end» := 31#usize } rfl rfl (Array.repeat 32#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for LookupTableRadix64<AffineNielsPoint>`: entry `j` represents
`(j + 1) • P`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem from_spec (P : edwards.EdwardsPoint.«x86_64-tables») (hP : P.LimbsLt 52) (hon : P.OnCurve) :
    «from» P ⦃ (r : LookupTableRadix64 AffineNielsPoint.«x86_64-tables») =>
      r.Represents P.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step with as_affine_niels_spec_point as ⟨x, hxon, hxp, hxb⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, add_comm, add_smul, one_smul]

end «CoreConvertFromSharedAEdwardsPointx86_64-tables»
end «LookupTableRadix64AffineNielsPointx86_64-tables».Insts

end

section
open «Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPointi686-tablesCompletedPointi686-tables»
  (add add_spec_point)
open «CompletedPointi686-tables» (as_extended as_extended_spec_point)
open edwards.«EdwardsPointi686-tables»
  (as_affine_niels as_affine_niels_spec_point)

namespace «LookupTableRadix64AffineNielsPointi686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPointi686-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (P : edwards.EdwardsPoint.«i686-tables»)
    (x : AffineNielsPoint.«i686-tables») (hP : P.LimbsLt 26) (hon : P.OnCurve)
    (hx : x.LimbsLt 27) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 31#usize } P (Array.repeat 32#usize x)
      ⦃ (r : Array AffineNielsPoint.«i686-tables» 32#usize) => ∀ k : ℕ, k < 32 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • P.toPoint ∧ r[k]!.LimbsLt 27 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 32#usize) (add P) as_extended as_affine_niels P.toPoint
    (fun q hq hqon => add_spec_point P q hP hq hon hqon)
    (fun c hc hcon => as_extended_spec_point c hc hcon)
    (fun e he heon => as_affine_niels_spec_point e he heon)
    { start := 0#usize, «end» := 31#usize } rfl rfl (Array.repeat 32#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for LookupTableRadix64<AffineNielsPoint>`: entry `j` represents
`(j + 1) • P`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem from_spec (P : edwards.EdwardsPoint.«i686-tables») (hP : P.LimbsLt 26) (hon : P.OnCurve) :
    «from» P ⦃ (r : LookupTableRadix64 AffineNielsPoint.«i686-tables») =>
      r.Represents P.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step with as_affine_niels_spec_point as ⟨x, hxon, hxp, hxb⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, add_comm, add_smul, one_smul]

end «CoreConvertFromSharedAEdwardsPointi686-tables»
end «LookupTableRadix64AffineNielsPointi686-tables».Insts

end

end Curve25519Dalek.window
