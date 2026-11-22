/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Backend.Serial.CurveModels.AddAffineNiels
import Proofs.Backend.Serial.CurveModels.AddProjectiveNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Edwards.AsAffineNiels
import Proofs.Edwards.AsProjectiveNiels
import Proofs.Helpers.Array
import Proofs.Helpers.Window
public section

/-! # `From<&EdwardsPoint> for LookupTable<T>`

One impl per entry type and configuration; each fills the table by the generic loop
`window.fromLoop_spec` (`Proofs/Helpers/Window.lean`):
entry `j` represents `(j + 1) • P`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.window

section
open «Shared0EdwardsPoint64bit-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint64bit-tablesCompletedPoint64bit-tables»
  (add add_spec)
open «CompletedPoint64bit-tables» (as_extended as_extended_spec)
open edwards.«EdwardsPoint64bit-tables»
  (as_projective_niels as_projective_niels_spec)

namespace «LookupTableProjectiveNielsPoint64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPoint64bit-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (P : edwards.EdwardsPoint.«64bit-tables»)
    (x : ProjectiveNielsPoint.«64bit-tables») (hP : P.LimbsLt 52) (hon : P.OnCurve)
    (hx : x.LimbsLt 54) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 7#usize } P (Array.repeat 8#usize x)
      ⦃ (r : Array ProjectiveNielsPoint.«64bit-tables» 8#usize) => ∀ k : ℕ, k < 8 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • P.toPoint ∧ r[k]!.LimbsLt 54 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 8#usize) (add P) as_extended as_projective_niels P.toPoint
    (fun q hq hqon => add_spec P q hP hq hon hqon)
    (fun c hc hcon => as_extended_spec c hc hcon)
    (fun e he heon => as_projective_niels_spec e he heon)
    { start := 0#usize, «end» := 7#usize } rfl rfl (Array.repeat 8#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for LookupTable<ProjectiveNielsPoint>`: entry `j` represents
`(j + 1) • P`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem from_spec (P : edwards.EdwardsPoint.«64bit-tables») (hP : P.LimbsLt 52) (hon : P.OnCurve) :
    «from» P ⦃ (r : LookupTable ProjectiveNielsPoint.«64bit-tables») =>
      r.Represents P.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step with as_projective_niels_spec as ⟨x, hxon, hxp, hxb⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, add_comm, add_smul, one_smul]

end «CoreConvertFromSharedAEdwardsPoint64bit-tables»
end «LookupTableProjectiveNielsPoint64bit-tables».Insts

end

section
open «Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint32bit-tablesCompletedPoint32bit-tables»
  (add add_spec)
open «CompletedPoint32bit-tables» (as_extended as_extended_spec)
open edwards.«EdwardsPoint32bit-tables»
  (as_projective_niels as_projective_niels_spec)

namespace «LookupTableProjectiveNielsPoint32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPoint32bit-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (P : edwards.EdwardsPoint.«32bit-tables»)
    (x : ProjectiveNielsPoint.«32bit-tables») (hP : P.LimbsLt 26) (hon : P.OnCurve)
    (hx : x.LimbsLt 27) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 7#usize } P (Array.repeat 8#usize x)
      ⦃ (r : Array ProjectiveNielsPoint.«32bit-tables» 8#usize) => ∀ k : ℕ, k < 8 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • P.toPoint ∧ r[k]!.LimbsLt 27 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 8#usize) (add P) as_extended as_projective_niels P.toPoint
    (fun q hq hqon => add_spec P q hP hq hon hqon)
    (fun c hc hcon => as_extended_spec c hc hcon)
    (fun e he heon => as_projective_niels_spec e he heon)
    { start := 0#usize, «end» := 7#usize } rfl rfl (Array.repeat 8#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for LookupTable<ProjectiveNielsPoint>`: entry `j` represents
`(j + 1) • P`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem from_spec (P : edwards.EdwardsPoint.«32bit-tables») (hP : P.LimbsLt 26) (hon : P.OnCurve) :
    «from» P ⦃ (r : LookupTable ProjectiveNielsPoint.«32bit-tables») =>
      r.Represents P.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step with as_projective_niels_spec as ⟨x, hxon, hxp, hxb⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, add_comm, add_smul, one_smul]

end «CoreConvertFromSharedAEdwardsPoint32bit-tables»
end «LookupTableProjectiveNielsPoint32bit-tables».Insts

end

section
open «Shared0EdwardsPoint64bit-notables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint64bit-notablesCompletedPoint64bit-notables»
  (add add_spec)
open «CompletedPoint64bit-notables» (as_extended as_extended_spec)
open edwards.«EdwardsPoint64bit-notables»
  (as_projective_niels as_projective_niels_spec)

namespace «LookupTableProjectiveNielsPoint64bit-notables».Insts
namespace «CoreConvertFromSharedAEdwardsPoint64bit-notables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (P : edwards.EdwardsPoint.«64bit-notables»)
    (x : ProjectiveNielsPoint.«64bit-notables») (hP : P.LimbsLt 52) (hon : P.OnCurve)
    (hx : x.LimbsLt 54) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 7#usize } P (Array.repeat 8#usize x)
      ⦃ (r : Array ProjectiveNielsPoint.«64bit-notables» 8#usize) => ∀ k : ℕ, k < 8 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • P.toPoint ∧ r[k]!.LimbsLt 54 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 8#usize) (add P) as_extended as_projective_niels P.toPoint
    (fun q hq hqon => add_spec P q hP hq hon hqon)
    (fun c hc hcon => as_extended_spec c hc hcon)
    (fun e he heon => as_projective_niels_spec e he heon)
    { start := 0#usize, «end» := 7#usize } rfl rfl (Array.repeat 8#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for LookupTable<ProjectiveNielsPoint>`: entry `j` represents
`(j + 1) • P`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem from_spec (P : edwards.EdwardsPoint.«64bit-notables») (hP : P.LimbsLt 52)
    (hon : P.OnCurve) :
    «from» P ⦃ (r : LookupTable ProjectiveNielsPoint.«64bit-notables») =>
      r.Represents P.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step with as_projective_niels_spec as ⟨x, hxon, hxp, hxb⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, add_comm, add_smul, one_smul]

end «CoreConvertFromSharedAEdwardsPoint64bit-notables»
end «LookupTableProjectiveNielsPoint64bit-notables».Insts

end

section
open «Shared0EdwardsPoint32bit-notables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint32bit-notablesCompletedPoint32bit-notables»
  (add add_spec)
open «CompletedPoint32bit-notables» (as_extended as_extended_spec)
open edwards.«EdwardsPoint32bit-notables»
  (as_projective_niels as_projective_niels_spec)

namespace «LookupTableProjectiveNielsPoint32bit-notables».Insts
namespace «CoreConvertFromSharedAEdwardsPoint32bit-notables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (P : edwards.EdwardsPoint.«32bit-notables»)
    (x : ProjectiveNielsPoint.«32bit-notables») (hP : P.LimbsLt 26) (hon : P.OnCurve)
    (hx : x.LimbsLt 27) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 7#usize } P (Array.repeat 8#usize x)
      ⦃ (r : Array ProjectiveNielsPoint.«32bit-notables» 8#usize) => ∀ k : ℕ, k < 8 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • P.toPoint ∧ r[k]!.LimbsLt 27 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 8#usize) (add P) as_extended as_projective_niels P.toPoint
    (fun q hq hqon => add_spec P q hP hq hon hqon)
    (fun c hc hcon => as_extended_spec c hc hcon)
    (fun e he heon => as_projective_niels_spec e he heon)
    { start := 0#usize, «end» := 7#usize } rfl rfl (Array.repeat 8#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for LookupTable<ProjectiveNielsPoint>`: entry `j` represents
`(j + 1) • P`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem from_spec (P : edwards.EdwardsPoint.«32bit-notables») (hP : P.LimbsLt 26)
    (hon : P.OnCurve) :
    «from» P ⦃ (r : LookupTable ProjectiveNielsPoint.«32bit-notables») =>
      r.Represents P.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step with as_projective_niels_spec as ⟨x, hxon, hxp, hxb⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, add_comm, add_smul, one_smul]

end «CoreConvertFromSharedAEdwardsPoint32bit-notables»
end «LookupTableProjectiveNielsPoint32bit-notables».Insts

end

section
open «Shared0EdwardsPoint64bit-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPoint64bit-tablesCompletedPoint64bit-tables»
  (add add_spec)
open «CompletedPoint64bit-tables» (as_extended as_extended_spec)
open edwards.«EdwardsPoint64bit-tables»
  (as_affine_niels as_affine_niels_spec)

namespace «LookupTableAffineNielsPoint64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPoint64bit-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (P : edwards.EdwardsPoint.«64bit-tables»)
    (x : AffineNielsPoint.«64bit-tables») (hP : P.LimbsLt 52) (hon : P.OnCurve)
    (hx : x.LimbsLt 54) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 7#usize } P (Array.repeat 8#usize x)
      ⦃ (r : Array AffineNielsPoint.«64bit-tables» 8#usize) => ∀ k : ℕ, k < 8 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • P.toPoint ∧ r[k]!.LimbsLt 54 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 8#usize) (add P) as_extended as_affine_niels P.toPoint
    (fun q hq hqon => add_spec P q hP hq hon hqon)
    (fun c hc hcon => as_extended_spec c hc hcon)
    (fun e he heon => as_affine_niels_spec e he heon)
    { start := 0#usize, «end» := 7#usize } rfl rfl (Array.repeat 8#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for LookupTable<AffineNielsPoint>`: entry `j` represents
`(j + 1) • P`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem from_spec (P : edwards.EdwardsPoint.«64bit-tables») (hP : P.LimbsLt 52) (hon : P.OnCurve) :
    «from» P ⦃ (r : LookupTable AffineNielsPoint.«64bit-tables») =>
      r.Represents P.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step with as_affine_niels_spec as ⟨x, hxon, hxp, hxb⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, add_comm, add_smul, one_smul]

end «CoreConvertFromSharedAEdwardsPoint64bit-tables»
end «LookupTableAffineNielsPoint64bit-tables».Insts

end

section
open «Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPoint32bit-tablesCompletedPoint32bit-tables»
  (add add_spec)
open «CompletedPoint32bit-tables» (as_extended as_extended_spec)
open edwards.«EdwardsPoint32bit-tables»
  (as_affine_niels as_affine_niels_spec)

namespace «LookupTableAffineNielsPoint32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPoint32bit-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (P : edwards.EdwardsPoint.«32bit-tables»)
    (x : AffineNielsPoint.«32bit-tables») (hP : P.LimbsLt 26) (hon : P.OnCurve)
    (hx : x.LimbsLt 27) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 7#usize } P (Array.repeat 8#usize x)
      ⦃ (r : Array AffineNielsPoint.«32bit-tables» 8#usize) => ∀ k : ℕ, k < 8 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • P.toPoint ∧ r[k]!.LimbsLt 27 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 8#usize) (add P) as_extended as_affine_niels P.toPoint
    (fun q hq hqon => add_spec P q hP hq hon hqon)
    (fun c hc hcon => as_extended_spec c hc hcon)
    (fun e he heon => as_affine_niels_spec e he heon)
    { start := 0#usize, «end» := 7#usize } rfl rfl (Array.repeat 8#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for LookupTable<AffineNielsPoint>`: entry `j` represents
`(j + 1) • P`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem from_spec (P : edwards.EdwardsPoint.«32bit-tables») (hP : P.LimbsLt 26) (hon : P.OnCurve) :
    «from» P ⦃ (r : LookupTable AffineNielsPoint.«32bit-tables») =>
      r.Represents P.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step with as_affine_niels_spec as ⟨x, hxon, hxp, hxb⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, add_comm, add_smul, one_smul]

end «CoreConvertFromSharedAEdwardsPoint32bit-tables»
end «LookupTableAffineNielsPoint32bit-tables».Insts

end

section
open «Shared0EdwardsPoint64bit-notables».Insts
open «CoreOpsArithAddSharedAAffineNielsPoint64bit-notablesCompletedPoint64bit-notables»
  (add add_spec)
open «CompletedPoint64bit-notables» (as_extended as_extended_spec)
open edwards.«EdwardsPoint64bit-notables»
  (as_affine_niels as_affine_niels_spec)

namespace «LookupTableAffineNielsPoint64bit-notables».Insts
namespace «CoreConvertFromSharedAEdwardsPoint64bit-notables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (P : edwards.EdwardsPoint.«64bit-notables»)
    (x : AffineNielsPoint.«64bit-notables») (hP : P.LimbsLt 52) (hon : P.OnCurve)
    (hx : x.LimbsLt 54) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 7#usize } P (Array.repeat 8#usize x)
      ⦃ (r : Array AffineNielsPoint.«64bit-notables» 8#usize) => ∀ k : ℕ, k < 8 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • P.toPoint ∧ r[k]!.LimbsLt 54 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 8#usize) (add P) as_extended as_affine_niels P.toPoint
    (fun q hq hqon => add_spec P q hP hq hon hqon)
    (fun c hc hcon => as_extended_spec c hc hcon)
    (fun e he heon => as_affine_niels_spec e he heon)
    { start := 0#usize, «end» := 7#usize } rfl rfl (Array.repeat 8#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for LookupTable<AffineNielsPoint>`: entry `j` represents
`(j + 1) • P`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem from_spec (P : edwards.EdwardsPoint.«64bit-notables») (hP : P.LimbsLt 52)
    (hon : P.OnCurve) :
    «from» P ⦃ (r : LookupTable AffineNielsPoint.«64bit-notables») =>
      r.Represents P.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step with as_affine_niels_spec as ⟨x, hxon, hxp, hxb⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, add_comm, add_smul, one_smul]

end «CoreConvertFromSharedAEdwardsPoint64bit-notables»
end «LookupTableAffineNielsPoint64bit-notables».Insts

end

section
open «Shared0EdwardsPoint32bit-notables».Insts
open «CoreOpsArithAddSharedAAffineNielsPoint32bit-notablesCompletedPoint32bit-notables»
  (add add_spec)
open «CompletedPoint32bit-notables» (as_extended as_extended_spec)
open edwards.«EdwardsPoint32bit-notables»
  (as_affine_niels as_affine_niels_spec)

namespace «LookupTableAffineNielsPoint32bit-notables».Insts
namespace «CoreConvertFromSharedAEdwardsPoint32bit-notables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (P : edwards.EdwardsPoint.«32bit-notables»)
    (x : AffineNielsPoint.«32bit-notables») (hP : P.LimbsLt 26) (hon : P.OnCurve)
    (hx : x.LimbsLt 27) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 7#usize } P (Array.repeat 8#usize x)
      ⦃ (r : Array AffineNielsPoint.«32bit-notables» 8#usize) => ∀ k : ℕ, k < 8 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • P.toPoint ∧ r[k]!.LimbsLt 27 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 8#usize) (add P) as_extended as_affine_niels P.toPoint
    (fun q hq hqon => add_spec P q hP hq hon hqon)
    (fun c hc hcon => as_extended_spec c hc hcon)
    (fun e he heon => as_affine_niels_spec e he heon)
    { start := 0#usize, «end» := 7#usize } rfl rfl (Array.repeat 8#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for LookupTable<AffineNielsPoint>`: entry `j` represents
`(j + 1) • P`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem from_spec (P : edwards.EdwardsPoint.«32bit-notables») (hP : P.LimbsLt 26)
    (hon : P.OnCurve) :
    «from» P ⦃ (r : LookupTable AffineNielsPoint.«32bit-notables») =>
      r.Represents P.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step with as_affine_niels_spec as ⟨x, hxon, hxp, hxb⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, add_comm, add_smul, one_smul]

end «CoreConvertFromSharedAEdwardsPoint32bit-notables»
end «LookupTableAffineNielsPoint32bit-notables».Insts

end

end Curve25519Dalek.window
