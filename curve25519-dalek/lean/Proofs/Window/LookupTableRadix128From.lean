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

/-! # `From<&EdwardsPoint> for LookupTableRadix128<T>`

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

namespace «LookupTableRadix128ProjectiveNielsPoint64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPoint64bit-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (P : edwards.EdwardsPoint.«64bit-tables»)
    (x : ProjectiveNielsPoint.«64bit-tables») (hP : P.LimbsLt 52) (hon : P.OnCurve)
    (hx : x.LimbsLt 54) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 63#usize } P (Array.repeat 64#usize x)
      ⦃ (r : Array ProjectiveNielsPoint.«64bit-tables» 64#usize) => ∀ k : ℕ, k < 64 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • P.toPoint ∧ r[k]!.LimbsLt 54 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 64#usize) (add P) as_extended as_projective_niels P.toPoint
    (fun q hq hqon => add_spec P q hP hq hon hqon)
    (fun c hc hcon => as_extended_spec c hc hcon)
    (fun e he heon => as_projective_niels_spec e he heon)
    { start := 0#usize, «end» := 63#usize } rfl rfl (Array.repeat 64#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for LookupTableRadix128<ProjectiveNielsPoint>`: entry `j` represents
`(j + 1) • P`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem from_spec (P : edwards.EdwardsPoint.«64bit-tables») (hP : P.LimbsLt 52) (hon : P.OnCurve) :
    «from» P ⦃ (r : LookupTableRadix128 ProjectiveNielsPoint.«64bit-tables») =>
      r.Represents P.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step with as_projective_niels_spec as ⟨x, hxon, hxp, hxb⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, add_comm, add_smul, one_smul]

end «CoreConvertFromSharedAEdwardsPoint64bit-tables»
end «LookupTableRadix128ProjectiveNielsPoint64bit-tables».Insts

end

section
open «Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint32bit-tablesCompletedPoint32bit-tables»
  (add add_spec)
open «CompletedPoint32bit-tables» (as_extended as_extended_spec)
open edwards.«EdwardsPoint32bit-tables»
  (as_projective_niels as_projective_niels_spec)

namespace «LookupTableRadix128ProjectiveNielsPoint32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPoint32bit-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (P : edwards.EdwardsPoint.«32bit-tables»)
    (x : ProjectiveNielsPoint.«32bit-tables») (hP : P.LimbsLt 26) (hon : P.OnCurve)
    (hx : x.LimbsLt 27) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 63#usize } P (Array.repeat 64#usize x)
      ⦃ (r : Array ProjectiveNielsPoint.«32bit-tables» 64#usize) => ∀ k : ℕ, k < 64 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • P.toPoint ∧ r[k]!.LimbsLt 27 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 64#usize) (add P) as_extended as_projective_niels P.toPoint
    (fun q hq hqon => add_spec P q hP hq hon hqon)
    (fun c hc hcon => as_extended_spec c hc hcon)
    (fun e he heon => as_projective_niels_spec e he heon)
    { start := 0#usize, «end» := 63#usize } rfl rfl (Array.repeat 64#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for LookupTableRadix128<ProjectiveNielsPoint>`: entry `j` represents
`(j + 1) • P`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem from_spec (P : edwards.EdwardsPoint.«32bit-tables») (hP : P.LimbsLt 26) (hon : P.OnCurve) :
    «from» P ⦃ (r : LookupTableRadix128 ProjectiveNielsPoint.«32bit-tables») =>
      r.Represents P.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step with as_projective_niels_spec as ⟨x, hxon, hxp, hxb⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, add_comm, add_smul, one_smul]

end «CoreConvertFromSharedAEdwardsPoint32bit-tables»
end «LookupTableRadix128ProjectiveNielsPoint32bit-tables».Insts

end

section
open «Shared0EdwardsPoint64bit-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPoint64bit-tablesCompletedPoint64bit-tables»
  (add add_spec)
open «CompletedPoint64bit-tables» (as_extended as_extended_spec)
open edwards.«EdwardsPoint64bit-tables»
  (as_affine_niels as_affine_niels_spec)

namespace «LookupTableRadix128AffineNielsPoint64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPoint64bit-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (P : edwards.EdwardsPoint.«64bit-tables»)
    (x : AffineNielsPoint.«64bit-tables») (hP : P.LimbsLt 52) (hon : P.OnCurve)
    (hx : x.LimbsLt 54) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 63#usize } P (Array.repeat 64#usize x)
      ⦃ (r : Array AffineNielsPoint.«64bit-tables» 64#usize) => ∀ k : ℕ, k < 64 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • P.toPoint ∧ r[k]!.LimbsLt 54 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 64#usize) (add P) as_extended as_affine_niels P.toPoint
    (fun q hq hqon => add_spec P q hP hq hon hqon)
    (fun c hc hcon => as_extended_spec c hc hcon)
    (fun e he heon => as_affine_niels_spec e he heon)
    { start := 0#usize, «end» := 63#usize } rfl rfl (Array.repeat 64#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for LookupTableRadix128<AffineNielsPoint>`: entry `j` represents
`(j + 1) • P`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem from_spec (P : edwards.EdwardsPoint.«64bit-tables») (hP : P.LimbsLt 52) (hon : P.OnCurve) :
    «from» P ⦃ (r : LookupTableRadix128 AffineNielsPoint.«64bit-tables») =>
      r.Represents P.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step with as_affine_niels_spec as ⟨x, hxon, hxp, hxb⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, add_comm, add_smul, one_smul]

end «CoreConvertFromSharedAEdwardsPoint64bit-tables»
end «LookupTableRadix128AffineNielsPoint64bit-tables».Insts

end

section
open «Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPoint32bit-tablesCompletedPoint32bit-tables»
  (add add_spec)
open «CompletedPoint32bit-tables» (as_extended as_extended_spec)
open edwards.«EdwardsPoint32bit-tables»
  (as_affine_niels as_affine_niels_spec)

namespace «LookupTableRadix128AffineNielsPoint32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsPoint32bit-tables»

/-- The loop: entry `k` represents `x + k • Q`, `Q` the added point. -/
@[local step]
private theorem from_loop_spec (P : edwards.EdwardsPoint.«32bit-tables»)
    (x : AffineNielsPoint.«32bit-tables») (hP : P.LimbsLt 26) (hon : P.OnCurve)
    (hx : x.LimbsLt 27) (hxon : x.OnCurve) :
    from_loop { start := 0#usize, «end» := 63#usize } P (Array.repeat 64#usize x)
      ⦃ (r : Array AffineNielsPoint.«32bit-tables» 64#usize) => ∀ k : ℕ, k < 64 →
        r[k]!.OnCurve ∧ r[k]!.toPoint = x.toPoint + k • P.toPoint ∧ r[k]!.LimbsLt 27 ⦄ := by
  unfold from_loop
  have h := fromLoop_spec (N := 64#usize) (add P) as_extended as_affine_niels P.toPoint
    (fun q hq hqon => add_spec P q hP hq hon hqon)
    (fun c hc hcon => as_extended_spec c hc hcon)
    (fun e he heon => as_affine_niels_spec e he heon)
    { start := 0#usize, «end» := 63#usize } rfl rfl (Array.repeat 64#usize x)
    (by rw [Array.getElem!_repeat x (by decide)]; exact ⟨hxon, hx⟩)
  rw [Array.getElem!_repeat x (by decide)] at h
  exact h

/-- `From<&EdwardsPoint> for LookupTableRadix128<AffineNielsPoint>`: entry `j` represents
`(j + 1) • P`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem from_spec (P : edwards.EdwardsPoint.«32bit-tables») (hP : P.LimbsLt 26) (hon : P.OnCurve) :
    «from» P ⦃ (r : LookupTableRadix128 AffineNielsPoint.«32bit-tables») =>
      r.Represents P.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step with as_affine_niels_spec as ⟨x, hxon, hxp, hxb⟩
  step as ⟨r, hr⟩
  refine ⟨fun k hk => ?_, fun k hk => (hr k hk).2.2⟩
  obtain ⟨hron, hrp, -⟩ := hr k hk
  refine ⟨hron, (?_ : r[k]!.toPoint = _)⟩
  rw [hrp, hxp, add_comm, add_smul, one_smul]

end «CoreConvertFromSharedAEdwardsPoint32bit-tables»
end «LookupTableRadix128AffineNielsPoint32bit-tables».Insts

end

end Curve25519Dalek.window
