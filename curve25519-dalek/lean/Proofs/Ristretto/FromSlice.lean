/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Ristretto
public section

/-! # `CompressedRistretto::from_slice` and `TryFrom<&[u8]>` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.ristretto.CompressedRistretto

/-- `CompressedRistretto::from_slice`: the bytes of a slice of length `32`, an error otherwise. -/
@[step]
theorem from_slice_spec (bytes : Slice U8) :
    from_slice bytes ⦃ (r : core.result.Result CompressedRistretto core.array.TryFromSliceError) =>
      (bytes.length = 32 → ∃ a : CompressedRistretto, r = .Ok a ∧ a.val = bytes.val) ∧
      (bytes.length ≠ 32 → r = .Err ()) ⦄ := by
  unfold from_slice
  step as ⟨r0, hr0⟩
  step with core.result.Result.map_spec
    P.Insts.CoreOpsFunctionFnOnceTupleArrayU832CompressedRistretto r0
    CompressedRistretto.constructor (fun x _ => ⟨x, rfl⟩) as ⟨r, hok, herr⟩
  rcases r0 with a | e
  · obtain ⟨y, hy, hr⟩ := hok a rfl
    obtain ⟨hval, -⟩ := hr0
    simp only [P.Insts.CoreOpsFunctionFnOnceTupleArrayU832CompressedRistretto.call_once,
      CompressedRistretto.constructor] at hy
    have hay : a = y := Result.ok_injective hy
    refine ⟨fun _ => ⟨a, by rw [hr, hay], hval⟩, fun hne => absurd ?_ hne⟩
    rw [Slice.length, ← hval, Array.length_eq]
    rfl
  · exact ⟨fun h => absurd h hr0, fun _ => herr e rfl⟩

namespace Insts.CoreConvertTryFromShared0SliceU8TryFromSliceError

/-- `TryFrom<&[u8]> for CompressedRistretto`: as `from_slice`. -/
@[step]
theorem try_from_spec (slice : Slice U8) :
    try_from slice ⦃ (r : core.result.Result CompressedRistretto core.array.TryFromSliceError) =>
      (slice.length = 32 → ∃ a : CompressedRistretto, r = .Ok a ∧ a.val = slice.val) ∧
      (slice.length ≠ 32 → r = .Err ()) ⦄ := by
  unfold try_from
  step*

end Insts.CoreConvertTryFromShared0SliceU8TryFromSliceError

end Curve25519Dalek.ristretto.CompressedRistretto
