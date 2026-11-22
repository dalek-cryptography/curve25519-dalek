/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards

/-- Cloning an array whose entries clone to themselves returns the array. -/
theorem cloneArray_eq_ok {T : Type} {N : Usize} (inst : core.clone.Clone T) (a : Array T N)
    (h : ∀ x ∈ a.val, inst.clone x = ok x) : core.array.CloneArray.clone inst a = ok a := by
  have := core.array.CloneArray.clone_spec inst a h
  revert this
  cases core.array.CloneArray.clone inst a <;> simp_all

namespace EdwardsBasepointTable.«64bit-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTable`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTable.«64bit-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTable.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTable.«64bit-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTableRadix32.«64bit-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTableRadix32`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTableRadix32.«64bit-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTableRadix32.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTableRadix32.«64bit-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTableRadix64.«64bit-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTableRadix64`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTableRadix64.«64bit-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTableRadix64.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTableRadix64.«64bit-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTableRadix128.«64bit-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTableRadix128`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTableRadix128.«64bit-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTableRadix128.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTableRadix128.«64bit-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTableRadix256.«64bit-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTableRadix256`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTableRadix256.«64bit-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTableRadix256.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTableRadix256.«64bit-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTable.«32bit-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTable`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTable.«32bit-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTable.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTable.«32bit-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTableRadix32.«32bit-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTableRadix32`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTableRadix32.«32bit-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTableRadix32.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTableRadix32.«32bit-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTableRadix64.«32bit-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTableRadix64`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTableRadix64.«32bit-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTableRadix64.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTableRadix64.«32bit-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTableRadix128.«32bit-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTableRadix128`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTableRadix128.«32bit-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTableRadix128.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTableRadix128.«32bit-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTableRadix256.«32bit-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTableRadix256`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTableRadix256.«32bit-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTableRadix256.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTableRadix256.«32bit-tables».Insts.CoreCloneClone

end Curve25519Dalek.edwards
