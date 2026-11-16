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

namespace EdwardsBasepointTable.«x86_64-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTable`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTable.«x86_64-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTable.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTable.«x86_64-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTableRadix32.«x86_64-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTableRadix32`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTableRadix32.«x86_64-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTableRadix32.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTableRadix32.«x86_64-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTableRadix64.«x86_64-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTableRadix64`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTableRadix64.«x86_64-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTableRadix64.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTableRadix64.«x86_64-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTableRadix128.«x86_64-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTableRadix128`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTableRadix128.«x86_64-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTableRadix128.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTableRadix128.«x86_64-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTableRadix256.«x86_64-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTableRadix256`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTableRadix256.«x86_64-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTableRadix256.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTableRadix256.«x86_64-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTable.«i686-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTable`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTable.«i686-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTable.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTable.«i686-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTableRadix32.«i686-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTableRadix32`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTableRadix32.«i686-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTableRadix32.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTableRadix32.«i686-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTableRadix64.«i686-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTableRadix64`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTableRadix64.«i686-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTableRadix64.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTableRadix64.«i686-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTableRadix128.«i686-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTableRadix128`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTableRadix128.«i686-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTableRadix128.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTableRadix128.«i686-tables».Insts.CoreCloneClone

namespace EdwardsBasepointTableRadix256.«i686-tables».Insts.CoreCloneClone

/-- `Clone for EdwardsBasepointTableRadix256`: the table itself. -/
@[step]
theorem clone_spec (self : EdwardsBasepointTableRadix256.«i686-tables») :
    clone self ⦃ r => r = self ⦄ := by
  unfold clone
  rw [cloneArray_eq_ok]
  · simp
  · intro x _
    simp only [window.LookupTableRadix256.Insts.CoreCloneClone.clone]
    rw [cloneArray_eq_ok]
    · simp
    · intro y _; rfl

end EdwardsBasepointTableRadix256.«i686-tables».Insts.CoreCloneClone

end Curve25519Dalek.edwards
