/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Aeneas.Std.Array.Array
public section

/-! # Byte arrays as `Vector UInt8` (staged for Aeneas)

The bridge between Aeneas's model of a Rust byte array, `Array U8 n`, and Lean's
`Vector UInt8 n.val`: both elements wrap a `BitVec 8`, so `toVector` and `ofVector` map the
elements one by one and are inverse to each other (`ofVector_toVector`, `toVector_ofVector`).
Specifications can then be stated with functions on `Vector UInt8`, such as the byte-level
functions of the RFCs, independently of Aeneas.

Staged here for upstreaming to Aeneas: it depends only on Aeneas's `Array` and `U8`. -/

namespace Aeneas.Std

/-- The bytes of a byte array, as a `Vector UInt8`. -/
@[expose] def Array.toVector {n : Usize} (a : Array U8 n) : Vector UInt8 n.val :=
  ⟨(a.val.map fun x => UInt8.ofBitVec x.bv).toArray, by simp⟩

/-- The byte array with the given bytes. -/
@[expose] def Array.ofVector {n : Usize} (v : Vector UInt8 n.val) : Array U8 n :=
  Array.from (v.toList.map fun b => (⟨b.toBitVec⟩ : U8)) (by simp)

theorem Array.toList_toVector {n : Usize} (a : Array U8 n) :
    a.toVector.toList = a.val.map fun x => UInt8.ofBitVec x.bv := by
  simp [Array.toVector, Vector.toList]

theorem Array.val_ofVector {n : Usize} (v : Vector UInt8 n.val) :
    (Array.ofVector v).val = v.toList.map fun b => (⟨b.toBitVec⟩ : U8) := by
  simp [Array.ofVector]

/-- The bytes of `ofVector v` are those of `v`. -/
@[simp]
theorem Array.toVector_ofVector {n : Usize} (v : Vector UInt8 n.val) :
    (Array.ofVector v).toVector = v := by
  apply Vector.toList_inj.mp
  rw [Array.toList_toVector, Array.val_ofVector, List.map_map]
  conv_rhs => rw [← List.map_id v.toList]
  rfl

/-- A byte array is determined by its bytes. -/
@[simp]
theorem Array.ofVector_toVector {n : Usize} (a : Array U8 n) :
    Array.ofVector a.toVector = a := by
  rw [Array.eq_iff, Array.val_ofVector, Array.toList_toVector, List.map_map]
  conv_rhs => rw [← List.map_id a.val]
  rfl

theorem Array.toVector_injective {n : Usize} :
    Function.Injective (Array.toVector : Array U8 n → Vector UInt8 n.val) :=
  fun a b h => by rw [← Array.ofVector_toVector a, h, Array.ofVector_toVector]

/-- Byte `i` of `a.toVector` has the value of byte `i` of `a`. -/
theorem Array.toNat_getElem_toVector {n : Usize} (a : Array U8 n) (i : ℕ) (hi : i < n.val) :
    a.toVector[i].toNat = a[i]!.val := by
  have hi' : i < a.val.length := by simpa using hi
  rw [← Vector.getElem_toList (by simpa using hi)]
  simp only [Array.toList_toVector, List.getElem_map, UInt8.toNat_ofBitVec]
  rw [Array.getElem!_Nat_eq, getElem!_pos a.val i hi']
  rfl

end Aeneas.Std
