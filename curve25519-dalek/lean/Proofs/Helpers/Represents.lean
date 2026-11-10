/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.Edwards
public import Defs.ScalarMul
public import Defs.Window
public section

/-! # Row invariants of the internal tables (proof helper, not audited)

`t.Represents P` says that a lookup table `t` holds the multiples of the point `P` that its
algorithm reads: `(j + 1) • P` for a lookup table, `(2 k + 1) • P` for a NAF table; `pre.Represents
ps` says that a serial precomputation holds the NAF tables of the points `ps`. The internal proofs
(`select`, the scalar-multiplication loops) are stated with them. The public specifications use the
invariants `IsTable` and `IsValid` with the points `t.point` and `pre.points` (`Defs`): a basepoint
table's `IsTable` unfolds to "row `i` represents `2^(w i) • t.point`", `isTable_of_rows` recovers it
from the rows, and `represents_iff` relates a serial precomputation to the backend's `IsValid`. -/

open Aeneas Aeneas.Std

namespace Curve25519Dalek

namespace window

variable {T : Type} [Inhabited T] [PointRepr T]

/-- Entry `j` of `t` (`j < 8`) is on the curve and represents `(j + 1) • P`. -/
@[expose] def LookupTable.Represents (t : LookupTable T) (P : curve25519.edwards.Point) : Prop :=
  ∀ j < 8, PointRepr.OnCurve t[j]! ∧ PointRepr.toPoint t[j]! = (j + 1) • P

/-- Entry `j` of `t` (`j < 16`) is on the curve and represents `(j + 1) • P`. -/
@[expose] def LookupTableRadix32.Represents (t : LookupTableRadix32 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ j < 16, PointRepr.OnCurve t[j]! ∧ PointRepr.toPoint t[j]! = (j + 1) • P

/-- Entry `j` of `t` (`j < 32`) is on the curve and represents `(j + 1) • P`. -/
@[expose] def LookupTableRadix64.Represents (t : LookupTableRadix64 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ j < 32, PointRepr.OnCurve t[j]! ∧ PointRepr.toPoint t[j]! = (j + 1) • P

/-- Entry `j` of `t` (`j < 64`) is on the curve and represents `(j + 1) • P`. -/
@[expose] def LookupTableRadix128.Represents (t : LookupTableRadix128 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ j < 64, PointRepr.OnCurve t[j]! ∧ PointRepr.toPoint t[j]! = (j + 1) • P

/-- Entry `j` of `t` (`j < 128`) is on the curve and represents `(j + 1) • P`. -/
@[expose] def LookupTableRadix256.Represents (t : LookupTableRadix256 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ j < 128, PointRepr.OnCurve t[j]! ∧ PointRepr.toPoint t[j]! = (j + 1) • P

/-- Entry `k` of `t` (`k < 8`) is on the curve and represents the odd multiple `(2 k + 1) • P`. -/
@[expose] def NafLookupTable5.Represents (t : NafLookupTable5 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ k < 8, PointRepr.OnCurve t[k]! ∧ PointRepr.toPoint t[k]! = (2 * k + 1) • P

/-- Entry `k` of `t` (`k < 64`) is on the curve and represents the odd multiple
`(2 k + 1) • P`. -/
@[expose] def NafLookupTable8.Represents (t : NafLookupTable8 T)
    (P : curve25519.edwards.Point) : Prop :=
  ∀ k < 64, PointRepr.OnCurve t[k]! ∧ PointRepr.toPoint t[k]! = (2 * k + 1) • P

end window

namespace edwards

namespace EdwardsBasepointTable.«x86_64-tables»

/-- A radix-`16` table whose row `i` is the lookup table of `2^(8 i) • P` is a table
(`IsTable`) of the point `P`. -/
theorem isTable_of_rows {self : EdwardsBasepointTable.«x86_64-tables»}
    {P : curve25519.edwards.Point}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (8 * i) • P)) :
    self.IsTable ∧ self.point = P := by
  have hpoint : self.point = P := by
    simpa [point] using (h 0 (by decide) 0 (by decide)).2
  refine ⟨fun i hi j hj => ?_, hpoint⟩
  rw [hpoint]
  exact h i hi j hj

/-- `isTable_of_rows` with a further conjunct, in the shape of the table specs. -/
theorem isTable_and_of_rows {self : EdwardsBasepointTable.«x86_64-tables»}
    {P : curve25519.edwards.Point} {Q : Prop}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (8 * i) • P)) (hq : Q) :
    self.IsTable ∧ self.point = P ∧ Q :=
  ⟨(isTable_of_rows h).1, (isTable_of_rows h).2, hq⟩

end EdwardsBasepointTable.«x86_64-tables»

namespace EdwardsBasepointTable.«i686-tables»

/-- A radix-`16` table whose row `i` is the lookup table of `2^(8 i) • P` is a table
(`IsTable`) of the point `P`. -/
theorem isTable_of_rows {self : EdwardsBasepointTable.«i686-tables»}
    {P : curve25519.edwards.Point}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (8 * i) • P)) :
    self.IsTable ∧ self.point = P := by
  have hpoint : self.point = P := by
    simpa [point] using (h 0 (by decide) 0 (by decide)).2
  refine ⟨fun i hi j hj => ?_, hpoint⟩
  rw [hpoint]
  exact h i hi j hj

/-- `isTable_of_rows` with a further conjunct, in the shape of the table specs. -/
theorem isTable_and_of_rows {self : EdwardsBasepointTable.«i686-tables»}
    {P : curve25519.edwards.Point} {Q : Prop}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (8 * i) • P)) (hq : Q) :
    self.IsTable ∧ self.point = P ∧ Q :=
  ⟨(isTable_of_rows h).1, (isTable_of_rows h).2, hq⟩

end EdwardsBasepointTable.«i686-tables»

namespace EdwardsBasepointTableRadix32.«x86_64-tables»

/-- A radix-`32` table whose row `i` is the lookup table of `2^(10 i) • P` is a table
(`IsTable`) of the point `P`. -/
theorem isTable_of_rows {self : EdwardsBasepointTableRadix32.«x86_64-tables»}
    {P : curve25519.edwards.Point}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (10 * i) • P)) :
    self.IsTable ∧ self.point = P := by
  have hpoint : self.point = P := by
    simpa [point] using (h 0 (by decide) 0 (by decide)).2
  refine ⟨fun i hi j hj => ?_, hpoint⟩
  rw [hpoint]
  exact h i hi j hj

/-- `isTable_of_rows` with a further conjunct, in the shape of the table specs. -/
theorem isTable_and_of_rows {self : EdwardsBasepointTableRadix32.«x86_64-tables»}
    {P : curve25519.edwards.Point} {Q : Prop}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (10 * i) • P)) (hq : Q) :
    self.IsTable ∧ self.point = P ∧ Q :=
  ⟨(isTable_of_rows h).1, (isTable_of_rows h).2, hq⟩

end EdwardsBasepointTableRadix32.«x86_64-tables»

namespace EdwardsBasepointTableRadix32.«i686-tables»

/-- A radix-`32` table whose row `i` is the lookup table of `2^(10 i) • P` is a table
(`IsTable`) of the point `P`. -/
theorem isTable_of_rows {self : EdwardsBasepointTableRadix32.«i686-tables»}
    {P : curve25519.edwards.Point}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (10 * i) • P)) :
    self.IsTable ∧ self.point = P := by
  have hpoint : self.point = P := by
    simpa [point] using (h 0 (by decide) 0 (by decide)).2
  refine ⟨fun i hi j hj => ?_, hpoint⟩
  rw [hpoint]
  exact h i hi j hj

/-- `isTable_of_rows` with a further conjunct, in the shape of the table specs. -/
theorem isTable_and_of_rows {self : EdwardsBasepointTableRadix32.«i686-tables»}
    {P : curve25519.edwards.Point} {Q : Prop}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (10 * i) • P)) (hq : Q) :
    self.IsTable ∧ self.point = P ∧ Q :=
  ⟨(isTable_of_rows h).1, (isTable_of_rows h).2, hq⟩

end EdwardsBasepointTableRadix32.«i686-tables»

namespace EdwardsBasepointTableRadix64.«x86_64-tables»

/-- A radix-`64` table whose row `i` is the lookup table of `2^(12 i) • P` is a table
(`IsTable`) of the point `P`. -/
theorem isTable_of_rows {self : EdwardsBasepointTableRadix64.«x86_64-tables»}
    {P : curve25519.edwards.Point}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (12 * i) • P)) :
    self.IsTable ∧ self.point = P := by
  have hpoint : self.point = P := by
    simpa [point] using (h 0 (by decide) 0 (by decide)).2
  refine ⟨fun i hi j hj => ?_, hpoint⟩
  rw [hpoint]
  exact h i hi j hj

/-- `isTable_of_rows` with a further conjunct, in the shape of the table specs. -/
theorem isTable_and_of_rows {self : EdwardsBasepointTableRadix64.«x86_64-tables»}
    {P : curve25519.edwards.Point} {Q : Prop}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (12 * i) • P)) (hq : Q) :
    self.IsTable ∧ self.point = P ∧ Q :=
  ⟨(isTable_of_rows h).1, (isTable_of_rows h).2, hq⟩

end EdwardsBasepointTableRadix64.«x86_64-tables»

namespace EdwardsBasepointTableRadix64.«i686-tables»

/-- A radix-`64` table whose row `i` is the lookup table of `2^(12 i) • P` is a table
(`IsTable`) of the point `P`. -/
theorem isTable_of_rows {self : EdwardsBasepointTableRadix64.«i686-tables»}
    {P : curve25519.edwards.Point}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (12 * i) • P)) :
    self.IsTable ∧ self.point = P := by
  have hpoint : self.point = P := by
    simpa [point] using (h 0 (by decide) 0 (by decide)).2
  refine ⟨fun i hi j hj => ?_, hpoint⟩
  rw [hpoint]
  exact h i hi j hj

/-- `isTable_of_rows` with a further conjunct, in the shape of the table specs. -/
theorem isTable_and_of_rows {self : EdwardsBasepointTableRadix64.«i686-tables»}
    {P : curve25519.edwards.Point} {Q : Prop}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (12 * i) • P)) (hq : Q) :
    self.IsTable ∧ self.point = P ∧ Q :=
  ⟨(isTable_of_rows h).1, (isTable_of_rows h).2, hq⟩

end EdwardsBasepointTableRadix64.«i686-tables»

namespace EdwardsBasepointTableRadix128.«x86_64-tables»

/-- A radix-`128` table whose row `i` is the lookup table of `2^(14 i) • P` is a table
(`IsTable`) of the point `P`. -/
theorem isTable_of_rows {self : EdwardsBasepointTableRadix128.«x86_64-tables»}
    {P : curve25519.edwards.Point}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (14 * i) • P)) :
    self.IsTable ∧ self.point = P := by
  have hpoint : self.point = P := by
    simpa [point] using (h 0 (by decide) 0 (by decide)).2
  refine ⟨fun i hi j hj => ?_, hpoint⟩
  rw [hpoint]
  exact h i hi j hj

/-- `isTable_of_rows` with a further conjunct, in the shape of the table specs. -/
theorem isTable_and_of_rows {self : EdwardsBasepointTableRadix128.«x86_64-tables»}
    {P : curve25519.edwards.Point} {Q : Prop}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (14 * i) • P)) (hq : Q) :
    self.IsTable ∧ self.point = P ∧ Q :=
  ⟨(isTable_of_rows h).1, (isTable_of_rows h).2, hq⟩

end EdwardsBasepointTableRadix128.«x86_64-tables»

namespace EdwardsBasepointTableRadix128.«i686-tables»

/-- A radix-`128` table whose row `i` is the lookup table of `2^(14 i) • P` is a table
(`IsTable`) of the point `P`. -/
theorem isTable_of_rows {self : EdwardsBasepointTableRadix128.«i686-tables»}
    {P : curve25519.edwards.Point}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (14 * i) • P)) :
    self.IsTable ∧ self.point = P := by
  have hpoint : self.point = P := by
    simpa [point] using (h 0 (by decide) 0 (by decide)).2
  refine ⟨fun i hi j hj => ?_, hpoint⟩
  rw [hpoint]
  exact h i hi j hj

/-- `isTable_of_rows` with a further conjunct, in the shape of the table specs. -/
theorem isTable_and_of_rows {self : EdwardsBasepointTableRadix128.«i686-tables»}
    {P : curve25519.edwards.Point} {Q : Prop}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (14 * i) • P)) (hq : Q) :
    self.IsTable ∧ self.point = P ∧ Q :=
  ⟨(isTable_of_rows h).1, (isTable_of_rows h).2, hq⟩

end EdwardsBasepointTableRadix128.«i686-tables»

namespace EdwardsBasepointTableRadix256.«x86_64-tables»

/-- A radix-`256` table whose row `i` is the lookup table of `2^(16 i) • P` is a table
(`IsTable`) of the point `P`. -/
theorem isTable_of_rows {self : EdwardsBasepointTableRadix256.«x86_64-tables»}
    {P : curve25519.edwards.Point}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (16 * i) • P)) :
    self.IsTable ∧ self.point = P := by
  have hpoint : self.point = P := by
    simpa [point] using (h 0 (by decide) 0 (by decide)).2
  refine ⟨fun i hi j hj => ?_, hpoint⟩
  rw [hpoint]
  exact h i hi j hj

/-- `isTable_of_rows` with a further conjunct, in the shape of the table specs. -/
theorem isTable_and_of_rows {self : EdwardsBasepointTableRadix256.«x86_64-tables»}
    {P : curve25519.edwards.Point} {Q : Prop}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (16 * i) • P)) (hq : Q) :
    self.IsTable ∧ self.point = P ∧ Q :=
  ⟨(isTable_of_rows h).1, (isTable_of_rows h).2, hq⟩

end EdwardsBasepointTableRadix256.«x86_64-tables»

namespace EdwardsBasepointTableRadix256.«i686-tables»

/-- A radix-`256` table whose row `i` is the lookup table of `2^(16 i) • P` is a table
(`IsTable`) of the point `P`. -/
theorem isTable_of_rows {self : EdwardsBasepointTableRadix256.«i686-tables»}
    {P : curve25519.edwards.Point}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (16 * i) • P)) :
    self.IsTable ∧ self.point = P := by
  have hpoint : self.point = P := by
    simpa [point] using (h 0 (by decide) 0 (by decide)).2
  refine ⟨fun i hi j hj => ?_, hpoint⟩
  rw [hpoint]
  exact h i hi j hj

/-- `isTable_of_rows` with a further conjunct, in the shape of the table specs. -/
theorem isTable_and_of_rows {self : EdwardsBasepointTableRadix256.«i686-tables»}
    {P : curve25519.edwards.Point} {Q : Prop}
    (h : ∀ i < 32, (self[i]!).Represents (2 ^ (16 * i) • P)) (hq : Q) :
    self.IsTable ∧ self.point = P ∧ Q :=
  ⟨(isTable_of_rows h).1, (isTable_of_rows h).2, hq⟩

end EdwardsBasepointTableRadix256.«i686-tables»

end edwards

namespace backend.serial.scalar_mul.precomputed_straus

/-- The tables of `self` are the NAF tables of the points `ps`, in order (same length). -/
@[expose] def VartimePrecomputedStraus.«x86_64-tables».Represents
    (self : VartimePrecomputedStraus.«x86_64-tables») (ps : List curve25519.edwards.Point) :
    Prop :=
  List.Forall₂ window.NafLookupTable8.Represents self.static_lookup_tables.val ps

/-- The tables of `self` are the NAF tables of the points `ps`, in order (same length). -/
@[expose] def VartimePrecomputedStraus.«i686-tables».Represents
    (self : VartimePrecomputedStraus.«i686-tables») (ps : List curve25519.edwards.Point) :
    Prop :=
  List.Forall₂ window.NafLookupTable8.Represents self.static_lookup_tables.val ps

/-- The tables of `self` are the NAF tables of the points `ps`, in order (same length). -/
@[expose] def VartimePrecomputedStraus.«x86_64-no-tables».Represents
    (self : VartimePrecomputedStraus.«x86_64-no-tables») (ps : List curve25519.edwards.Point) :
    Prop :=
  List.Forall₂ window.NafLookupTable8.Represents self.static_lookup_tables.val ps

/-- The tables of `self` are the NAF tables of the points `ps`, in order (same length). -/
@[expose] def VartimePrecomputedStraus.«i686-no-tables».Represents
    (self : VartimePrecomputedStraus.«i686-no-tables») (ps : List curve25519.edwards.Point) :
    Prop :=
  List.Forall₂ window.NafLookupTable8.Represents self.static_lookup_tables.val ps

/-- The serial precomputation `pre` represents `ps` iff the backend precomputation holding it is
valid (`IsValid`) with the static points `ps`. -/
theorem VartimePrecomputedStraus.«x86_64-tables».represents_iff
    (pre : VartimePrecomputedStraus.«x86_64-tables») (ps : List curve25519.edwards.Point) :
    pre.Represents ps ↔ (backend.VartimePrecomputedStraus.«x86_64-tables».Scalar pre).IsValid ∧
      (backend.VartimePrecomputedStraus.«x86_64-tables».Scalar pre).points = ps := by
  simp only [backend.VartimePrecomputedStraus.«x86_64-tables».IsValid,
    backend.VartimePrecomputedStraus.«x86_64-tables».points,
    VartimePrecomputedStraus.«x86_64-tables».Represents]
  constructor
  · intro h
    obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp h
    have h0 : ∀ n (h₁ : n < pre.static_lookup_tables.val.length),
        PointRepr.toPoint (pre.static_lookup_tables.val.get ⟨n, h₁⟩)[0]! =
          ps.get ⟨n, hlen ▸ h₁⟩ := fun n h₁ => by
      simpa using (hget n h₁ (hlen ▸ h₁) 0 (by decide)).2
    refine ⟨fun n hn k hk => ?_, ?_⟩
    · have hn' : n < pre.static_lookup_tables.val.length := hn
      have := hget n hn' (hlen ▸ hn') k hk
      simp only [List.get_eq_getElem] at this h0
      simp only [Aeneas.Std.alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos
          pre.static_lookup_tables.val n hn']
      rw [h0 n hn']
      exact this
    · apply List.ext_get (by simp [hlen])
      intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_map] at h0 ⊢
      exact h0 n (by simpa using h₁)
  · rintro ⟨h, rfl⟩
    refine List.forall₂_iff_get.mpr ⟨by simp, fun n h₁ h₂ k hk => ?_⟩
    have := h n h₁ k hk
    simp only [Aeneas.Std.alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos pre.static_lookup_tables.val
        n h₁]
      at this
    simpa using this

/-- The serial precomputation `pre` represents `ps` iff the backend precomputation holding it is
valid (`IsValid`) with the static points `ps`. -/
theorem VartimePrecomputedStraus.«i686-tables».represents_iff
    (pre : VartimePrecomputedStraus.«i686-tables») (ps : List curve25519.edwards.Point) :
    pre.Represents ps ↔ (backend.VartimePrecomputedStraus.«i686-tables».Scalar pre).IsValid ∧
      (backend.VartimePrecomputedStraus.«i686-tables».Scalar pre).points = ps := by
  simp only [backend.VartimePrecomputedStraus.«i686-tables».IsValid,
    backend.VartimePrecomputedStraus.«i686-tables».points,
    VartimePrecomputedStraus.«i686-tables».Represents]
  constructor
  · intro h
    obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp h
    have h0 : ∀ n (h₁ : n < pre.static_lookup_tables.val.length),
        PointRepr.toPoint (pre.static_lookup_tables.val.get ⟨n, h₁⟩)[0]! =
          ps.get ⟨n, hlen ▸ h₁⟩ := fun n h₁ => by
      simpa using (hget n h₁ (hlen ▸ h₁) 0 (by decide)).2
    refine ⟨fun n hn k hk => ?_, ?_⟩
    · have hn' : n < pre.static_lookup_tables.val.length := hn
      have := hget n hn' (hlen ▸ hn') k hk
      simp only [List.get_eq_getElem] at this h0
      simp only [Aeneas.Std.alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos
          pre.static_lookup_tables.val n hn']
      rw [h0 n hn']
      exact this
    · apply List.ext_get (by simp [hlen])
      intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_map] at h0 ⊢
      exact h0 n (by simpa using h₁)
  · rintro ⟨h, rfl⟩
    refine List.forall₂_iff_get.mpr ⟨by simp, fun n h₁ h₂ k hk => ?_⟩
    have := h n h₁ k hk
    simp only [Aeneas.Std.alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos pre.static_lookup_tables.val
        n h₁]
      at this
    simpa using this

/-- The serial precomputation `pre` represents `ps` iff the backend precomputation holding it is
valid (`IsValid`) with the static points `ps`. -/
theorem VartimePrecomputedStraus.«x86_64-no-tables».represents_iff
    (pre : VartimePrecomputedStraus.«x86_64-no-tables») (ps : List curve25519.edwards.Point) :
    pre.Represents ps ↔ (backend.VartimePrecomputedStraus.«x86_64-no-tables».Scalar pre).IsValid ∧
      (backend.VartimePrecomputedStraus.«x86_64-no-tables».Scalar pre).points = ps := by
  simp only [backend.VartimePrecomputedStraus.«x86_64-no-tables».IsValid,
    backend.VartimePrecomputedStraus.«x86_64-no-tables».points,
    VartimePrecomputedStraus.«x86_64-no-tables».Represents]
  constructor
  · intro h
    obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp h
    have h0 : ∀ n (h₁ : n < pre.static_lookup_tables.val.length),
        PointRepr.toPoint (pre.static_lookup_tables.val.get ⟨n, h₁⟩)[0]! =
          ps.get ⟨n, hlen ▸ h₁⟩ := fun n h₁ => by
      simpa using (hget n h₁ (hlen ▸ h₁) 0 (by decide)).2
    refine ⟨fun n hn k hk => ?_, ?_⟩
    · have hn' : n < pre.static_lookup_tables.val.length := hn
      have := hget n hn' (hlen ▸ hn') k hk
      simp only [List.get_eq_getElem] at this h0
      simp only [Aeneas.Std.alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos
          pre.static_lookup_tables.val n hn']
      rw [h0 n hn']
      exact this
    · apply List.ext_get (by simp [hlen])
      intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_map] at h0 ⊢
      exact h0 n (by simpa using h₁)
  · rintro ⟨h, rfl⟩
    refine List.forall₂_iff_get.mpr ⟨by simp, fun n h₁ h₂ k hk => ?_⟩
    have := h n h₁ k hk
    simp only [Aeneas.Std.alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos pre.static_lookup_tables.val
        n h₁]
      at this
    simpa using this

/-- The serial precomputation `pre` represents `ps` iff the backend precomputation holding it is
valid (`IsValid`) with the static points `ps`. -/
theorem VartimePrecomputedStraus.«i686-no-tables».represents_iff
    (pre : VartimePrecomputedStraus.«i686-no-tables») (ps : List curve25519.edwards.Point) :
    pre.Represents ps ↔ (backend.VartimePrecomputedStraus.«i686-no-tables».Scalar pre).IsValid ∧
      (backend.VartimePrecomputedStraus.«i686-no-tables».Scalar pre).points = ps := by
  simp only [backend.VartimePrecomputedStraus.«i686-no-tables».IsValid,
    backend.VartimePrecomputedStraus.«i686-no-tables».points,
    VartimePrecomputedStraus.«i686-no-tables».Represents]
  constructor
  · intro h
    obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp h
    have h0 : ∀ n (h₁ : n < pre.static_lookup_tables.val.length),
        PointRepr.toPoint (pre.static_lookup_tables.val.get ⟨n, h₁⟩)[0]! =
          ps.get ⟨n, hlen ▸ h₁⟩ := fun n h₁ => by
      simpa using (hget n h₁ (hlen ▸ h₁) 0 (by decide)).2
    refine ⟨fun n hn k hk => ?_, ?_⟩
    · have hn' : n < pre.static_lookup_tables.val.length := hn
      have := hget n hn' (hlen ▸ hn') k hk
      simp only [List.get_eq_getElem] at this h0
      simp only [Aeneas.Std.alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos
          pre.static_lookup_tables.val n hn']
      rw [h0 n hn']
      exact this
    · apply List.ext_get (by simp [hlen])
      intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_map] at h0 ⊢
      exact h0 n (by simpa using h₁)
  · rintro ⟨h, rfl⟩
    refine List.forall₂_iff_get.mpr ⟨by simp, fun n h₁ h₂ k hk => ?_⟩
    have := h n h₁ k hk
    simp only [Aeneas.Std.alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos pre.static_lookup_tables.val
        n h₁]
      at this
    simpa using this

end backend.serial.scalar_mul.precomputed_straus

end Curve25519Dalek
