/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.ToAeneas.Iterator
public import Proofs.Representation.Scalar
public import ForHumans.Specs.Representation
public import Proofs.Representation.Window
import Proofs.Backend.Serial.ScalarMul.PrecomputedStraus.Len
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

namespace «VartimePrecomputedStraus64bit-tables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«64bit-tables».Insts in
/-- `VartimePrecomputedStraus::len` (backend): the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«64bit-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄ := by
  rcases self with ⟨inner⟩
  unfold len
  step as ⟨r, h⟩
  simp only [h, VartimePrecomputedStraus.«64bit-tables».points, List.length_map]

end «VartimePrecomputedStraus64bit-tables»

namespace «VartimePrecomputedStraus32bit-tables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«32bit-tables».Insts in
/-- `VartimePrecomputedStraus::len` (backend): the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«32bit-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄ := by
  rcases self with ⟨inner⟩
  unfold len
  step as ⟨r, h⟩
  simp only [h, VartimePrecomputedStraus.«32bit-tables».points, List.length_map]

end «VartimePrecomputedStraus32bit-tables»

namespace «VartimePrecomputedStraus64bit-notables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«64bit-notables».Insts in
/-- `VartimePrecomputedStraus::len` (backend): the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«64bit-notables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄ := by
  rcases self with ⟨inner⟩
  unfold len
  step as ⟨r, h⟩
  simp only [h, VartimePrecomputedStraus.«64bit-notables».points, List.length_map]

end «VartimePrecomputedStraus64bit-notables»

namespace «VartimePrecomputedStraus32bit-notables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«32bit-notables».Insts in
/-- `VartimePrecomputedStraus::len` (backend): the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«32bit-notables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄ := by
  rcases self with ⟨inner⟩
  unfold len
  step as ⟨r, h⟩
  simp only [h, VartimePrecomputedStraus.«32bit-notables».points, List.length_map]

end «VartimePrecomputedStraus32bit-notables»

end Curve25519Dalek.backend
