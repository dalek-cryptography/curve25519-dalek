/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import ToAeneas.Iterator
public import Defs.Scalar
public import Defs.ScalarMul
import Proofs.Backend.Serial.ScalarMul.PrecomputedStraus.Len
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

namespace «VartimePrecomputedStrausx86_64-tables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«x86_64-tables».Insts in
/-- `VartimePrecomputedStraus::len` (backend): the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«x86_64-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄ := by
  rcases self with ⟨inner⟩
  unfold len
  step as ⟨r, h⟩
  simp only [h, VartimePrecomputedStraus.«x86_64-tables».points, List.length_map]

end «VartimePrecomputedStrausx86_64-tables»

namespace «VartimePrecomputedStrausi686-tables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«i686-tables».Insts in
/-- `VartimePrecomputedStraus::len` (backend): the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«i686-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄ := by
  rcases self with ⟨inner⟩
  unfold len
  step as ⟨r, h⟩
  simp only [h, VartimePrecomputedStraus.«i686-tables».points, List.length_map]

end «VartimePrecomputedStrausi686-tables»

namespace «VartimePrecomputedStrausx86_64-no-tables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«x86_64-no-tables».Insts in
/-- `VartimePrecomputedStraus::len` (backend): the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«x86_64-no-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄ := by
  rcases self with ⟨inner⟩
  unfold len
  step as ⟨r, h⟩
  simp only [h, VartimePrecomputedStraus.«x86_64-no-tables».points, List.length_map]

end «VartimePrecomputedStrausx86_64-no-tables»

namespace «VartimePrecomputedStrausi686-no-tables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«i686-no-tables».Insts in
/-- `VartimePrecomputedStraus::len` (backend): the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«i686-no-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄ := by
  rcases self with ⟨inner⟩
  unfold len
  step as ⟨r, h⟩
  simp only [h, VartimePrecomputedStraus.«i686-no-tables».points, List.length_map]

end «VartimePrecomputedStrausi686-no-tables»

end Curve25519Dalek.backend
