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
import Proofs.Backend.Serial.ScalarMul.PrecomputedStraus.IsEmpty
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

namespace «VartimePrecomputedStraus64bit-tables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«64bit-tables».Insts in
open «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-tables» renaming
  is_empty_spec → serial_is_empty_spec in
/-- `VartimePrecomputedStraus::is_empty` (backend): whether there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimePrecomputedStraus.«64bit-tables») :
    is_empty self ⦃ (r : Bool) => r = decide (self.points = []) ⦄ := by
  rcases self with ⟨inner⟩
  unfold is_empty
  exact spec_mono (serial_is_empty_spec inner) fun r h => by
    simp only [h, VartimePrecomputedStraus.«64bit-tables».points, List.map_eq_nil_iff]

end «VartimePrecomputedStraus64bit-tables»

namespace «VartimePrecomputedStraus32bit-tables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«32bit-tables».Insts in
open «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-tables» renaming
  is_empty_spec → serial_is_empty_spec in
/-- `VartimePrecomputedStraus::is_empty` (backend): whether there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimePrecomputedStraus.«32bit-tables») :
    is_empty self ⦃ (r : Bool) => r = decide (self.points = []) ⦄ := by
  rcases self with ⟨inner⟩
  unfold is_empty
  exact spec_mono (serial_is_empty_spec inner) fun r h => by
    simp only [h, VartimePrecomputedStraus.«32bit-tables».points, List.map_eq_nil_iff]

end «VartimePrecomputedStraus32bit-tables»

namespace «VartimePrecomputedStraus64bit-notables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«64bit-notables».Insts in
open «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-notables» renaming
  is_empty_spec → serial_is_empty_spec in
/-- `VartimePrecomputedStraus::is_empty` (backend): whether there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimePrecomputedStraus.«64bit-notables») :
    is_empty self ⦃ (r : Bool) => r = decide (self.points = []) ⦄ := by
  rcases self with ⟨inner⟩
  unfold is_empty
  exact spec_mono (serial_is_empty_spec inner) fun r h => by
    simp only [h, VartimePrecomputedStraus.«64bit-notables».points, List.map_eq_nil_iff]

end «VartimePrecomputedStraus64bit-notables»

namespace «VartimePrecomputedStraus32bit-notables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«32bit-notables».Insts in
open «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-notables» renaming
  is_empty_spec → serial_is_empty_spec in
/-- `VartimePrecomputedStraus::is_empty` (backend): whether there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimePrecomputedStraus.«32bit-notables») :
    is_empty self ⦃ (r : Bool) => r = decide (self.points = []) ⦄ := by
  rcases self with ⟨inner⟩
  unfold is_empty
  exact spec_mono (serial_is_empty_spec inner) fun r h => by
    simp only [h, VartimePrecomputedStraus.«32bit-notables».points, List.map_eq_nil_iff]

end «VartimePrecomputedStraus32bit-notables»

end Curve25519Dalek.backend
