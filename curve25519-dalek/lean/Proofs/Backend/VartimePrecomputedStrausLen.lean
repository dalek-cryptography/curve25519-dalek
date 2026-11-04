/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Iterator
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
theorem len_spec (self : VartimePrecomputedStraus.«x86_64-tables»)
    (ps : List curve25519.edwards.Point)
    (hself : self.Represents ps) :
    len self ⦃ (r : Usize) => r.val = ps.length ⦄ := by
  rcases self with ⟨inner⟩
  unfold len
  exact «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables».len_spec
      inner ps hself

end «VartimePrecomputedStrausx86_64-tables»

namespace «VartimePrecomputedStrausi686-tables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«i686-tables».Insts in
/-- `VartimePrecomputedStraus::len` (backend): the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«i686-tables»)
    (ps : List curve25519.edwards.Point)
    (hself : self.Represents ps) :
    len self ⦃ (r : Usize) => r.val = ps.length ⦄ := by
  rcases self with ⟨inner⟩
  unfold len
  exact «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables».len_spec
      inner ps hself

end «VartimePrecomputedStrausi686-tables»

namespace «VartimePrecomputedStrausx86_64-no-tables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«x86_64-no-tables».Insts in
/-- `VartimePrecomputedStraus::len` (backend): the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«x86_64-no-tables»)
    (ps : List curve25519.edwards.Point)
    (hself : self.Represents ps) :
    len self ⦃ (r : Usize) => r.val = ps.length ⦄ := by
  rcases self with ⟨inner⟩
  unfold len
  exact
      «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables».len_spec
      inner ps hself

end «VartimePrecomputedStrausx86_64-no-tables»

namespace «VartimePrecomputedStrausi686-no-tables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«i686-no-tables».Insts in
/-- `VartimePrecomputedStraus::len` (backend): the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«i686-no-tables»)
    (ps : List curve25519.edwards.Point)
    (hself : self.Represents ps) :
    len self ⦃ (r : Usize) => r.val = ps.length ⦄ := by
  rcases self with ⟨inner⟩
  unfold len
  exact
      «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables».len_spec
      inner ps hself

end «VartimePrecomputedStrausi686-no-tables»

end Curve25519Dalek.backend
