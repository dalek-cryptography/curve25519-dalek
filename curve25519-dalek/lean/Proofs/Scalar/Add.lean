/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Proofs.Curve25519.Basic
public import Curve25519Dalek.Funs
public import Proofs.Representation.Scalar
public import Proofs.Representation.Scalar29
import Proofs.Backend.Serial.U64.Scalar.Add
import Proofs.Helpers.Scalar
import Proofs.Helpers.Target
import Proofs.Scalar.Scalar52Pack
import Proofs.Scalar.Unpack
import Proofs.Backend.Serial.U32.Scalar.Add
import Proofs.Scalar.Scalar29Pack
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.AddShared0ScalarSharedAScalarScalar

@[step]
theorem add.«64bit-tables_spec» (self rhs : Scalar) (hself : self.asNat < L)
    (hrhs : rhs.asNat < L) :
    add.«64bit-tables» self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄ := by
  unfold add.«64bit-tables»
  step as ⟨a, ha, hab⟩
  step as ⟨b, hb, hbb⟩
  step with backend.serial.u64.scalar.Scalar52.add_spec a b hab hbb (ha ▸ hself) (hb ▸ hrhs)
    as ⟨c, hc, hcb⟩
  step with Scalar52.pack_spec c hcb (lt_two_pow_256_of_lt_L (hc ▸ Nat.mod_lt _ L_pos))
    as ⟨r, hr⟩
  rw [hr, hc, ha, hb]

end Curve25519Dalek.scalar.AddShared0ScalarSharedAScalarScalar

namespace Curve25519Dalek.scalar.AddShared0ScalarSharedAScalarScalar

@[step]
theorem add.«64bit-notables_spec» (self rhs : Scalar) (hself : self.asNat < L)
    (hrhs : rhs.asNat < L) :
    add.«64bit-notables» self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄ :=
  add.«64bit-tables_spec» self rhs hself hrhs

end Curve25519Dalek.scalar.AddShared0ScalarSharedAScalarScalar


namespace Curve25519Dalek.scalar.AddShared0ScalarSharedAScalarScalar

@[step]
theorem add.«32bit-tables_spec» (self rhs : Scalar) (hself : self.asNat < L)
    (hrhs : rhs.asNat < L) :
    add.«32bit-tables» self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄ := by
  unfold add.«32bit-tables»
  step as ⟨a, ha, hab⟩
  step as ⟨b, hb, hbb⟩
  step with backend.serial.u32.scalar.Scalar29.add_spec a b hab hbb (ha ▸ hself) (hb ▸ hrhs)
    as ⟨c, hc, hcb⟩
  step with Scalar29.pack_spec c hcb (lt_two_pow_256_of_lt_L (hc ▸ Nat.mod_lt _ L_pos))
    as ⟨r, hr⟩
  rw [hr, hc, ha, hb]

end Curve25519Dalek.scalar.AddShared0ScalarSharedAScalarScalar

namespace Curve25519Dalek.scalar.AddShared0ScalarSharedAScalarScalar

@[step]
theorem add.«32bit-notables_spec» (self rhs : Scalar) (hself : self.asNat < L)
    (hrhs : rhs.asNat < L) :
    add.«32bit-notables» self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄ :=
  add.«32bit-tables_spec» self rhs hself hrhs

end Curve25519Dalek.scalar.AddShared0ScalarSharedAScalarScalar
namespace Curve25519Dalek.Shared0Scalar.Insts.CoreOpsArithAddSharedAScalarScalar

@[step]
theorem add_spec (self rhs : Scalar) (hself : self.asNat < L)
    (hrhs : rhs.asNat < L) :
    add self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄ := by
  unfold add
  exact dispatch_all_spec
    (scalar.AddShared0ScalarSharedAScalarScalar.add.«64bit-tables_spec» self rhs hself hrhs)
    (scalar.AddShared0ScalarSharedAScalarScalar.add.«64bit-notables_spec» self rhs hself hrhs)
    (scalar.AddShared0ScalarSharedAScalarScalar.add.«32bit-tables_spec» self rhs hself hrhs)
    (scalar.AddShared0ScalarSharedAScalarScalar.add.«32bit-notables_spec» self rhs hself hrhs)

end Curve25519Dalek.Shared0Scalar.Insts.CoreOpsArithAddSharedAScalarScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddSharedBScalarScalar

/-- `Add<&Scalar> for Scalar` (from `define_add_variants!`): forwards to `&Scalar + &Scalar`. -/
@[step]
theorem add_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    add self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄ := by
  unfold add
  step*

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddSharedBScalarScalar

namespace Curve25519Dalek.SharedAScalar.Insts.CoreOpsArithAddScalarScalar

/-- `Add<Scalar> for &Scalar` (from `define_add_variants!`): forwards to `&Scalar + &Scalar`. -/
@[step]
theorem add_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    add self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄ := by
  unfold add
  step*

end Curve25519Dalek.SharedAScalar.Insts.CoreOpsArithAddScalarScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddScalarScalar

/-- `Add<Scalar> for Scalar` (from `define_add_variants!`): forwards to `&Scalar + &Scalar`. -/
@[step]
theorem add_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    add self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄ := by
  unfold add
  step*

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddScalarScalar
