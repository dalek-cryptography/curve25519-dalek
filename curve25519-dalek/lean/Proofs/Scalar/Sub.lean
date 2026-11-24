module
public import Proofs.Curve25519.Basic
public import Curve25519Dalek.Funs
public import Proofs.Representation.Scalar
public import Proofs.Representation.Scalar29
import Proofs.Backend.Serial.U64.Scalar.Sub
import Proofs.Helpers.Scalar
import Proofs.Helpers.Target
import Proofs.Scalar.Scalar52Pack
import Proofs.Scalar.Unpack
import Proofs.Backend.Serial.U32.Scalar.Sub
import Proofs.Scalar.Scalar29Pack
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.SubShared0ScalarSharedAScalarScalar

@[step]
theorem sub.«64bit-tables_spec» (self rhs : Scalar) (hself : self.asNat < L)
    (hrhs : rhs.asNat < L) :
    sub.«64bit-tables» self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄ := by
  unfold sub.«64bit-tables»
  step as ⟨a, ha, hab⟩
  step as ⟨b, hb, hbb⟩
  step with backend.serial.u64.scalar.Scalar52.sub_spec a b hab hbb
    (ha ▸ hself.trans_le (Nat.le_add_left _ _)) (hb ▸ hrhs.le) as ⟨c, hc, hcL, hcb⟩
  step with Scalar52.pack_spec c hcb (lt_two_pow_256_of_lt_L hcL) as ⟨r, hr⟩
  rw [hr, ← ha, ← hb]
  exact ⟨hc.trans (Nat.mod_eq_of_lt (by rw [ha]; exact hself)), hcL⟩

end Curve25519Dalek.scalar.SubShared0ScalarSharedAScalarScalar

namespace Curve25519Dalek.scalar.SubShared0ScalarSharedAScalarScalar

@[step]
theorem sub.«64bit-notables_spec» (self rhs : Scalar) (hself : self.asNat < L)
    (hrhs : rhs.asNat < L) :
    sub.«64bit-notables» self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄ :=
  sub.«64bit-tables_spec» self rhs hself hrhs

end Curve25519Dalek.scalar.SubShared0ScalarSharedAScalarScalar


namespace Curve25519Dalek.scalar.SubShared0ScalarSharedAScalarScalar

@[step]
theorem sub.«32bit-tables_spec» (self rhs : Scalar) (hself : self.asNat < L)
    (hrhs : rhs.asNat < L) :
    sub.«32bit-tables» self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄ := by
  unfold sub.«32bit-tables»
  step as ⟨a, ha, hab⟩
  step as ⟨b, hb, hbb⟩
  step with backend.serial.u32.scalar.Scalar29.sub_spec a b hab hbb
    (ha ▸ hself.trans_le (Nat.le_add_left _ _)) (hb ▸ hrhs.le) as ⟨c, hc, hcL, hcb⟩
  step with Scalar29.pack_spec c hcb (lt_two_pow_256_of_lt_L hcL) as ⟨r, hr⟩
  rw [hr, ← ha, ← hb]
  exact ⟨hc.trans (Nat.mod_eq_of_lt (by rw [ha]; exact hself)), hcL⟩

end Curve25519Dalek.scalar.SubShared0ScalarSharedAScalarScalar

namespace Curve25519Dalek.scalar.SubShared0ScalarSharedAScalarScalar

@[step]
theorem sub.«32bit-notables_spec» (self rhs : Scalar) (hself : self.asNat < L)
    (hrhs : rhs.asNat < L) :
    sub.«32bit-notables» self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄ :=
  sub.«32bit-tables_spec» self rhs hself hrhs

end Curve25519Dalek.scalar.SubShared0ScalarSharedAScalarScalar
namespace Curve25519Dalek.Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar

@[step]
theorem sub_spec (self rhs : Scalar) (hself : self.asNat < L)
    (hrhs : rhs.asNat < L) :
    sub self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄ := by
  unfold sub
  exact dispatch_all_spec
    (scalar.SubShared0ScalarSharedAScalarScalar.sub.«64bit-tables_spec» self rhs hself hrhs)
    (scalar.SubShared0ScalarSharedAScalarScalar.sub.«64bit-notables_spec» self rhs hself hrhs)
    (scalar.SubShared0ScalarSharedAScalarScalar.sub.«32bit-tables_spec» self rhs hself hrhs)
    (scalar.SubShared0ScalarSharedAScalarScalar.sub.«32bit-notables_spec» self rhs hself hrhs)

end Curve25519Dalek.Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubSharedBScalarScalar

/-- `Sub<&Scalar> for Scalar` (from `define_sub_variants!`): forwards to `&Scalar - &Scalar`. -/
@[step]
theorem sub_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    sub self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄ := by
  unfold sub
  step*

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubSharedBScalarScalar

namespace Curve25519Dalek.SharedAScalar.Insts.CoreOpsArithSubScalarScalar

/-- `Sub<Scalar> for &Scalar` (from `define_sub_variants!`): forwards to `&Scalar - &Scalar`. -/
@[step]
theorem sub_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    sub self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄ := by
  unfold sub
  step*

end Curve25519Dalek.SharedAScalar.Insts.CoreOpsArithSubScalarScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubScalarScalar

/-- `Sub<Scalar> for Scalar` (from `define_sub_variants!`): forwards to `&Scalar - &Scalar`. -/
@[step]
theorem sub_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    sub self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄ := by
  unfold sub
  step*

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubScalarScalar
