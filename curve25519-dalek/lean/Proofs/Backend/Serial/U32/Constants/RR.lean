module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Scalar29
public import Proofs.Curve25519.Basic
import Proofs.Helpers.Scalar29
public import Proofs.Helpers.ByteValues
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29 montgomeryRadix)

namespace Curve25519Dalek.backend.serial.u32.constants

theorem RR_spec :
    Scalar29.asNat RR = montgomeryRadix ^ 2 % curve25519.L ∧ RR.LimbsLt 29 := by
  unfold RR
  simp only [scalar.Scalar29.asNat_def, Array.asNat_def]
  rw [scalar.montgomeryRadix_sq_mod_L]
  decide

end Curve25519Dalek.backend.serial.u32.constants
