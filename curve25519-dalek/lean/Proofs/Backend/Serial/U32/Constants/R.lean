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

theorem R_spec :
    Scalar29.asNat R = montgomeryRadix % curve25519.L ∧ R.LimbsLt 29 := by
  unfold R
  simp only [scalar.Scalar29.asNat_def, Array.asNat_def]
  rw [scalar.montgomeryRadix_mod_L]
  decide

end Curve25519Dalek.backend.serial.u32.constants
