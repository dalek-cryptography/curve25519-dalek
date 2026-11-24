module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
public import Proofs.Curve25519.Edwards.Basepoint
public import Proofs.External.Subtle
import Proofs.Edwards.Identity
public section

/-! # `Identity` and `Default` for `RistrettoPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace ristretto.RistrettoPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for RistrettoPoint` represents the neutral element. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold identity
  step with
    edwards.EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact Even.zero, h2, h3⟩

end ristretto.RistrettoPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity

namespace ristretto.RistrettoPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for RistrettoPoint` represents the neutral element. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold identity
  step with
    edwards.EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact Even.zero, h2, h3⟩

end ristretto.RistrettoPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity

namespace ristretto.RistrettoPoint.«64bit-tables».Insts.CoreDefaultDefault

/-- `Default for RistrettoPoint` represents the neutral element. -/
@[step]
theorem default_spec :
    default ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold default
  step as ⟨r, h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4⟩

end ristretto.RistrettoPoint.«64bit-tables».Insts.CoreDefaultDefault

namespace ristretto.RistrettoPoint.«32bit-tables».Insts.CoreDefaultDefault

/-- `Default for RistrettoPoint` represents the neutral element. -/
@[step]
theorem default_spec :
    default ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  step as ⟨r, h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4⟩

end ristretto.RistrettoPoint.«32bit-tables».Insts.CoreDefaultDefault

namespace ristretto.RistrettoPoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for RistrettoPoint` represents the neutral element. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold identity
  step with
    edwards.EdwardsPoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact Even.zero, h2, h3⟩

end ristretto.RistrettoPoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity

namespace ristretto.RistrettoPoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for RistrettoPoint` represents the neutral element. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold identity
  step with
    edwards.EdwardsPoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact Even.zero, h2, h3⟩

end ristretto.RistrettoPoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity

namespace ristretto.RistrettoPoint.«64bit-notables».Insts.CoreDefaultDefault

/-- `Default for RistrettoPoint` represents the neutral element. -/
@[step]
theorem default_spec :
    default ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold default
  step as ⟨r, h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4⟩

end ristretto.RistrettoPoint.«64bit-notables».Insts.CoreDefaultDefault

namespace ristretto.RistrettoPoint.«32bit-notables».Insts.CoreDefaultDefault

/-- `Default for RistrettoPoint` represents the neutral element. -/
@[step]
theorem default_spec :
    default ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  step as ⟨r, h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4⟩

end ristretto.RistrettoPoint.«32bit-notables».Insts.CoreDefaultDefault

end Curve25519Dalek
