/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
public import Curve25519.Edwards.Basepoint
public import Subtle
import Proofs.Edwards.Identity
public section

/-! # `Identity` and `Default` for `RistrettoPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for RistrettoPoint` represents the neutral element. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold identity
  step with
    edwards.EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact Even.zero, h2, h3⟩

end ristretto.RistrettoPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity

namespace ristretto.RistrettoPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for RistrettoPoint` represents the neutral element. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold identity
  step with
    edwards.EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact Even.zero, h2, h3⟩

end ristretto.RistrettoPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts.CoreDefaultDefault

/-- `Default for RistrettoPoint` represents the neutral element. -/
@[step]
theorem default_spec :
    default ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold default
  step as ⟨r, h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4⟩

end ristretto.RistrettoPoint.«x86_64-tables».Insts.CoreDefaultDefault

namespace ristretto.RistrettoPoint.«i686-tables».Insts.CoreDefaultDefault

/-- `Default for RistrettoPoint` represents the neutral element. -/
@[step]
theorem default_spec :
    default ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  step as ⟨r, h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4⟩

end ristretto.RistrettoPoint.«i686-tables».Insts.CoreDefaultDefault

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for RistrettoPoint` represents the neutral element. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold identity
  step with
    edwards.EdwardsPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact Even.zero, h2, h3⟩

end ristretto.RistrettoPoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity

/-- `Identity for RistrettoPoint` represents the neutral element. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold identity
  step with
    edwards.EdwardsPoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact Even.zero, h2, h3⟩

end ristretto.RistrettoPoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts.CoreDefaultDefault

/-- `Default for RistrettoPoint` represents the neutral element. -/
@[step]
theorem default_spec :
    default ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold default
  step as ⟨r, h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4⟩

end ristretto.RistrettoPoint.«x86_64-no-tables».Insts.CoreDefaultDefault

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts.CoreDefaultDefault

/-- `Default for RistrettoPoint` represents the neutral element. -/
@[step]
theorem default_spec :
    default ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  step as ⟨r, h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4⟩

end ristretto.RistrettoPoint.«i686-no-tables».Insts.CoreDefaultDefault

end Curve25519Dalek
