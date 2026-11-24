module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
public import Proofs.Curve25519.Edwards.Basepoint
public import Proofs.External.Subtle
import Proofs.Edwards.Neg
public section

/-! # `Neg` for `RistrettoPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace «Shared0RistrettoPoint64bit-tables».Insts.«CoreOpsArithNegRistrettoPoint64bit-tables»

open «Shared0EdwardsPoint64bit-tables» in
/-- `Neg for &RistrettoPoint` negates the represented point. -/
@[step]
theorem neg_spec (self : ristretto.RistrettoPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold neg
  step with
    Insts.«CoreOpsArithNegEdwardsPoint64bit-tables».neg_spec
    self hself hon as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «Shared0RistrettoPoint64bit-tables».Insts.«CoreOpsArithNegRistrettoPoint64bit-tables»

namespace «Shared0RistrettoPoint32bit-tables».Insts.«CoreOpsArithNegRistrettoPoint32bit-tables»

open «Shared0EdwardsPoint32bit-tables» in
/-- `Neg for &RistrettoPoint` negates the represented point. -/
@[step]
theorem neg_spec (self : ristretto.RistrettoPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold neg
  step with
    Insts.«CoreOpsArithNegEdwardsPoint32bit-tables».neg_spec
    self hself hon as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «Shared0RistrettoPoint32bit-tables».Insts.«CoreOpsArithNegRistrettoPoint32bit-tables»

namespace ristretto.RistrettoPoint.«64bit-tables».Insts
namespace «CoreOpsArithNegRistrettoPoint64bit-tables»

/-- `Neg for RistrettoPoint` negates the represented point. -/
@[step]
theorem neg_spec (self : ristretto.RistrettoPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold neg
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithNegRistrettoPoint64bit-tables»
end ristretto.RistrettoPoint.«64bit-tables».Insts

namespace ristretto.RistrettoPoint.«32bit-tables».Insts
namespace «CoreOpsArithNegRistrettoPoint32bit-tables»

/-- `Neg for RistrettoPoint` negates the represented point. -/
@[step]
theorem neg_spec (self : ristretto.RistrettoPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold neg
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithNegRistrettoPoint32bit-tables»
end ristretto.RistrettoPoint.«32bit-tables».Insts

namespace «Shared0RistrettoPoint64bit-notables».Insts
namespace «CoreOpsArithNegRistrettoPoint64bit-notables»

open «Shared0EdwardsPoint64bit-notables» in
/-- `Neg for &RistrettoPoint` negates the represented point. -/
@[step]
theorem neg_spec (self : ristretto.RistrettoPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold neg
  step with
    Insts.«CoreOpsArithNegEdwardsPoint64bit-notables».neg_spec
    self hself hon as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithNegRistrettoPoint64bit-notables»
end «Shared0RistrettoPoint64bit-notables».Insts

namespace «Shared0RistrettoPoint32bit-notables».Insts
namespace «CoreOpsArithNegRistrettoPoint32bit-notables»

open «Shared0EdwardsPoint32bit-notables» in
/-- `Neg for &RistrettoPoint` negates the represented point. -/
@[step]
theorem neg_spec (self : ristretto.RistrettoPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold neg
  step with
    Insts.«CoreOpsArithNegEdwardsPoint32bit-notables».neg_spec
    self hself hon as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithNegRistrettoPoint32bit-notables»
end «Shared0RistrettoPoint32bit-notables».Insts

namespace ristretto.RistrettoPoint.«64bit-notables».Insts
namespace «CoreOpsArithNegRistrettoPoint64bit-notables»

/-- `Neg for RistrettoPoint` negates the represented point. -/
@[step]
theorem neg_spec (self : ristretto.RistrettoPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold neg
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithNegRistrettoPoint64bit-notables»
end ristretto.RistrettoPoint.«64bit-notables».Insts

namespace ristretto.RistrettoPoint.«32bit-notables».Insts
namespace «CoreOpsArithNegRistrettoPoint32bit-notables»

/-- `Neg for RistrettoPoint` negates the represented point. -/
@[step]
theorem neg_spec (self : ristretto.RistrettoPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    neg self ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = -self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold neg
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithNegRistrettoPoint32bit-notables»
end ristretto.RistrettoPoint.«32bit-notables».Insts

end Curve25519Dalek
