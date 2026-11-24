module
public import Proofs.Curve25519.Prime
public import Mathlib.Algebra.Field.ZMod
public import EllipticCurve.TwistedEdwards.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
public section

namespace curve25519

/-- The twisted Edwards model `-x² + y² = 1 + d x² y²` of curve25519 (edwards25519). -/
noncomputable def edwards : TwistedEdwardsModel (ZMod p) := ⟨a, d⟩

/-- The Montgomery model `v² = u³ + A u² + u` of curve25519. -/
def montgomery : MontgomeryModel (ZMod p) := ⟨(A : ZMod p), 1⟩

end curve25519
