module
public import Curve25519Dalek.Types
public section

open Aeneas Aeneas.Std

namespace Curve25519Dalek.montgomery

/-- Needed for `v[i]!` on vectors of points; the default is never observed for in-range
indices. -/
instance MontgomeryPoint.instInhabited : Inhabited MontgomeryPoint :=
  inferInstanceAs (Inhabited (Array U8 32#usize))

end Curve25519Dalek.montgomery
