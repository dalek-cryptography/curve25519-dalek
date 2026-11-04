/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Edwards.BasepointTableBasepoint
import Proofs.Edwards.BasepointTableCreate
public section

/-! # `From<&BasepointTableA> for BasepointTableB` (the twenty conversions)

`create(&table.basepoint())`: the new table represents the same point. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix32.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTable.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32i686-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix32.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTable.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix64.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTable.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64i686-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix64.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTable.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix128.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTable.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128i686-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix128.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTable.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix256.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTable.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256i686-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix256.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTable.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTable.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTablei686-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTable.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTablei686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix64.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64i686-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix64.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix128.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128i686-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix128.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix256.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256i686-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix256.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTable.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTablei686-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTable.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTablei686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix32.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32i686-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix32.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix128.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128i686-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix128.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix256.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256i686-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix256.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTable.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTablei686-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTable.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTablei686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix32.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32i686-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix32.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix64.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64i686-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix64.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix256.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix256i686-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix256.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix256i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTable.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTablex86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTablei686-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTable.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTablei686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix32.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix32i686-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix32.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix32i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix64.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix64i686-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix64.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix64i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix128.«x86_64-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 54) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«x86_64-tables») =>
      r.Represents P ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128x86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix128i686-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix128.«i686-tables»)
    (P : curve25519.edwards.Point) (htable : table.LimbsLt 27) (hP : table.Represents P) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«i686-tables») =>
      r.Represents P ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix128i686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

