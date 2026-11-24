module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Edwards.BasepointTableBasepoint
import Proofs.Edwards.BasepointTableCreate
public section

/-! # `From<&BasepointTableA> for BasepointTableB` (the twenty conversions)

`create(&table.basepoint())`: the new table represents the same point. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix3264bit-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix32.«64bit-tables»)
    (htable : table.LimbsLt 54) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTable.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix3264bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix3232bit-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix32.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTable.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix3232bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix6464bit-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix64.«64bit-tables»)
    (htable : table.LimbsLt 54) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTable.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix6464bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix6432bit-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix64.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTable.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix6432bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix12864bit-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix128.«64bit-tables»)
    (htable : table.LimbsLt 54) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTable.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix12864bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix12832bit-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix128.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTable.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix12832bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix25664bit-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix256.«64bit-tables»)
    (htable : table.LimbsLt 54) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTable.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix25664bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix25632bit-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTable`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix256.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTable.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix25632bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTable64bit-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTable.«64bit-tables») (htable : table.LimbsLt 54)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTable64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTable32bit-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTable.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTable32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix6464bit-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix64.«64bit-tables»)
    (htable : table.LimbsLt 54) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix6464bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix6432bit-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix64.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix6432bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix12864bit-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix128.«64bit-tables»)
    (htable : table.LimbsLt 54) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix12864bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix12832bit-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix128.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix12832bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix25664bit-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix256.«64bit-tables»)
    (htable : table.LimbsLt 54) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix25664bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix25632bit-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix32`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix256.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix32.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix25632bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTable64bit-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTable.«64bit-tables») (htable : table.LimbsLt 54)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTable64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTable32bit-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTable.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTable32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix3264bit-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix32.«64bit-tables»)
    (htable : table.LimbsLt 54) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix3264bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix3232bit-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix32.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix3232bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix12864bit-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix128.«64bit-tables»)
    (htable : table.LimbsLt 54) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix12864bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix12832bit-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix128.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix12832bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix25664bit-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix256.«64bit-tables»)
    (htable : table.LimbsLt 54) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix25664bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix25632bit-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix64`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix256.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix64.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix25632bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTable64bit-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTable.«64bit-tables») (htable : table.LimbsLt 54)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTable64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTable32bit-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTable.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTable32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix3264bit-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix32.«64bit-tables»)
    (htable : table.LimbsLt 54) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix3264bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix3232bit-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix32.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix3232bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix6464bit-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix64.«64bit-tables»)
    (htable : table.LimbsLt 54) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix6464bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix6432bit-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix64.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix6432bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix25664bit-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix256.«64bit-tables»)
    (htable : table.LimbsLt 54) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix25664bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix25632bit-tables»

/-- `From<&EdwardsBasepointTableRadix256> for EdwardsBasepointTableRadix128`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix256.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix128.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix25632bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTable64bit-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTable.«64bit-tables») (htable : table.LimbsLt 54)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTable64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTable32bit-tables»

/-- `From<&EdwardsBasepointTable> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTable.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTable32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix3264bit-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix32.«64bit-tables»)
    (htable : table.LimbsLt 54) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix3264bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix3232bit-tables»

/-- `From<&EdwardsBasepointTableRadix32> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix32.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix3232bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix6464bit-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix64.«64bit-tables»)
    (htable : table.LimbsLt 54) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix6464bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix6432bit-tables»

/-- `From<&EdwardsBasepointTableRadix64> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix64.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix6432bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«64bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix12864bit-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^54`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix128.«64bit-tables»)
    (htable : table.LimbsLt 54) (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«64bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 54 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix12864bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«32bit-tables».Insts
namespace «CoreConvertFromSharedAEdwardsBasepointTableRadix12832bit-tables»

/-- `From<&EdwardsBasepointTableRadix128> for EdwardsBasepointTableRadix256`: a table of the same
point; limbs `< 2^27`. -/
@[step]
theorem from_spec (table : EdwardsBasepointTableRadix128.«32bit-tables») (htable : table.LimbsLt 27)
    (hP : table.IsTable) :
    «from» table ⦃ (r : EdwardsBasepointTableRadix256.«32bit-tables») =>
      r.IsTable ∧ r.point = table.point ∧ r.LimbsLt 27 ⦄ := by
  unfold «from»
  step*

end «CoreConvertFromSharedAEdwardsBasepointTableRadix12832bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«32bit-tables».Insts

