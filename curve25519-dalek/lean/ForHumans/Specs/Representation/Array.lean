module
public import Aeneas.Std.Array.Array
import Mathlib.Data.Nat.Digits.Defs
public section

open Aeneas.Std

/-- The natural number with the array's elements as little-endian digits in radix `2^bits`:
`a[0] + 2^bits · a[1] + 2^(2 bits) · a[2] + …`. The digits may exceed `2^bits`.
Bytes use `bits = 8`. -/
def Aeneas.Std.Array.asNat {ty : UScalarTy} {n : Usize} (bits : ℕ) (a : Array (UScalar ty) n) : ℕ :=
  Nat.ofDigits (2 ^ bits) (a.val.map (·.val))

namespace Aeneas.Std

/-- The bytes of a byte array, as a `Vector UInt8`. -/
@[expose] def Array.toVector {n : Usize} (a : Array U8 n) : Vector UInt8 n.val :=
  ⟨(a.val.map fun x => UInt8.ofBitVec x.bv).toArray, by simp⟩

end Aeneas.Std
