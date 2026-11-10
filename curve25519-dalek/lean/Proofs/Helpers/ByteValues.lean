/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Encoding
public import Curve25519.Ristretto.Map
public import Curve25519.Montgomery
public import Defs.Edwards
public import Defs.Montgomery
public import Defs.Ristretto
public section

/-! # The values of byte strings (proof helper, not audited)

The specs state the 32-byte types (`MontgomeryPoint`, `CompressedEdwardsY`, `CompressedRistretto`)
through their bytes (`toVector`, a `Vector UInt8 32`) and the RFC functions on byte strings. The
proofs work with the little-endian values: `asNat` of each type, `Array.asNat 8` of a byte array,
and the arithmetic cores (`encodeNat`, `x25519Nat`, …). `Array.decodeLittleEndian_toVector` and
`decodeLittleEndian_toVector` relate the two, and the bridging lemmas below turn each byte-level
statement into the value-level one, for use as a first `simp only` step. -/

open Aeneas Aeneas.Std curve25519

/-- The value of the bytes of `a.toVector` (RFC 7748 `decodeLittleEndian`) is `a.asNat 8`. -/
theorem Aeneas.Std.Array.decodeLittleEndian_toVector {n : Usize} (a : Array U8 n) :
    decodeLittleEndian a.toVector = a.asNat 8 := by
  rw [decodeLittleEndian, Array.toList_toVector, List.map_map, Array.asNat_def]
  norm_num
  rfl

theorem Aeneas.Std.Array.decodeScalar25519_toVector (a : Array U8 32#usize) :
    decodeScalar25519 a.toVector = clamp (a.asNat 8) := by
  rw [decodeScalar25519, Array.decodeLittleEndian_toVector]

theorem Aeneas.Std.Array.mapRep_toVector (a : Array U8 32#usize) :
    Ristretto.mapRep a.toVector = Ristretto.mapRepField (decodeU (a.asNat 8)) := by
  rw [Ristretto.mapRep_eq, Array.decodeLittleEndian_toVector]

theorem Aeneas.Std.Array.fromUniformRep_toVector (a : Array U8 64#usize) :
    Ristretto.fromUniformRep a.toVector = Ristretto.fromUniformRepNat (a.asNat 8) := by
  rw [Ristretto.fromUniformRep_eq, Array.decodeLittleEndian_toVector]

namespace Curve25519Dalek

namespace montgomery

/-- The little-endian value of the 32 bytes. -/
def MontgomeryPoint.asNat (self : MontgomeryPoint) : ℕ :=
  Aeneas.Std.Array.asNat 8 self

theorem MontgomeryPoint.asNat_def (self : MontgomeryPoint) :
    self.asNat = Aeneas.Std.Array.asNat 8 self := by
  unfold MontgomeryPoint.asNat
  rfl

theorem MontgomeryPoint.decodeLittleEndian_toVector (self : MontgomeryPoint) :
    decodeLittleEndian self.toVector = self.asNat :=
  Aeneas.Std.Array.decodeLittleEndian_toVector self

theorem MontgomeryPoint.decodeUCoordinate_toVector (self : MontgomeryPoint) :
    decodeUCoordinate self.toVector = decodeU self.asNat := by
  rw [decodeUCoordinate_eq, MontgomeryPoint.decodeLittleEndian_toVector]

theorem MontgomeryPoint.toVector_eq_encodeUCoordinate_iff (r : MontgomeryPoint) (u : ZMod p) :
    r.toVector = encodeUCoordinate u ↔ r.asNat = encodeU u := by
  rw [eq_encodeUCoordinate_iff, MontgomeryPoint.decodeLittleEndian_toVector]

theorem MontgomeryPoint.toVector_eq_X25519_iff (r : MontgomeryPoint) (k : Array U8 32#usize)
    (s : MontgomeryPoint) :
    r.toVector = X25519 k.toVector s.toVector ↔ r.asNat = x25519Nat (k.asNat 8) s.asNat := by
  rw [eq_X25519_iff, MontgomeryPoint.decodeLittleEndian_toVector,
    Aeneas.Std.Array.decodeLittleEndian_toVector, MontgomeryPoint.decodeLittleEndian_toVector]

theorem MontgomeryPoint.toVector_eq_X25519_nine_iff (r : MontgomeryPoint) (k : Array U8 32#usize) :
    r.toVector = X25519 k.toVector (encodeUCoordinate 9) ↔ r.asNat = x25519Nat (k.asNat 8) 9 := by
  rw [eq_X25519_iff, MontgomeryPoint.decodeLittleEndian_toVector,
    Aeneas.Std.Array.decodeLittleEndian_toVector, decodeLittleEndian_encodeUCoordinate,
    encodeU_nine]

end montgomery

namespace edwards

/-- The little-endian value of the 32 bytes. -/
def CompressedEdwardsY.asNat (self : CompressedEdwardsY) : ℕ :=
  Aeneas.Std.Array.asNat 8 self

theorem CompressedEdwardsY.asNat_def (self : CompressedEdwardsY) :
    self.asNat = Aeneas.Std.Array.asNat 8 self := by
  unfold CompressedEdwardsY.asNat
  rfl

theorem CompressedEdwardsY.decodeLittleEndian_toVector (self : CompressedEdwardsY) :
    decodeLittleEndian self.toVector = self.asNat :=
  Aeneas.Std.Array.decodeLittleEndian_toVector self

theorem CompressedEdwardsY.toVector_eq_encode_iff (r : CompressedEdwardsY)
    (P : curve25519.edwards.Point) :
    r.toVector = encode P ↔ r.asNat = encodeNat P := by
  rw [eq_encode_iff, CompressedEdwardsY.decodeLittleEndian_toVector]

theorem CompressedEdwardsY.decodeLenient_toVector (self : CompressedEdwardsY) :
    decodeLenient self.toVector = decodeLenientNat self.asNat := by
  rw [decodeLenient, CompressedEdwardsY.decodeLittleEndian_toVector]

end edwards

namespace ristretto

/-- The little-endian value of the 32 bytes. -/
def CompressedRistretto.asNat (self : CompressedRistretto) : ℕ :=
  Aeneas.Std.Array.asNat 8 self

theorem CompressedRistretto.asNat_def (self : CompressedRistretto) :
    self.asNat = Aeneas.Std.Array.asNat 8 self := by
  unfold CompressedRistretto.asNat
  rfl

theorem CompressedRistretto.decodeLittleEndian_toVector (self : CompressedRistretto) :
    decodeLittleEndian self.toVector = self.asNat :=
  Aeneas.Std.Array.decodeLittleEndian_toVector self

theorem CompressedRistretto.toVector_eq_encodeRep_iff (r : CompressedRistretto)
    (P : curve25519.edwards.Point) :
    r.toVector = Ristretto.encodeRep P ↔ r.asNat = Ristretto.encodeRepNat P := by
  rw [Ristretto.eq_encodeRep_iff, CompressedRistretto.decodeLittleEndian_toVector]

theorem CompressedRistretto.decodeRep_toVector (self : CompressedRistretto) :
    Ristretto.decodeRep self.toVector = Ristretto.decodeRepNat self.asNat := by
  rw [Ristretto.decodeRep, CompressedRistretto.decodeLittleEndian_toVector]

end ristretto

end Curve25519Dalek
