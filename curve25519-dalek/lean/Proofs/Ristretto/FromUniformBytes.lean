/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Ristretto.Map
public import Defs.Edwards
import Proofs.Backend.Serial.U64.Field.FromBytes
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
import Proofs.Helpers.ToField
import Proofs.Ristretto.Add
import Proofs.Ristretto.Elligator
import Proofs.Backend.Serial.U32.Field.FromBytes
import Proofs.Helpers.ToField2625
public section

/-! # `RistrettoPoint::from_uniform_bytes`

RFC 9496 §4.3.4's one-way map: the Elligator map of each 32-byte half, added. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.ristretto

namespace «RistrettoPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `RistrettoPoint::from_uniform_bytes`: RFC 9496's one-way map of the 64 bytes' little-endian
value, `MAP(r₀) + MAP(r₁)` for the two halves: an even point (a ristretto255 representative);
limbs `< 2^52`. -/
@[step]
theorem from_uniform_bytes_spec (bytes : Array U8 64#usize) :
    from_uniform_bytes bytes ⦃ (r : RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.fromUniformRep (bytes.asNat 8) ∧
        r.LimbsLt 52 ⦄ := by
  unfold from_uniform_bytes
  step*
  have hlen : bytes.val.length = 64 := bytes.property
  have hA : (to_slice_mut_back s2).val = bytes.val.take 32 := by
    rw [to_slice_mut_back_post, s2_post, Array.from_slice_val _ _ (by
      rw [s1_post, List.slice_length, Array.val_to_slice, hlen]; rfl), s1_post,
      Array.val_to_slice, List.slice_zero_j]
  have hB : (to_slice_mut_back1 s5).val = bytes.val.drop 32 := by
    rw [to_slice_mut_back1_post, s5_post, Array.from_slice_val _ _ (by
      rw [s4_post, List.slice_length, Array.val_to_slice, hlen]; rfl), s4_post,
      Array.val_to_slice, List.slice, List.take_of_length_le (by simp [hlen])]
  obtain ⟨h1, -⟩ := Array.asNat_append_eq bytes (to_slice_mut_back s2) (to_slice_mut_back1 s5)
    (by rw [hA, hB, List.take_append_drop])
  obtain ⟨-, h2⟩ := Array.asNat_append_eq bytes (to_slice_mut_back s2) (to_slice_mut_back1 s5)
    (by rw [hA, hB, List.take_append_drop])
  refine (fun h => ⟨r_post, by rw [h]; exact Ristretto.even_fromUniformRep _, h, r_post2⟩) ?_
  rw [r_post1, R_1_post1, R_2_post1, toField_eq_decodeU_of_asNat_eq r_1_post,
    toField_eq_decodeU_of_asNat_eq r_2_post, h1, h2, Ristretto.fromUniformRep_def]
  rfl

end «RistrettoPointx86_64-tables»

namespace «RistrettoPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `RistrettoPoint::from_uniform_bytes`: RFC 9496's one-way map of the 64 bytes' little-endian
value, `MAP(r₀) + MAP(r₁)` for the two halves: an even point (a ristretto255 representative);
limbs `< 2^26`. -/
@[step]
theorem from_uniform_bytes_spec (bytes : Array U8 64#usize) :
    from_uniform_bytes bytes ⦃ (r : RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.fromUniformRep (bytes.asNat 8) ∧
        r.LimbsLt 26 ⦄ := by
  unfold from_uniform_bytes
  step*
  have hlen : bytes.val.length = 64 := bytes.property
  have hA : (to_slice_mut_back s2).val = bytes.val.take 32 := by
    rw [to_slice_mut_back_post, s2_post, Array.from_slice_val _ _ (by
      rw [s1_post, List.slice_length, Array.val_to_slice, hlen]; rfl), s1_post,
      Array.val_to_slice, List.slice_zero_j]
  have hB : (to_slice_mut_back1 s5).val = bytes.val.drop 32 := by
    rw [to_slice_mut_back1_post, s5_post, Array.from_slice_val _ _ (by
      rw [s4_post, List.slice_length, Array.val_to_slice, hlen]; rfl), s4_post,
      Array.val_to_slice, List.slice, List.take_of_length_le (by simp [hlen])]
  obtain ⟨h1, -⟩ := Array.asNat_append_eq bytes (to_slice_mut_back s2) (to_slice_mut_back1 s5)
    (by rw [hA, hB, List.take_append_drop])
  obtain ⟨-, h2⟩ := Array.asNat_append_eq bytes (to_slice_mut_back s2) (to_slice_mut_back1 s5)
    (by rw [hA, hB, List.take_append_drop])
  refine (fun h => ⟨r_post, by rw [h]; exact Ristretto.even_fromUniformRep _, h, r_post2⟩) ?_
  rw [r_post1, R_1_post1, R_2_post1, toField_eq_decodeU_of_mod r_1_post,
    toField_eq_decodeU_of_mod r_2_post, h1, h2, Ristretto.fromUniformRep_def]
  rfl

end «RistrettoPointi686-tables»

namespace «RistrettoPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `RistrettoPoint::from_uniform_bytes`: RFC 9496's one-way map of the 64 bytes' little-endian
value, `MAP(r₀) + MAP(r₁)` for the two halves: an even point (a ristretto255 representative);
limbs `< 2^52`. -/
@[step]
theorem from_uniform_bytes_spec (bytes : Array U8 64#usize) :
    from_uniform_bytes bytes ⦃ (r : RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.fromUniformRep (bytes.asNat 8) ∧
        r.LimbsLt 52 ⦄ := by
  unfold from_uniform_bytes
  step*
  have hlen : bytes.val.length = 64 := bytes.property
  have hA : (to_slice_mut_back s2).val = bytes.val.take 32 := by
    rw [to_slice_mut_back_post, s2_post, Array.from_slice_val _ _ (by
      rw [s1_post, List.slice_length, Array.val_to_slice, hlen]; rfl), s1_post,
      Array.val_to_slice, List.slice_zero_j]
  have hB : (to_slice_mut_back1 s5).val = bytes.val.drop 32 := by
    rw [to_slice_mut_back1_post, s5_post, Array.from_slice_val _ _ (by
      rw [s4_post, List.slice_length, Array.val_to_slice, hlen]; rfl), s4_post,
      Array.val_to_slice, List.slice, List.take_of_length_le (by simp [hlen])]
  obtain ⟨h1, -⟩ := Array.asNat_append_eq bytes (to_slice_mut_back s2) (to_slice_mut_back1 s5)
    (by rw [hA, hB, List.take_append_drop])
  obtain ⟨-, h2⟩ := Array.asNat_append_eq bytes (to_slice_mut_back s2) (to_slice_mut_back1 s5)
    (by rw [hA, hB, List.take_append_drop])
  refine (fun h => ⟨r_post, by rw [h]; exact Ristretto.even_fromUniformRep _, h, r_post2⟩) ?_
  rw [r_post1, R_1_post1, R_2_post1, toField_eq_decodeU_of_asNat_eq r_1_post,
    toField_eq_decodeU_of_asNat_eq r_2_post, h1, h2, Ristretto.fromUniformRep_def]
  rfl

end «RistrettoPointx86_64-no-tables»

namespace «RistrettoPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `RistrettoPoint::from_uniform_bytes`: RFC 9496's one-way map of the 64 bytes' little-endian
value, `MAP(r₀) + MAP(r₁)` for the two halves: an even point (a ristretto255 representative);
limbs `< 2^26`. -/
@[step]
theorem from_uniform_bytes_spec (bytes : Array U8 64#usize) :
    from_uniform_bytes bytes ⦃ (r : RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.fromUniformRep (bytes.asNat 8) ∧
        r.LimbsLt 26 ⦄ := by
  unfold from_uniform_bytes
  step*
  have hlen : bytes.val.length = 64 := bytes.property
  have hA : (to_slice_mut_back s2).val = bytes.val.take 32 := by
    rw [to_slice_mut_back_post, s2_post, Array.from_slice_val _ _ (by
      rw [s1_post, List.slice_length, Array.val_to_slice, hlen]; rfl), s1_post,
      Array.val_to_slice, List.slice_zero_j]
  have hB : (to_slice_mut_back1 s5).val = bytes.val.drop 32 := by
    rw [to_slice_mut_back1_post, s5_post, Array.from_slice_val _ _ (by
      rw [s4_post, List.slice_length, Array.val_to_slice, hlen]; rfl), s4_post,
      Array.val_to_slice, List.slice, List.take_of_length_le (by simp [hlen])]
  obtain ⟨h1, -⟩ := Array.asNat_append_eq bytes (to_slice_mut_back s2) (to_slice_mut_back1 s5)
    (by rw [hA, hB, List.take_append_drop])
  obtain ⟨-, h2⟩ := Array.asNat_append_eq bytes (to_slice_mut_back s2) (to_slice_mut_back1 s5)
    (by rw [hA, hB, List.take_append_drop])
  refine (fun h => ⟨r_post, by rw [h]; exact Ristretto.even_fromUniformRep _, h, r_post2⟩) ?_
  rw [r_post1, R_1_post1, R_2_post1, toField_eq_decodeU_of_mod r_1_post,
    toField_eq_decodeU_of_mod r_2_post, h1, h2, Ristretto.fromUniformRep_def]
  rfl

end «RistrettoPointi686-no-tables»

end Curve25519Dalek.ristretto
