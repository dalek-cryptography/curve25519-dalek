/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Ristretto.Encoding
public import Defs.Edwards
public import Defs.Iterator
public import Defs.Ristretto
import Proofs.Backend.Serial.U64.Constants.EdwardsD
import Proofs.Backend.Serial.U64.Constants.InvsqrtAMinusD
import Proofs.Backend.Serial.U64.Constants.SqrtM1
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.ConditionalAssign
import Proofs.Backend.Serial.U64.Field.ConditionalNegate
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Neg
import Proofs.Backend.Serial.U64.Field.Square
import Proofs.Backend.Serial.U64.Field.Sub
import Proofs.Backend.Serial.U64.Field.ToBytes
import Proofs.Field.InvertBatchAlloc
import Proofs.Field.IsNegative
import Proofs.Helpers.Coords
import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
import Proofs.Helpers.RistrettoCompress
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.ToField
import Proofs.Helpers.Vec
import Proofs.Backend.Serial.U32.Constants.EdwardsD
import Proofs.Backend.Serial.U32.Constants.InvsqrtAMinusD
import Proofs.Backend.Serial.U32.Constants.SqrtM1
import Proofs.Backend.Serial.U32.Field.Add
import Proofs.Backend.Serial.U32.Field.ConditionalAssign
import Proofs.Backend.Serial.U32.Field.ConditionalNegate
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.Neg
import Proofs.Backend.Serial.U32.Field.Square
import Proofs.Backend.Serial.U32.Field.Sub
import Proofs.Backend.Serial.U32.Field.ToBytes
import Proofs.Helpers.ToField2625
public import Proofs.Field.Invsqrt
import Proofs.Helpers.Backend.U32.Bytes
import Proofs.Helpers.Backend.U64.Bytes
public section

/-! # `RistrettoPoint::double_and_compress_batch`

The patched code collects a `BatchCompressState` per point (the doubling quantities
`e, f, g, h` and the products `e g`, `f h`), inverts the products `e g · f h` in one batch, and
encodes each doubled point from its state and inverse
(`RistrettoCompress.doubleCompress_eq_encodeRep`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.Backend

variable (B : Backend)

/-- `BatchCompressState::from` over a backend. -/
@[expose] def batchStateBody {S : Type} (mk : B.F → B.F → B.F → B.F → B.F → B.F → S)
    (X Y Z T : B.F) : Result S := do
  let XX ← B.square X
  let YY ← B.square Y
  let ZZ ← B.square Z
  let fe ← B.square T
  let fe1 ← B.constEdwardsD
  let dTT ← B.mul fe fe1
  let fe2 ← B.add Y Y
  let e ← B.mul X fe2
  let f ← B.add ZZ dTT
  let g ← B.add YY XX
  let h ← B.sub ZZ dTT
  let eg ← B.mul e g
  let fh ← B.mul f h
  ok (mk e f g h eg fh)

/-- `batchStateBody`: the doubling quantities `e, f, g, h` of `(X : Y : Z : T)` and the products
`e g`, `f h`. -/
theorem batchStateBody_spec (hadd : B.AddSpec) (hsub : B.SubSpec) (hmul : B.MulSpec)
    (hsq : B.SquareSpec) (hD : B.EdwardsDSpec) {S : Type}
    (mk : B.F → B.F → B.F → B.F → B.F → B.F → S) (X Y Z T : B.F) (hX : B.Red X)
    (hY : B.Red Y) (hZ : B.Red Z) (hT : B.Red T) :
    B.batchStateBody mk X Y Z T ⦃ r => ∃ e f g h eg fh, r = mk e f g h eg fh ∧
      B.toField e = B.toField X * (B.toField Y + B.toField Y) ∧
      B.toField f = B.toField Z ^ 2 + B.toField T ^ 2 * d ∧
      B.toField g = B.toField Y ^ 2 + B.toField X ^ 2 ∧
      B.toField h = B.toField Z ^ 2 - B.toField T ^ 2 * d ∧
      B.toField eg = B.toField e * B.toField g ∧ B.toField fh = B.toField f * B.toField h ∧
      B.SqIn e ∧ B.SqIn f ∧ B.SqIn g ∧ B.SqIn h ∧ B.Red eg ∧ B.Red fh ⦄ := by
  unfold batchStateBody
  step with hsq X (B.red_sqIn hX) as ⟨XX, hXX, hXXb⟩
  step with hsq Y (B.red_sqIn hY) as ⟨YY, hYY, hYYb⟩
  step with hsq Z (B.red_sqIn hZ) as ⟨ZZ, hZZ, hZZb⟩
  step with hsq T (B.red_sqIn hT) as ⟨TT, hTT, hTTb⟩
  apply spec_bind hD
  rintro fd ⟨Fd, hfdb⟩
  step with hmul TT fd (B.red_mulIn hTTb) (B.red_mulIn hfdb) as ⟨dTT, hdTT, hdTTb⟩
  step with hadd Y Y hY hY as ⟨Y2, hY2, hY2b⟩
  step with hmul X Y2 (B.red_mulIn hX) (B.sum2_mulIn hY2b) as ⟨e, he, heb⟩
  step with hadd ZZ dTT hZZb hdTTb as ⟨f, hf, hfb⟩
  step with hadd YY XX hYYb hXXb as ⟨g, hg, hgb⟩
  step with hsub ZZ dTT (B.red_mulIn hZZb) (B.red_mulIn hdTTb) as ⟨h, hh, hhb⟩
  step with hmul e g (B.red_mulIn heb) (B.sum2_mulIn hgb) as ⟨eg, heg, hegb⟩
  step with hmul f h (B.sum2_mulIn hfb) (B.red_mulIn hhb) as ⟨fh, hfh, hfhb⟩
  refine ⟨e, f, g, h, eg, fh, rfl, by rw [he, hY2], by rw [hf, hZZ, hdTT, hTT, Fd],
    by rw [hg, hYY, hXX], by rw [hh, hZZ, hdTT, hTT, Fd], heg, hfh, B.red_sqIn heb,
    B.sum2_sqIn hfb, B.sum2_sqIn hgb, B.red_sqIn hhb, hegb, hfhb⟩

/-- The encoding step of `double_and_compress_batch`'s second loop over a backend. -/
@[expose] def compressStateBody (e f g h eg fh inv : B.F) : Result (Array U8 32#usize) := do
  let Zinv ← B.mul eg inv
  let Tinv ← B.mul fh inv
  let magic ← B.constInvsqrtAMinusD
  let fe ← B.mul eg Zinv
  let negcheck1 ← B.isNegative fe
  let minus_e ← B.neg e
  let fe1 ← B.constSqrtM1
  let f_times_sqrta ← B.mul f fe1
  let e1 ← B.condAssign e g negcheck1
  let g1 ← B.condAssign g minus_e negcheck1
  let h1 ← B.condAssign h f_times_sqrta negcheck1
  let magic1 ← B.condAssign magic fe1 negcheck1
  let fe2 ← B.mul h1 e1
  let fe3 ← B.mul fe2 Zinv
  let negcheck2 ← B.isNegative fe3
  let g2 ← B.condNeg g1 negcheck2
  let fe4 ← B.sub h1 g2
  let fe5 ← B.mul g2 Tinv
  let fe6 ← B.mul magic1 fe5
  let s ← B.mul fe4 fe6
  let s_is_negative ← B.isNegative s
  let s1 ← B.condNeg s s_is_negative
  B.toBytes s1

/-- `compressStateBody`: from the state of `P` and the inverse of `e g · f h`, the bytes of
`2 P`. -/
theorem compressStateBody_spec (hsub : B.SubSpec) (hmul : B.MulSpec) (hneg : B.NegSpec)
    (hm1 : B.SqrtM1Spec) (hiad : B.InvsqrtAMinusDSpec) (hisn : B.IsNegativeSpec)
    (hca : B.CondAssignSpec) (hcng : B.CondNegSpec) (htb : B.ToBytesSpec)
    (e f g h eg fh inv : B.F) {X Y Z T : ZMod p}
    (hP : (⟨X, Y, Z, T⟩ : edwards.Extended).OnCurve)
    (Se : B.toField e = X * (Y + Y)) (Sf : B.toField f = Z ^ 2 + T ^ 2 * d)
    (Sg : B.toField g = Y ^ 2 + X ^ 2) (Sh : B.toField h = Z ^ 2 - T ^ 2 * d)
    (Seg : B.toField eg = B.toField e * B.toField g)
    (Sfh : B.toField fh = B.toField f * B.toField h) (Seb : B.SqIn e) (Sfb : B.SqIn f)
    (Sgb : B.SqIn g) (Shb : B.SqIn h) (Segb : B.Red eg) (Sfhb : B.Red fh)
    (Inv : B.toField inv = (B.toField eg * B.toField fh)⁻¹) (Invb : B.Red inv) :
    B.compressStateBody e f g h eg fh inv ⦃ (bytes : ristretto.CompressedRistretto) =>
      bytes.asNat = Ristretto.encodeRep (2 • (⟨X, Y, Z, T⟩ : edwards.Extended).toPoint) ⦄ := by
  have hx : (⟨X, Y, Z, T⟩ : edwards.Extended).toPoint.x = X / Z :=
    TwistedEdwardsModel.Extended.toPoint_x hP
  have hy : (⟨X, Y, Z, T⟩ : edwards.Extended).toPoint.y = Y / Z :=
    TwistedEdwardsModel.Extended.toPoint_y hP
  obtain ⟨hZ0, hXYZT, -⟩ := hP
  unfold compressStateBody
  step with hmul eg inv (B.red_mulIn Segb) (B.red_mulIn Invb) as ⟨Zinv, hZinv, hZinvb⟩
  step with hmul fh inv (B.red_mulIn Sfhb) (B.red_mulIn Invb) as ⟨Tinv, hTinv, hTinvb⟩
  apply spec_bind hiad
  rintro magic ⟨Mg, hmb⟩
  step with hmul eg Zinv (B.red_mulIn Segb) (B.red_mulIn hZinvb) as ⟨fe, hfe, hfeb⟩
  step with hisn fe as ⟨n1, hn1v, hn1⟩
  step with hneg e (B.sqIn_mulIn Seb) as ⟨me, hme, hmeb⟩
  apply spec_bind hm1
  rintro fi ⟨Fi, hfib⟩
  step with hmul f fi (B.sqIn_mulIn Sfb) (B.red_mulIn hfib) as ⟨fts, hfts, hftsb⟩
  step with hca e g n1 hn1v as ⟨e1, he10, he11⟩
  step with hca g me n1 hn1v as ⟨g1, hg10, hg11⟩
  step with hca h fts n1 hn1v as ⟨h1, hh10, hh11⟩
  step with hca magic fi n1 hn1v as ⟨mg1, hmg10, hmg11⟩
  have he1b : B.SqIn e1 := by
    rcases hn1v with h | h
    · rw [he10 h]; exact Seb
    · rw [he11 h]; exact Sgb
  have hg1b : B.SqIn g1 := by
    rcases hn1v with h | h
    · rw [hg10 h]; exact Sgb
    · rw [hg11 h]; exact B.red_sqIn hmeb
  have hh1b : B.SqIn h1 := by
    rcases hn1v with h | h
    · rw [hh10 h]; exact Shb
    · rw [hh11 h]; exact B.red_sqIn hftsb
  have hmg1b : B.Red mg1 := by
    rcases hn1v with h | h
    · rw [hmg10 h]; exact hmb
    · rw [hmg11 h]; exact hfib
  step with hmul h1 e1 (B.sqIn_mulIn hh1b) (B.sqIn_mulIn he1b) as ⟨fe2, hfe2, hfe2b⟩
  step with hmul fe2 Zinv (B.red_mulIn hfe2b) (B.red_mulIn hZinvb) as ⟨fe3, hfe3, hfe3b⟩
  step with hisn fe3 as ⟨n2, hn2v, hn2⟩
  step with hcng g1 n2 hn2v (B.sqIn_mulIn hg1b) as ⟨g2, hg20, hg21⟩
  have hg2b : B.SqIn g2 := by
    rcases hn2v with h | h
    · rw [hg20 h]; exact hg1b
    · exact B.red_sqIn (hg21 h).2
  step with hsub h1 g2 (B.sqIn_mulIn hh1b) (B.sqIn_mulIn hg2b) as ⟨fe4, hfe4, hfe4b⟩
  step with hmul g2 Tinv (B.sqIn_mulIn hg2b) (B.red_mulIn hTinvb) as ⟨fe5, hfe5, hfe5b⟩
  step with hmul mg1 fe5 (B.red_mulIn hmg1b) (B.red_mulIn hfe5b) as ⟨fe6, hfe6, hfe6b⟩
  step with hmul fe4 fe6 (B.red_mulIn hfe4b) (B.red_mulIn hfe6b) as ⟨sv, hsv, hsvb⟩
  step with hisn sv as ⟨sn, hsnv, hsn⟩
  step with hcng sv sn hsnv (B.red_mulIn hsvb) as ⟨s1, hs10, hs11⟩
  step with htb s1 as ⟨bytes, hbytes⟩
  -- the field values
  have C : B.toField magic ^ 2 * (a - d) = 1 := by rw [Mg, invsqrtAMinusD_sq_mul]
  have Neg1 := eq_one_iff_isNeg hn1
  have E1 : B.toField e1 = if (B.toField fe).IsNeg then B.toField g else B.toField e :=
    eq_ite_of_choice hn1v Neg1 (fun h => by rw [he10 h]) (fun h => by rw [he11 h])
  have G1 : B.toField g1 = if (B.toField fe).IsNeg then -B.toField e else B.toField g :=
    eq_ite_of_choice hn1v Neg1 (fun h => by rw [hg10 h]) (fun h => by rw [hg11 h]; exact hme)
  have H1 : B.toField h1 =
      if (B.toField fe).IsNeg then B.toField f * sqrtM1 else B.toField h :=
    eq_ite_of_choice hn1v Neg1 (fun h => by rw [hh10 h])
      (fun h => by rw [hh11 h, hfts, Fi])
  have M1 : B.toField mg1 =
      if (B.toField fe).IsNeg then (sqrtM1 : ZMod p) else B.toField magic :=
    eq_ite_of_choice hn1v Neg1 (fun h => by rw [hmg10 h]) (fun h => by rw [hmg11 h, Fi])
  have G2 : B.toField g2 = if (B.toField fe3).IsNeg then -B.toField g1 else B.toField g1 :=
    eq_ite_of_choice hn2v (eq_one_iff_isNeg hn2) (fun h => by rw [hg20 h])
      (fun h => (hg21 h).1)
  have S1 : B.toField s1 = (B.toField sv).abs :=
    eq_ite_of_choice hsnv (eq_one_iff_isNeg hsn) (fun h => by rw [hs10 h])
      (fun h => (hs11 h).1)
  rw [ristretto.CompressedRistretto.asNat_def, hbytes, S1,
    ← RistrettoCompress.doubleCompress_eq_encodeRep _ C hZ0 hXYZT hx hy, ← Se, ← Sf, ← Sg,
    ← Sh]
  congr 1
  dsimp only [RistrettoCompress.doubleCompress]
  rw [hsv, hfe4, hfe6, hfe5, G2, hfe3, hfe2, H1, E1, G1, M1, hfe, hZinv, hTinv, Inv, Seg, Sfh]

end Curve25519Dalek.Backend

namespace Curve25519Dalek.ristretto

namespace «RistrettoPointx86_64-tables».double_and_compress_batch

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- The state of a point `P`: its doubling quantities as field elements, with their limb bounds. -/
private def StateOf (P : RistrettoPoint.«x86_64-tables») (st : BatchCompressState) : Prop :=
  st.e.toField = P.X.toField * (P.Y.toField + P.Y.toField) ∧
  st.f.toField = P.Z.toField ^ 2 + P.T.toField ^ 2 * d ∧
  st.g.toField = P.Y.toField ^ 2 + P.X.toField ^ 2 ∧
  st.h.toField = P.Z.toField ^ 2 - P.T.toField ^ 2 * d ∧
  st.eg.toField = st.e.toField * st.g.toField ∧ st.fh.toField = st.f.toField * st.h.toField ∧
  st.e.LimbsLt 54 ∧ st.f.LimbsLt 54 ∧ st.g.LimbsLt 54 ∧ st.h.LimbsLt 54 ∧ st.eg.LimbsLt 52 ∧
  st.fh.LimbsLt 52

private theorem from_eq (P : RistrettoPoint.«x86_64-tables») :
    BatchCompressState.Insts.«CoreConvertFromSharedARistrettoPointx86_64-tables».from P =
      Backend.batchStateBody Backend.U64
        (fun e f g h eg fh => (⟨e, f, g, h, eg, fh⟩ : BatchCompressState))
        P.X P.Y P.Z P.T := rfl

open BatchCompressState.Insts in
/-- `BatchCompressState::from`: the doubling quantities of `P`. -/
private theorem from_spec (P : RistrettoPoint.«x86_64-tables») (hP : P.LimbsLt 52) :
    «CoreConvertFromSharedARistrettoPointx86_64-tables».from P
      ⦃ (st : BatchCompressState) => StateOf P st ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hP
  rw [from_eq]
  apply spec_mono (Backend.batchStateBody_spec Backend.U64
    Backend.U64.add_spec Backend.U64.sub_spec Backend.U64.mul_spec Backend.U64.square_spec
    Backend.U64.edwardsD_spec _ _ _ _ _ hX hY hZ hT)
  rintro _ ⟨e, f, g, h, eg, fh, rfl, h1, h2, h3, h4, h5, h6, b1, b2, b3, b4, b5, b6⟩
  unfold StateOf
  exact ⟨h1, h2, h3, h4, h5, h6, b1, b2, b3, b4, b5, b6⟩

private instance : Inhabited BatchCompressState :=
  ⟨⟨default, default, default, default, default, default⟩⟩

/-- `Forall₂` entry by entry. -/
private theorem forall₂_getElem! {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) (k : ℕ) (hk : k < l₁.length) :
    R l₁[k]! l₂[k]! := by
  obtain ⟨hlen, hR⟩ := List.forall₂_iff_get.mp h
  rw [getElem!_pos l₁ k hk, getElem!_pos l₂ k (hlen ▸ hk)]
  exact hR k hk (hlen ▸ hk)

/-- The collecting loop: one state per point. -/
private theorem states_loop_spec {I It : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«x86_64-tables» It)
    (it : It) (ps : List RistrettoPoint.«x86_64-tables»)
    (hit : pointsInst.iteratorInst.Yields it ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52) (out : alloc.vec.Vec BatchCompressState)
    (hlen : out.length + ps.length ≤ Usize.max) :
    double_and_compress_batch_loop0 pointsInst it out ⦃ (v : alloc.vec.Vec BatchCompressState) =>
      ∃ sts, v.val = out.val ++ sts ∧ List.Forall₂ StateOf ps sts ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold double_and_compress_batch_loop0 loop double_and_compress_batch_loop0.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | @cons it it' P ps' hnext _ ih =>
    unfold double_and_compress_batch_loop0 loop double_and_compress_batch_loop0.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with from_spec P (hps P List.mem_cons_self) as ⟨st, hst⟩
    step with alloc.vec.Vec.push_spec out st
      (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
    apply WP.spec_mono (ih (fun Q hQ => hps Q (List.mem_cons_of_mem _ hQ)) out1 (by
      rw [alloc.vec.Vec.length_of_val_eq_append hout1]
      simp only [List.length_cons] at hlen; omega))
    rintro r ⟨zs, hr, hzs⟩
    exact ⟨st :: zs, by rw [hr, hout1, List.append_assoc, List.singleton_append],
      List.Forall₂.cons hst hzs⟩

/-- `BatchCompressState::efgh`: the product `e g · f h`. -/
@[local step]
private theorem efgh_spec (st : BatchCompressState) (h1 : st.eg.LimbsLt 52)
    (h2 : st.fh.LimbsLt 52) :
    st.efgh ⦃ (r : FieldElement51) =>
      r.toField = st.eg.toField * st.fh.toField ∧ r.LimbsLt 52 ⦄ := by
  unfold BatchCompressState.efgh
  step as ⟨r, hr, hrb⟩
  exact ⟨toField_mul_of_mod hr, hrb⟩

/-- `states`: one state per point. -/
private theorem states_spec {I It : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«x86_64-tables» It)
    (it : It) (ps : List RistrettoPoint.«x86_64-tables»)
    (hit : pointsInst.iteratorInst.Yields it ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52) (hlen : ps.length ≤ Usize.max) :
    double_and_compress_batch_loop0 pointsInst it (alloc.vec.Vec.new _)
      ⦃ (v : alloc.vec.Vec BatchCompressState) =>
      List.Forall₂ StateOf ps v.val ⦄ := by
  apply spec_mono (states_loop_spec pointsInst it ps hit hps (alloc.vec.Vec.new _)
    (by simpa using hlen))
  rintro v ⟨zs, hv, hzs⟩
  rw [hv]
  simpa using hzs

end «RistrettoPointx86_64-tables».double_and_compress_batch

namespace «RistrettoPointi686-tables».double_and_compress_batch

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- The state of a point `P`: its doubling quantities as field elements, with their limb bounds. -/
private def StateOf (P : RistrettoPoint.«i686-tables») (st : BatchCompressState) : Prop :=
  st.e.toField = P.X.toField * (P.Y.toField + P.Y.toField) ∧
  st.f.toField = P.Z.toField ^ 2 + P.T.toField ^ 2 * d ∧
  st.g.toField = P.Y.toField ^ 2 + P.X.toField ^ 2 ∧
  st.h.toField = P.Z.toField ^ 2 - P.T.toField ^ 2 * d ∧
  st.eg.toField = st.e.toField * st.g.toField ∧ st.fh.toField = st.f.toField * st.h.toField ∧
  st.e.LimbsLt 27 ∧ st.f.LimbsLt 27 ∧ st.g.LimbsLt 27 ∧ st.h.LimbsLt 27 ∧ st.eg.LimbsLt 26 ∧
  st.fh.LimbsLt 26

private theorem from_eq (P : RistrettoPoint.«i686-tables») :
    BatchCompressState.Insts.«CoreConvertFromSharedARistrettoPointi686-tables».from P =
      Backend.batchStateBody Backend.U32
        (fun e f g h eg fh => (⟨e, f, g, h, eg, fh⟩ : BatchCompressState))
        P.X P.Y P.Z P.T := rfl

open BatchCompressState.Insts in
/-- `BatchCompressState::from`: the doubling quantities of `P`. -/
private theorem from_spec (P : RistrettoPoint.«i686-tables») (hP : P.LimbsLt 26) :
    «CoreConvertFromSharedARistrettoPointi686-tables».from P
      ⦃ (st : BatchCompressState) => StateOf P st ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hP
  rw [from_eq]
  apply spec_mono (Backend.batchStateBody_spec Backend.U32
    Backend.U32.add_spec Backend.U32.sub_spec Backend.U32.mul_spec Backend.U32.square_spec
    Backend.U32.edwardsD_spec _ _ _ _ _ hX hY hZ hT)
  rintro _ ⟨e, f, g, h, eg, fh, rfl, h1, h2, h3, h4, h5, h6, b1, b2, b3, b4, b5, b6⟩
  unfold StateOf
  exact ⟨h1, h2, h3, h4, h5, h6, b1, b2, b3, b4, b5, b6⟩

private instance : Inhabited BatchCompressState :=
  ⟨⟨default, default, default, default, default, default⟩⟩

/-- `Forall₂` entry by entry. -/
private theorem forall₂_getElem! {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) (k : ℕ) (hk : k < l₁.length) :
    R l₁[k]! l₂[k]! := by
  obtain ⟨hlen, hR⟩ := List.forall₂_iff_get.mp h
  rw [getElem!_pos l₁ k hk, getElem!_pos l₂ k (hlen ▸ hk)]
  exact hR k hk (hlen ▸ hk)

/-- The collecting loop: one state per point. -/
private theorem states_loop_spec {I It : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«i686-tables» It)
    (it : It) (ps : List RistrettoPoint.«i686-tables»)
    (hit : pointsInst.iteratorInst.Yields it ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26) (out : alloc.vec.Vec BatchCompressState)
    (hlen : out.length + ps.length ≤ Usize.max) :
    double_and_compress_batch_loop0 pointsInst it out ⦃ (v : alloc.vec.Vec BatchCompressState) =>
      ∃ sts, v.val = out.val ++ sts ∧ List.Forall₂ StateOf ps sts ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold double_and_compress_batch_loop0 loop double_and_compress_batch_loop0.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | @cons it it' P ps' hnext _ ih =>
    unfold double_and_compress_batch_loop0 loop double_and_compress_batch_loop0.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with from_spec P (hps P List.mem_cons_self) as ⟨st, hst⟩
    step with alloc.vec.Vec.push_spec out st
      (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
    apply WP.spec_mono (ih (fun Q hQ => hps Q (List.mem_cons_of_mem _ hQ)) out1 (by
      rw [alloc.vec.Vec.length_of_val_eq_append hout1]
      simp only [List.length_cons] at hlen; omega))
    rintro r ⟨zs, hr, hzs⟩
    exact ⟨st :: zs, by rw [hr, hout1, List.append_assoc, List.singleton_append],
      List.Forall₂.cons hst hzs⟩

/-- `BatchCompressState::efgh`: the product `e g · f h`. -/
@[local step]
private theorem efgh_spec (st : BatchCompressState) (h1 : st.eg.LimbsLt 26)
    (h2 : st.fh.LimbsLt 26) :
    st.efgh ⦃ (r : FieldElement2625) =>
      r.toField = st.eg.toField * st.fh.toField ∧ r.LimbsLt 26 ⦄ := by
  unfold BatchCompressState.efgh
  step as ⟨r, hr, hrb⟩
  exact ⟨toField_mul_of_mod hr, hrb⟩

/-- `states`: one state per point. -/
private theorem states_spec {I It : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«i686-tables» It)
    (it : It) (ps : List RistrettoPoint.«i686-tables»)
    (hit : pointsInst.iteratorInst.Yields it ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26) (hlen : ps.length ≤ Usize.max) :
    double_and_compress_batch_loop0 pointsInst it (alloc.vec.Vec.new _)
      ⦃ (v : alloc.vec.Vec BatchCompressState) =>
      List.Forall₂ StateOf ps v.val ⦄ := by
  apply spec_mono (states_loop_spec pointsInst it ps hit hps (alloc.vec.Vec.new _)
    (by simpa using hlen))
  rintro v ⟨zs, hv, hzs⟩
  rw [hv]
  simpa using hzs

end «RistrettoPointi686-tables».double_and_compress_batch

namespace «RistrettoPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

open double_and_compress_batch

open scoped Helpers.IndexStep in
/-- The first loop: the products `e g · f h` of the states. -/
private theorem loop0_spec (states : alloc.vec.Vec double_and_compress_batch.BatchCompressState)
    (hst : ∀ k < states.length, (states[k]!).eg.LimbsLt 52 ∧ (states[k]!).fh.LimbsLt 52)
    (invs : alloc.vec.Vec FieldElement51) (i : ℕ) (hi : i ≤ states.length)
    (hlen : invs.length = i)
    (hinvs : ∀ k < i, invs[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧
      (invs[k]!).LimbsLt 52) :
    double_and_compress_batch_loop1 { slice := states.deref, i } invs
      ⦃ (r : alloc.vec.Vec FieldElement51) =>
      r.length = states.length ∧ ∀ k < states.length,
        r[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧
          (r[k]!).LimbsLt 52 ⦄ := by
  unfold double_and_compress_batch_loop1
  apply loop.spec_decr_nat (measure := fun (it, _) => states.length - it.i)
    (inv := fun (it, z) => it.slice = states.deref ∧ it.i ≤ states.length ∧
      z.length = it.i ∧ ∀ k < it.i,
      z[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧
        (z[k]!).LimbsLt 52)
  · rintro ⟨it, z⟩ ⟨hs, hi', hl, hz⟩
    unfold double_and_compress_batch_loop1.body
    have hsval : it.slice.val = states.val := by rw [hs]; exact Slice.from_val _ _
    by_cases hlt : it.i < states.length
    · have hnext : core.slice.iter.IteratorSliceIter.next it
          ⦃ o it1 => o = some (states[it.i]!) ∧
            it1 = { slice := it.slice, i := it.i + 1 } ⦄ := by
        have h := Curve25519Dalek.EdwardsOps.sliceNextSome it.slice it.i
          (by simpa [hsval] using hlt)
        apply spec_mono h
        rintro ⟨o, it1⟩ ⟨ho, hit⟩
        refine ⟨?_, hit⟩
        rw [ho, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos states.val it.i hlt]
        congr 1
        have hslt : it.i < it.slice.val.length := by simpa [hsval] using hlt
        change it.slice.val[it.i] = states.val[it.i]
        simp only [hsval]
      step with hnext as ⟨o, it1, ho, hit1⟩
      subst ho hit1
      obtain ⟨h1, h2⟩ := hst it.i hlt
      step with efgh_spec _ h1 h2 as ⟨fe, hfe, hfeb⟩
      step as ⟨z1, hz1⟩
      refine ⟨hs, by omega, ?_, ?_, by omega⟩
      · rw [alloc.vec.Vec.length_of_val_eq_append hz1, hl]
      · rw [← hl]
        exact alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x =>
          x.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧ x.LimbsLt 52)
          hz1 (hl ▸ hz) (by rw [hl]; exact ⟨hfe, hfeb⟩)
    · have hnext : core.slice.iter.IteratorSliceIter.next it
          ⦃ o it1 => o = none ∧ it1 = it ⦄ := by
        have h := Curve25519Dalek.EdwardsOps.sliceNextNone it.slice it.i
          (by simpa [hsval] using Nat.le_of_not_gt hlt)
        simpa using h
      step with hnext as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have hin : it.i = states.length := by omega
      exact ⟨hl.trans hin, hin ▸ hz⟩
  · exact ⟨rfl, hi, hlen, hinvs⟩

set_option linter.hashCommand false in
#decompose double_and_compress_batch_loop2.body loop1_body_eq
  afterLets (branch 1 (letRange 2 23)) => compressState

/-- The encoding step of `double_and_compress_batch`'s second loop: the bytes of `2 P` from the
state of `P` and the inverse of `e g · f h`. -/
add_decl_doc compressState

private theorem compressState_eq (st : BatchCompressState) (inv : FieldElement51) :
    compressState st inv =
      Backend.compressStateBody Backend.U64 st.e st.f st.g st.h st.eg st.fh inv := rfl

/-- The encoding step of the second loop: from the state of `P` and the inverse of `e g · f h`,
the bytes of `2 P`. -/
private theorem compressState_spec (P : RistrettoPoint.«x86_64-tables») (hP : P.OnCurve)
    (st : BatchCompressState) (hst : StateOf P st) (inv : FieldElement51)
    (Inv : inv.toField = (st.eg.toField * st.fh.toField)⁻¹) (Invb : inv.LimbsLt 52) :
    compressState st inv ⦃ (bytes : CompressedRistretto) =>
      bytes.asNat = Ristretto.encodeRep (2 • P.toPoint) ⦄ := by
  obtain ⟨Se, Sf, Sg, Sh, Seg, Sfh, Seb, Sfb, Sgb, Shb, Segb, Sfhb⟩ := hst
  rw [edwards.EdwardsPoint.«x86_64-tables».onCurve_iff,
    edwards.EdwardsPoint.«x86_64-tables».toExtended_def] at hP
  rw [compressState_eq, edwards.EdwardsPoint.«x86_64-tables».toPoint_def,
    edwards.EdwardsPoint.«x86_64-tables».toExtended_def]
  exact Backend.compressStateBody_spec Backend.U64
    Backend.U64.sub_spec Backend.U64.mul_spec Backend.U64.neg_spec Backend.U64.sqrtM1_spec
    Backend.U64.invsqrtAMinusD_spec Backend.U64.is_negative_spec Backend.U64.conditional_assign_spec
    Backend.U64.conditional_negate_spec Backend.U64.to_bytes_spec _ _ _ _ _ _ _ hP Se Sf Sg Sh Seg
    Sfh Seb Sfb Sgb Shb Segb Sfhb Inv Invb


open scoped Helpers.IndexStep in
/-- The second loop: entry `k` encodes `2 P_k`, from the state and the inverse of `e g · f h`. -/
private theorem loop1_spec (states : alloc.vec.Vec double_and_compress_batch.BatchCompressState)
    (ps : List RistrettoPoint.«x86_64-tables») (hsts : List.Forall₂ StateOf ps states.val)
    (hon : ∀ P ∈ ps, P.OnCurve) (invs : alloc.vec.Vec FieldElement51)
    (hinvs : ∀ k < states.length, invs[k]!.toField =
      ((states[k]!).eg.toField * (states[k]!).fh.toField)⁻¹ ∧ (invs[k]!).LimbsLt 52)
    (hinvlen : invs.length = states.length)
    (out : alloc.vec.Vec CompressedRistretto) (i : Usize) (hi : i.val ≤ states.length)
    (hlen : out.length = i.val)
    (hout : ∀ k < i.val, out[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint)) :
    double_and_compress_batch_loop2 { start := i, «end» := states.len } states invs out
      ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = states.length ∧
        ∀ k < states.length, r[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint) ⦄ := by
  have hpslen : ps.length = states.length := by
    rw [hsts.length_eq]
  unfold double_and_compress_batch_loop2
  apply loop.spec_decr_nat (measure := fun (it, _) => states.length - it.start.val)
    (inv := fun (it, o) => it.end = states.len ∧ it.start.val ≤ states.length ∧
      o.length = it.start.val ∧ ∀ k < it.start.val,
      o[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint))
  · rintro ⟨it, o⟩ ⟨hend, hi', hl, ho⟩
    dsimp only
    rw [loop1_body_eq]
    by_cases hlt : it.start.val < states.length
    · have hlt' : it.start.val < it.end.val := by
        rw [hend, alloc.vec.Vec.len_val]; exact hlt
      step with core.iter.range.IteratorRange.next_Usize_some_spec it hlt'
        as ⟨opt, it1, hopt, hstart1, hend1⟩
      subst hopt
      step as ⟨st, hst⟩
      replace hst : st = states[it.start.val]! := by
        rw [hst, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      step as ⟨inv, hinv⟩
      replace hinv : inv = invs[it.start.val]! := by
        rw [hinv, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      obtain ⟨Inv, Invb⟩ := hinvs it.start.val hlt
      rw [← hst, ← hinv] at Inv
      rw [← hinv] at Invb
      rw [alloc.vec.Vec.getElem!_Nat_eq] at hst
      have hPmem : ps[it.start.val]! ∈ ps := by
        rw [getElem!_pos ps it.start.val (hpslen ▸ hlt)]
        exact List.getElem_mem _
      have hS := forall₂_getElem! hsts it.start.val (hpslen ▸ hlt)
      rw [← hst] at hS
      step with compressState_spec _ (hon _ hPmem) st hS inv Inv Invb as ⟨bytes, hbytes⟩
      step as ⟨o1, ho1⟩
      refine ⟨hend1.trans hend, by scalar_tac,
        by rw [alloc.vec.Vec.length_of_val_eq_append ho1, hl, hstart1], ?_, by scalar_tac⟩
      rw [hstart1, ← hl]
      refine alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x =>
        x.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint)) ho1 (hl ▸ ho) ?_
      rw [hl]
      exact hbytes
    · have hge : it.end.val ≤ it.start.val := by
        rw [hend, alloc.vec.Vec.len_val]; omega
      step with core.iter.range.IteratorRange.next_Usize_none_spec it hge
        as ⟨opt, it1, hopt, hit1⟩
      subst hopt
      simp only [WP.spec_ok]
      have hin : it.start.val = states.length := by omega
      exact ⟨hl.trans hin, hin ▸ ho⟩
  · exact ⟨rfl, hi, hlen, hout⟩

/-- `RistrettoPoint::double_and_compress_batch`: entry `i` is RFC 9496's encoding of `2 P_i` for
the points `P_i` the input yields; limbs `< 2^52`. -/
@[step]
theorem double_and_compress_batch_spec {I Clause0_IntoIter : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«x86_64-tables» Clause0_IntoIter)
    (points : I) (ps : List RistrettoPoint.«x86_64-tables»)
    (hpoints : pointsInst.Yields points ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve) (hlen : ps.length ≤ Usize.max) :
    double_and_compress_batch pointsInst points ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = ps.length ∧
        ∀ i < ps.length, r[i]!.asNat = Ristretto.encodeRep (2 • (ps[i]!).toPoint) ⦄ := by
  unfold double_and_compress_batch
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ps ⦄ := hpoints
  step with hpoints' as ⟨it, hit⟩
  step with states_spec pointsInst it ps hit (fun P hP => (hps P hP).1) hlen as ⟨states, hsts⟩
  have hpslen : ps.length = states.length := hsts.length_eq
  have hst : ∀ k < states.length, (states[k]!).eg.LimbsLt 52 ∧ (states[k]!).fh.LimbsLt 52 :=
    fun k hk => by
      have h := forall₂_getElem! hsts k (hpslen ▸ hk)
      rw [alloc.vec.Vec.getElem!_Nat_eq]
      exact ⟨h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩
  simp only [SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter,
    core.slice.Slice.iter, bind_ok]
  step with loop0_spec states hst (alloc.vec.Vec.with_capacity FieldElement51 states.len) 0
    (by simp) (by rfl) (fun k hk => absurd hk (by simp)) as ⟨invs1, hinvs1len, hinvs1⟩
  simp only [alloc.vec.Vec.index_mut, pure]
  have hsb : ∀ k < invs1.slice.length, (invs1.slice[k]!).LimbsLt 54 := fun k hk => by
    rw [alloc.vec.Vec.getElem!_slice]
    exact limbs_lt_of_le (by decide) (hinvs1 k (hinvs1len ▸ hk)).2
  step as ⟨s1, hs1len, hs1⟩
  have hslen : invs1.slice.length = states.length := hinvs1len
  have hinvs : ∀ k < states.length, ({ slice := s1 } : alloc.vec.Vec FieldElement51)[k]!.toField =
      ((states[k]!).eg.toField * (states[k]!).fh.toField)⁻¹ ∧
      (({ slice := s1 } : alloc.vec.Vec FieldElement51)[k]!).LimbsLt 52 := by
    intro k hk
    obtain ⟨h0, h1⟩ := hs1 k (hslen ▸ hk)
    obtain ⟨hv, hb⟩ := hinvs1 k hk
    rw [alloc.vec.Vec.getElem!_slice] at h0 h1
    rw [alloc.vec.Vec.getElem!_mk, ← hv]
    exact toField_inv_of_batch h0 h1 hb
  step with loop1_spec states ps hsts (fun P hP => (hps P hP).2) _ hinvs
    (by rw [alloc.vec.Vec.length]; exact hs1len.trans hslen)
    (alloc.vec.Vec.with_capacity CompressedRistretto states.len) 0#usize (by simp) (by rfl)
    (fun k hk => absurd hk (by simp)) as ⟨r, hrlen, hr⟩
  exact ⟨hrlen.trans hpslen.symm, fun k hk => hr k (hpslen ▸ hk)⟩

end «RistrettoPointx86_64-tables»

namespace «RistrettoPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

open double_and_compress_batch

open scoped Helpers.IndexStep in
/-- The first loop: the products `e g · f h` of the states. -/
private theorem loop0_spec (states : alloc.vec.Vec double_and_compress_batch.BatchCompressState)
    (hst : ∀ k < states.length, (states[k]!).eg.LimbsLt 26 ∧ (states[k]!).fh.LimbsLt 26)
    (invs : alloc.vec.Vec FieldElement2625) (i : ℕ) (hi : i ≤ states.length)
    (hlen : invs.length = i)
    (hinvs : ∀ k < i, invs[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧
      (invs[k]!).LimbsLt 26) :
    double_and_compress_batch_loop1 { slice := states.deref, i } invs
      ⦃ (r : alloc.vec.Vec FieldElement2625) =>
      r.length = states.length ∧ ∀ k < states.length,
        r[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧
          (r[k]!).LimbsLt 26 ⦄ := by
  unfold double_and_compress_batch_loop1
  apply loop.spec_decr_nat (measure := fun (it, _) => states.length - it.i)
    (inv := fun (it, z) => it.slice = states.deref ∧ it.i ≤ states.length ∧
      z.length = it.i ∧ ∀ k < it.i,
      z[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧
        (z[k]!).LimbsLt 26)
  · rintro ⟨it, z⟩ ⟨hs, hi', hl, hz⟩
    unfold double_and_compress_batch_loop1.body
    have hsval : it.slice.val = states.val := by rw [hs]; exact Slice.from_val _ _
    by_cases hlt : it.i < states.length
    · have hnext : core.slice.iter.IteratorSliceIter.next it
          ⦃ o it1 => o = some (states[it.i]!) ∧
            it1 = { slice := it.slice, i := it.i + 1 } ⦄ := by
        have h := Curve25519Dalek.EdwardsOps.sliceNextSome it.slice it.i
          (by simpa [hsval] using hlt)
        apply spec_mono h
        rintro ⟨o, it1⟩ ⟨ho, hit⟩
        refine ⟨?_, hit⟩
        rw [ho, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos states.val it.i hlt]
        congr 1
        have hslt : it.i < it.slice.val.length := by simpa [hsval] using hlt
        change it.slice.val[it.i] = states.val[it.i]
        simp only [hsval]
      step with hnext as ⟨o, it1, ho, hit1⟩
      subst ho hit1
      obtain ⟨h1, h2⟩ := hst it.i hlt
      step with efgh_spec _ h1 h2 as ⟨fe, hfe, hfeb⟩
      step as ⟨z1, hz1⟩
      refine ⟨hs, by omega, ?_, ?_, by omega⟩
      · rw [alloc.vec.Vec.length_of_val_eq_append hz1, hl]
      · rw [← hl]
        exact alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x =>
          x.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧ x.LimbsLt 26)
          hz1 (hl ▸ hz) (by rw [hl]; exact ⟨hfe, hfeb⟩)
    · have hnext : core.slice.iter.IteratorSliceIter.next it
          ⦃ o it1 => o = none ∧ it1 = it ⦄ := by
        have h := Curve25519Dalek.EdwardsOps.sliceNextNone it.slice it.i
          (by simpa [hsval] using Nat.le_of_not_gt hlt)
        simpa using h
      step with hnext as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have hin : it.i = states.length := by omega
      exact ⟨hl.trans hin, hin ▸ hz⟩
  · exact ⟨rfl, hi, hlen, hinvs⟩

set_option linter.hashCommand false in
#decompose double_and_compress_batch_loop2.body loop1_body_eq
  afterLets (branch 1 (letRange 2 23)) => compressState

/-- The encoding step of `double_and_compress_batch`'s second loop: the bytes of `2 P` from the
state of `P` and the inverse of `e g · f h`. -/
add_decl_doc compressState

private theorem compressState_eq (st : BatchCompressState) (inv : FieldElement2625) :
    compressState st inv =
      Backend.compressStateBody Backend.U32 st.e st.f st.g st.h st.eg st.fh inv := rfl

/-- The encoding step of the second loop: from the state of `P` and the inverse of `e g · f h`,
the bytes of `2 P`. -/
private theorem compressState_spec (P : RistrettoPoint.«i686-tables») (hP : P.OnCurve)
    (st : BatchCompressState) (hst : StateOf P st) (inv : FieldElement2625)
    (Inv : inv.toField = (st.eg.toField * st.fh.toField)⁻¹) (Invb : inv.LimbsLt 26) :
    compressState st inv ⦃ (bytes : CompressedRistretto) =>
      bytes.asNat = Ristretto.encodeRep (2 • P.toPoint) ⦄ := by
  obtain ⟨Se, Sf, Sg, Sh, Seg, Sfh, Seb, Sfb, Sgb, Shb, Segb, Sfhb⟩ := hst
  rw [edwards.EdwardsPoint.«i686-tables».onCurve_iff,
    edwards.EdwardsPoint.«i686-tables».toExtended_def] at hP
  rw [compressState_eq, edwards.EdwardsPoint.«i686-tables».toPoint_def,
    edwards.EdwardsPoint.«i686-tables».toExtended_def]
  exact Backend.compressStateBody_spec Backend.U32
    Backend.U32.sub_spec Backend.U32.mul_spec Backend.U32.neg_spec Backend.U32.sqrtM1_spec
    Backend.U32.invsqrtAMinusD_spec Backend.U32.is_negative_spec Backend.U32.conditional_assign_spec
    Backend.U32.conditional_negate_spec Backend.U32.to_bytes_spec _ _ _ _ _ _ _ hP Se Sf Sg Sh Seg
    Sfh Seb Sfb Sgb Shb Segb Sfhb Inv Invb


open scoped Helpers.IndexStep in
/-- The second loop: entry `k` encodes `2 P_k`, from the state and the inverse of `e g · f h`. -/
private theorem loop1_spec (states : alloc.vec.Vec double_and_compress_batch.BatchCompressState)
    (ps : List RistrettoPoint.«i686-tables») (hsts : List.Forall₂ StateOf ps states.val)
    (hon : ∀ P ∈ ps, P.OnCurve) (invs : alloc.vec.Vec FieldElement2625)
    (hinvs : ∀ k < states.length, invs[k]!.toField =
      ((states[k]!).eg.toField * (states[k]!).fh.toField)⁻¹ ∧ (invs[k]!).LimbsLt 26)
    (hinvlen : invs.length = states.length)
    (out : alloc.vec.Vec CompressedRistretto) (i : Usize) (hi : i.val ≤ states.length)
    (hlen : out.length = i.val)
    (hout : ∀ k < i.val, out[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint)) :
    double_and_compress_batch_loop2 { start := i, «end» := states.len } states invs out
      ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = states.length ∧
        ∀ k < states.length, r[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint) ⦄ := by
  have hpslen : ps.length = states.length := by
    rw [hsts.length_eq]
  unfold double_and_compress_batch_loop2
  apply loop.spec_decr_nat (measure := fun (it, _) => states.length - it.start.val)
    (inv := fun (it, o) => it.end = states.len ∧ it.start.val ≤ states.length ∧
      o.length = it.start.val ∧ ∀ k < it.start.val,
      o[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint))
  · rintro ⟨it, o⟩ ⟨hend, hi', hl, ho⟩
    dsimp only
    rw [loop1_body_eq]
    by_cases hlt : it.start.val < states.length
    · have hlt' : it.start.val < it.end.val := by
        rw [hend, alloc.vec.Vec.len_val]; exact hlt
      step with core.iter.range.IteratorRange.next_Usize_some_spec it hlt'
        as ⟨opt, it1, hopt, hstart1, hend1⟩
      subst hopt
      step as ⟨st, hst⟩
      replace hst : st = states[it.start.val]! := by
        rw [hst, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      step as ⟨inv, hinv⟩
      replace hinv : inv = invs[it.start.val]! := by
        rw [hinv, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      obtain ⟨Inv, Invb⟩ := hinvs it.start.val hlt
      rw [← hst, ← hinv] at Inv
      rw [← hinv] at Invb
      rw [alloc.vec.Vec.getElem!_Nat_eq] at hst
      have hPmem : ps[it.start.val]! ∈ ps := by
        rw [getElem!_pos ps it.start.val (hpslen ▸ hlt)]
        exact List.getElem_mem _
      have hS := forall₂_getElem! hsts it.start.val (hpslen ▸ hlt)
      rw [← hst] at hS
      step with compressState_spec _ (hon _ hPmem) st hS inv Inv Invb as ⟨bytes, hbytes⟩
      step as ⟨o1, ho1⟩
      refine ⟨hend1.trans hend, by scalar_tac,
        by rw [alloc.vec.Vec.length_of_val_eq_append ho1, hl, hstart1], ?_, by scalar_tac⟩
      rw [hstart1, ← hl]
      refine alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x =>
        x.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint)) ho1 (hl ▸ ho) ?_
      rw [hl]
      exact hbytes
    · have hge : it.end.val ≤ it.start.val := by
        rw [hend, alloc.vec.Vec.len_val]; omega
      step with core.iter.range.IteratorRange.next_Usize_none_spec it hge
        as ⟨opt, it1, hopt, hit1⟩
      subst hopt
      simp only [WP.spec_ok]
      have hin : it.start.val = states.length := by omega
      exact ⟨hl.trans hin, hin ▸ ho⟩
  · exact ⟨rfl, hi, hlen, hout⟩

/-- `RistrettoPoint::double_and_compress_batch`: entry `i` is RFC 9496's encoding of `2 P_i` for
the points `P_i` the input yields; limbs `< 2^26`. -/
@[step]
theorem double_and_compress_batch_spec {I Clause0_IntoIter : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«i686-tables» Clause0_IntoIter)
    (points : I) (ps : List RistrettoPoint.«i686-tables»)
    (hpoints : pointsInst.Yields points ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26 ∧ P.OnCurve) (hlen : ps.length ≤ Usize.max) :
    double_and_compress_batch pointsInst points ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = ps.length ∧
        ∀ i < ps.length, r[i]!.asNat = Ristretto.encodeRep (2 • (ps[i]!).toPoint) ⦄ := by
  unfold double_and_compress_batch
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ps ⦄ := hpoints
  step with hpoints' as ⟨it, hit⟩
  step with states_spec pointsInst it ps hit (fun P hP => (hps P hP).1) hlen as ⟨states, hsts⟩
  have hpslen : ps.length = states.length := hsts.length_eq
  have hst : ∀ k < states.length, (states[k]!).eg.LimbsLt 26 ∧ (states[k]!).fh.LimbsLt 26 :=
    fun k hk => by
      have h := forall₂_getElem! hsts k (hpslen ▸ hk)
      rw [alloc.vec.Vec.getElem!_Nat_eq]
      exact ⟨h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩
  simp only [SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter,
    core.slice.Slice.iter, bind_ok]
  step with loop0_spec states hst (alloc.vec.Vec.with_capacity FieldElement2625 states.len) 0
    (by simp) (by rfl) (fun k hk => absurd hk (by simp)) as ⟨invs1, hinvs1len, hinvs1⟩
  simp only [alloc.vec.Vec.index_mut, pure]
  have hsb : ∀ k < invs1.slice.length, (invs1.slice[k]!).LimbsLt 27 := fun k hk => by
    rw [alloc.vec.Vec.getElem!_slice]
    exact limbs_lt_of_le (by decide) (hinvs1 k (hinvs1len ▸ hk)).2
  step as ⟨s1, hs1len, hs1⟩
  have hslen : invs1.slice.length = states.length := hinvs1len
  have hinvs : ∀ k < states.length, ({ slice := s1 } : alloc.vec.Vec FieldElement2625)[k]!.toField =
      ((states[k]!).eg.toField * (states[k]!).fh.toField)⁻¹ ∧
      (({ slice := s1 } : alloc.vec.Vec FieldElement2625)[k]!).LimbsLt 26 := by
    intro k hk
    obtain ⟨h0, h1⟩ := hs1 k (hslen ▸ hk)
    obtain ⟨hv, hb⟩ := hinvs1 k hk
    rw [alloc.vec.Vec.getElem!_slice] at h0 h1
    rw [alloc.vec.Vec.getElem!_mk, ← hv]
    exact toField_inv_of_batch h0 h1 hb
  step with loop1_spec states ps hsts (fun P hP => (hps P hP).2) _ hinvs
    (by rw [alloc.vec.Vec.length]; exact hs1len.trans hslen)
    (alloc.vec.Vec.with_capacity CompressedRistretto states.len) 0#usize (by simp) (by rfl)
    (fun k hk => absurd hk (by simp)) as ⟨r, hrlen, hr⟩
  exact ⟨hrlen.trans hpslen.symm, fun k hk => hr k (hpslen ▸ hk)⟩

end «RistrettoPointi686-tables»

namespace «RistrettoPointx86_64-no-tables».double_and_compress_batch

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- The state of a point `P`: its doubling quantities as field elements, with their limb bounds. -/
private def StateOf (P : RistrettoPoint.«x86_64-no-tables») (st : BatchCompressState) : Prop :=
  st.e.toField = P.X.toField * (P.Y.toField + P.Y.toField) ∧
  st.f.toField = P.Z.toField ^ 2 + P.T.toField ^ 2 * d ∧
  st.g.toField = P.Y.toField ^ 2 + P.X.toField ^ 2 ∧
  st.h.toField = P.Z.toField ^ 2 - P.T.toField ^ 2 * d ∧
  st.eg.toField = st.e.toField * st.g.toField ∧ st.fh.toField = st.f.toField * st.h.toField ∧
  st.e.LimbsLt 54 ∧ st.f.LimbsLt 54 ∧ st.g.LimbsLt 54 ∧ st.h.LimbsLt 54 ∧ st.eg.LimbsLt 52 ∧
  st.fh.LimbsLt 52

private theorem from_eq (P : RistrettoPoint.«x86_64-no-tables») :
    BatchCompressState.Insts.«CoreConvertFromSharedARistrettoPointx86_64-no-tables».from P =
      Backend.batchStateBody Backend.U64
        (fun e f g h eg fh => (⟨e, f, g, h, eg, fh⟩ : BatchCompressState))
        P.X P.Y P.Z P.T := rfl

open BatchCompressState.Insts in
/-- `BatchCompressState::from`: the doubling quantities of `P`. -/
private theorem from_spec (P : RistrettoPoint.«x86_64-no-tables») (hP : P.LimbsLt 52) :
    «CoreConvertFromSharedARistrettoPointx86_64-no-tables».from P
      ⦃ (st : BatchCompressState) => StateOf P st ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hP
  rw [from_eq]
  apply spec_mono (Backend.batchStateBody_spec Backend.U64
    Backend.U64.add_spec Backend.U64.sub_spec Backend.U64.mul_spec Backend.U64.square_spec
    Backend.U64.edwardsD_spec _ _ _ _ _ hX hY hZ hT)
  rintro _ ⟨e, f, g, h, eg, fh, rfl, h1, h2, h3, h4, h5, h6, b1, b2, b3, b4, b5, b6⟩
  unfold StateOf
  exact ⟨h1, h2, h3, h4, h5, h6, b1, b2, b3, b4, b5, b6⟩

private instance : Inhabited BatchCompressState :=
  ⟨⟨default, default, default, default, default, default⟩⟩

/-- `Forall₂` entry by entry. -/
private theorem forall₂_getElem! {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) (k : ℕ) (hk : k < l₁.length) :
    R l₁[k]! l₂[k]! := by
  obtain ⟨hlen, hR⟩ := List.forall₂_iff_get.mp h
  rw [getElem!_pos l₁ k hk, getElem!_pos l₂ k (hlen ▸ hk)]
  exact hR k hk (hlen ▸ hk)

/-- The collecting loop: one state per point. -/
private theorem states_loop_spec {I It : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«x86_64-no-tables» It)
    (it : It) (ps : List RistrettoPoint.«x86_64-no-tables»)
    (hit : pointsInst.iteratorInst.Yields it ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52) (out : alloc.vec.Vec BatchCompressState)
    (hlen : out.length + ps.length ≤ Usize.max) :
    double_and_compress_batch_loop0 pointsInst it out ⦃ (v : alloc.vec.Vec BatchCompressState) =>
      ∃ sts, v.val = out.val ++ sts ∧ List.Forall₂ StateOf ps sts ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold double_and_compress_batch_loop0 loop double_and_compress_batch_loop0.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | @cons it it' P ps' hnext _ ih =>
    unfold double_and_compress_batch_loop0 loop double_and_compress_batch_loop0.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with from_spec P (hps P List.mem_cons_self) as ⟨st, hst⟩
    step with alloc.vec.Vec.push_spec out st
      (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
    apply WP.spec_mono (ih (fun Q hQ => hps Q (List.mem_cons_of_mem _ hQ)) out1 (by
      rw [alloc.vec.Vec.length_of_val_eq_append hout1]
      simp only [List.length_cons] at hlen; omega))
    rintro r ⟨zs, hr, hzs⟩
    exact ⟨st :: zs, by rw [hr, hout1, List.append_assoc, List.singleton_append],
      List.Forall₂.cons hst hzs⟩

/-- `BatchCompressState::efgh`: the product `e g · f h`. -/
@[local step]
private theorem efgh_spec (st : BatchCompressState) (h1 : st.eg.LimbsLt 52)
    (h2 : st.fh.LimbsLt 52) :
    st.efgh ⦃ (r : FieldElement51) =>
      r.toField = st.eg.toField * st.fh.toField ∧ r.LimbsLt 52 ⦄ := by
  unfold BatchCompressState.efgh
  step as ⟨r, hr, hrb⟩
  exact ⟨toField_mul_of_mod hr, hrb⟩

/-- `states`: one state per point. -/
private theorem states_spec {I It : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«x86_64-no-tables» It)
    (it : It) (ps : List RistrettoPoint.«x86_64-no-tables»)
    (hit : pointsInst.iteratorInst.Yields it ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52) (hlen : ps.length ≤ Usize.max) :
    double_and_compress_batch_loop0 pointsInst it (alloc.vec.Vec.new _)
      ⦃ (v : alloc.vec.Vec BatchCompressState) =>
      List.Forall₂ StateOf ps v.val ⦄ := by
  apply spec_mono (states_loop_spec pointsInst it ps hit hps (alloc.vec.Vec.new _)
    (by simpa using hlen))
  rintro v ⟨zs, hv, hzs⟩
  rw [hv]
  simpa using hzs

end «RistrettoPointx86_64-no-tables».double_and_compress_batch

namespace «RistrettoPointi686-no-tables».double_and_compress_batch

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- The state of a point `P`: its doubling quantities as field elements, with their limb bounds. -/
private def StateOf (P : RistrettoPoint.«i686-no-tables») (st : BatchCompressState) : Prop :=
  st.e.toField = P.X.toField * (P.Y.toField + P.Y.toField) ∧
  st.f.toField = P.Z.toField ^ 2 + P.T.toField ^ 2 * d ∧
  st.g.toField = P.Y.toField ^ 2 + P.X.toField ^ 2 ∧
  st.h.toField = P.Z.toField ^ 2 - P.T.toField ^ 2 * d ∧
  st.eg.toField = st.e.toField * st.g.toField ∧ st.fh.toField = st.f.toField * st.h.toField ∧
  st.e.LimbsLt 27 ∧ st.f.LimbsLt 27 ∧ st.g.LimbsLt 27 ∧ st.h.LimbsLt 27 ∧ st.eg.LimbsLt 26 ∧
  st.fh.LimbsLt 26

private theorem from_eq (P : RistrettoPoint.«i686-no-tables») :
    BatchCompressState.Insts.«CoreConvertFromSharedARistrettoPointi686-no-tables».from P =
      Backend.batchStateBody Backend.U32
        (fun e f g h eg fh => (⟨e, f, g, h, eg, fh⟩ : BatchCompressState))
        P.X P.Y P.Z P.T := rfl

open BatchCompressState.Insts in
/-- `BatchCompressState::from`: the doubling quantities of `P`. -/
private theorem from_spec (P : RistrettoPoint.«i686-no-tables») (hP : P.LimbsLt 26) :
    «CoreConvertFromSharedARistrettoPointi686-no-tables».from P
      ⦃ (st : BatchCompressState) => StateOf P st ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hP
  rw [from_eq]
  apply spec_mono (Backend.batchStateBody_spec Backend.U32
    Backend.U32.add_spec Backend.U32.sub_spec Backend.U32.mul_spec Backend.U32.square_spec
    Backend.U32.edwardsD_spec _ _ _ _ _ hX hY hZ hT)
  rintro _ ⟨e, f, g, h, eg, fh, rfl, h1, h2, h3, h4, h5, h6, b1, b2, b3, b4, b5, b6⟩
  unfold StateOf
  exact ⟨h1, h2, h3, h4, h5, h6, b1, b2, b3, b4, b5, b6⟩

private instance : Inhabited BatchCompressState :=
  ⟨⟨default, default, default, default, default, default⟩⟩

/-- `Forall₂` entry by entry. -/
private theorem forall₂_getElem! {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) (k : ℕ) (hk : k < l₁.length) :
    R l₁[k]! l₂[k]! := by
  obtain ⟨hlen, hR⟩ := List.forall₂_iff_get.mp h
  rw [getElem!_pos l₁ k hk, getElem!_pos l₂ k (hlen ▸ hk)]
  exact hR k hk (hlen ▸ hk)

/-- The collecting loop: one state per point. -/
private theorem states_loop_spec {I It : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«i686-no-tables» It)
    (it : It) (ps : List RistrettoPoint.«i686-no-tables»)
    (hit : pointsInst.iteratorInst.Yields it ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26) (out : alloc.vec.Vec BatchCompressState)
    (hlen : out.length + ps.length ≤ Usize.max) :
    double_and_compress_batch_loop0 pointsInst it out ⦃ (v : alloc.vec.Vec BatchCompressState) =>
      ∃ sts, v.val = out.val ++ sts ∧ List.Forall₂ StateOf ps sts ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold double_and_compress_batch_loop0 loop double_and_compress_batch_loop0.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | @cons it it' P ps' hnext _ ih =>
    unfold double_and_compress_batch_loop0 loop double_and_compress_batch_loop0.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with from_spec P (hps P List.mem_cons_self) as ⟨st, hst⟩
    step with alloc.vec.Vec.push_spec out st
      (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
    apply WP.spec_mono (ih (fun Q hQ => hps Q (List.mem_cons_of_mem _ hQ)) out1 (by
      rw [alloc.vec.Vec.length_of_val_eq_append hout1]
      simp only [List.length_cons] at hlen; omega))
    rintro r ⟨zs, hr, hzs⟩
    exact ⟨st :: zs, by rw [hr, hout1, List.append_assoc, List.singleton_append],
      List.Forall₂.cons hst hzs⟩

/-- `BatchCompressState::efgh`: the product `e g · f h`. -/
@[local step]
private theorem efgh_spec (st : BatchCompressState) (h1 : st.eg.LimbsLt 26)
    (h2 : st.fh.LimbsLt 26) :
    st.efgh ⦃ (r : FieldElement2625) =>
      r.toField = st.eg.toField * st.fh.toField ∧ r.LimbsLt 26 ⦄ := by
  unfold BatchCompressState.efgh
  step as ⟨r, hr, hrb⟩
  exact ⟨toField_mul_of_mod hr, hrb⟩

/-- `states`: one state per point. -/
private theorem states_spec {I It : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«i686-no-tables» It)
    (it : It) (ps : List RistrettoPoint.«i686-no-tables»)
    (hit : pointsInst.iteratorInst.Yields it ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26) (hlen : ps.length ≤ Usize.max) :
    double_and_compress_batch_loop0 pointsInst it (alloc.vec.Vec.new _)
      ⦃ (v : alloc.vec.Vec BatchCompressState) =>
      List.Forall₂ StateOf ps v.val ⦄ := by
  apply spec_mono (states_loop_spec pointsInst it ps hit hps (alloc.vec.Vec.new _)
    (by simpa using hlen))
  rintro v ⟨zs, hv, hzs⟩
  rw [hv]
  simpa using hzs

end «RistrettoPointi686-no-tables».double_and_compress_batch

namespace «RistrettoPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

open double_and_compress_batch

open scoped Helpers.IndexStep in
/-- The first loop: the products `e g · f h` of the states. -/
private theorem loop0_spec (states : alloc.vec.Vec double_and_compress_batch.BatchCompressState)
    (hst : ∀ k < states.length, (states[k]!).eg.LimbsLt 52 ∧ (states[k]!).fh.LimbsLt 52)
    (invs : alloc.vec.Vec FieldElement51) (i : ℕ) (hi : i ≤ states.length)
    (hlen : invs.length = i)
    (hinvs : ∀ k < i, invs[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧
      (invs[k]!).LimbsLt 52) :
    double_and_compress_batch_loop1 { slice := states.deref, i } invs
      ⦃ (r : alloc.vec.Vec FieldElement51) =>
      r.length = states.length ∧ ∀ k < states.length,
        r[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧
          (r[k]!).LimbsLt 52 ⦄ := by
  unfold double_and_compress_batch_loop1
  apply loop.spec_decr_nat (measure := fun (it, _) => states.length - it.i)
    (inv := fun (it, z) => it.slice = states.deref ∧ it.i ≤ states.length ∧
      z.length = it.i ∧ ∀ k < it.i,
      z[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧
        (z[k]!).LimbsLt 52)
  · rintro ⟨it, z⟩ ⟨hs, hi', hl, hz⟩
    unfold double_and_compress_batch_loop1.body
    have hsval : it.slice.val = states.val := by rw [hs]; exact Slice.from_val _ _
    by_cases hlt : it.i < states.length
    · have hnext : core.slice.iter.IteratorSliceIter.next it
          ⦃ o it1 => o = some (states[it.i]!) ∧
            it1 = { slice := it.slice, i := it.i + 1 } ⦄ := by
        have h := Curve25519Dalek.EdwardsOps.sliceNextSome it.slice it.i
          (by simpa [hsval] using hlt)
        apply spec_mono h
        rintro ⟨o, it1⟩ ⟨ho, hit⟩
        refine ⟨?_, hit⟩
        rw [ho, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos states.val it.i hlt]
        congr 1
        have hslt : it.i < it.slice.val.length := by simpa [hsval] using hlt
        change it.slice.val[it.i] = states.val[it.i]
        simp only [hsval]
      step with hnext as ⟨o, it1, ho, hit1⟩
      subst ho hit1
      obtain ⟨h1, h2⟩ := hst it.i hlt
      step with efgh_spec _ h1 h2 as ⟨fe, hfe, hfeb⟩
      step as ⟨z1, hz1⟩
      refine ⟨hs, by omega, ?_, ?_, by omega⟩
      · rw [alloc.vec.Vec.length_of_val_eq_append hz1, hl]
      · rw [← hl]
        exact alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x =>
          x.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧ x.LimbsLt 52)
          hz1 (hl ▸ hz) (by rw [hl]; exact ⟨hfe, hfeb⟩)
    · have hnext : core.slice.iter.IteratorSliceIter.next it
          ⦃ o it1 => o = none ∧ it1 = it ⦄ := by
        have h := Curve25519Dalek.EdwardsOps.sliceNextNone it.slice it.i
          (by simpa [hsval] using Nat.le_of_not_gt hlt)
        simpa using h
      step with hnext as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have hin : it.i = states.length := by omega
      exact ⟨hl.trans hin, hin ▸ hz⟩
  · exact ⟨rfl, hi, hlen, hinvs⟩

set_option linter.hashCommand false in
#decompose double_and_compress_batch_loop2.body loop1_body_eq
  afterLets (branch 1 (letRange 2 23)) => compressState

/-- The encoding step of `double_and_compress_batch`'s second loop: the bytes of `2 P` from the
state of `P` and the inverse of `e g · f h`. -/
add_decl_doc compressState

private theorem compressState_eq (st : BatchCompressState) (inv : FieldElement51) :
    compressState st inv =
      Backend.compressStateBody Backend.U64 st.e st.f st.g st.h st.eg st.fh inv := rfl

/-- The encoding step of the second loop: from the state of `P` and the inverse of `e g · f h`,
the bytes of `2 P`. -/
private theorem compressState_spec (P : RistrettoPoint.«x86_64-no-tables») (hP : P.OnCurve)
    (st : BatchCompressState) (hst : StateOf P st) (inv : FieldElement51)
    (Inv : inv.toField = (st.eg.toField * st.fh.toField)⁻¹) (Invb : inv.LimbsLt 52) :
    compressState st inv ⦃ (bytes : CompressedRistretto) =>
      bytes.asNat = Ristretto.encodeRep (2 • P.toPoint) ⦄ := by
  obtain ⟨Se, Sf, Sg, Sh, Seg, Sfh, Seb, Sfb, Sgb, Shb, Segb, Sfhb⟩ := hst
  rw [edwards.EdwardsPoint.«x86_64-no-tables».onCurve_iff,
    edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def] at hP
  rw [compressState_eq, edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def,
    edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def]
  exact Backend.compressStateBody_spec Backend.U64
    Backend.U64.sub_spec Backend.U64.mul_spec Backend.U64.neg_spec Backend.U64.sqrtM1_spec
    Backend.U64.invsqrtAMinusD_spec Backend.U64.is_negative_spec Backend.U64.conditional_assign_spec
    Backend.U64.conditional_negate_spec Backend.U64.to_bytes_spec _ _ _ _ _ _ _ hP Se Sf Sg Sh Seg
    Sfh Seb Sfb Sgb Shb Segb Sfhb Inv Invb


open scoped Helpers.IndexStep in
/-- The second loop: entry `k` encodes `2 P_k`, from the state and the inverse of `e g · f h`. -/
private theorem loop1_spec (states : alloc.vec.Vec double_and_compress_batch.BatchCompressState)
    (ps : List RistrettoPoint.«x86_64-no-tables») (hsts : List.Forall₂ StateOf ps states.val)
    (hon : ∀ P ∈ ps, P.OnCurve) (invs : alloc.vec.Vec FieldElement51)
    (hinvs : ∀ k < states.length, invs[k]!.toField =
      ((states[k]!).eg.toField * (states[k]!).fh.toField)⁻¹ ∧ (invs[k]!).LimbsLt 52)
    (hinvlen : invs.length = states.length)
    (out : alloc.vec.Vec CompressedRistretto) (i : Usize) (hi : i.val ≤ states.length)
    (hlen : out.length = i.val)
    (hout : ∀ k < i.val, out[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint)) :
    double_and_compress_batch_loop2 { start := i, «end» := states.len } states invs out
      ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = states.length ∧
        ∀ k < states.length, r[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint) ⦄ := by
  have hpslen : ps.length = states.length := by
    rw [hsts.length_eq]
  unfold double_and_compress_batch_loop2
  apply loop.spec_decr_nat (measure := fun (it, _) => states.length - it.start.val)
    (inv := fun (it, o) => it.end = states.len ∧ it.start.val ≤ states.length ∧
      o.length = it.start.val ∧ ∀ k < it.start.val,
      o[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint))
  · rintro ⟨it, o⟩ ⟨hend, hi', hl, ho⟩
    dsimp only
    rw [loop1_body_eq]
    by_cases hlt : it.start.val < states.length
    · have hlt' : it.start.val < it.end.val := by
        rw [hend, alloc.vec.Vec.len_val]; exact hlt
      step with core.iter.range.IteratorRange.next_Usize_some_spec it hlt'
        as ⟨opt, it1, hopt, hstart1, hend1⟩
      subst hopt
      step as ⟨st, hst⟩
      replace hst : st = states[it.start.val]! := by
        rw [hst, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      step as ⟨inv, hinv⟩
      replace hinv : inv = invs[it.start.val]! := by
        rw [hinv, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      obtain ⟨Inv, Invb⟩ := hinvs it.start.val hlt
      rw [← hst, ← hinv] at Inv
      rw [← hinv] at Invb
      rw [alloc.vec.Vec.getElem!_Nat_eq] at hst
      have hPmem : ps[it.start.val]! ∈ ps := by
        rw [getElem!_pos ps it.start.val (hpslen ▸ hlt)]
        exact List.getElem_mem _
      have hS := forall₂_getElem! hsts it.start.val (hpslen ▸ hlt)
      rw [← hst] at hS
      step with compressState_spec _ (hon _ hPmem) st hS inv Inv Invb as ⟨bytes, hbytes⟩
      step as ⟨o1, ho1⟩
      refine ⟨hend1.trans hend, by scalar_tac,
        by rw [alloc.vec.Vec.length_of_val_eq_append ho1, hl, hstart1], ?_, by scalar_tac⟩
      rw [hstart1, ← hl]
      refine alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x =>
        x.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint)) ho1 (hl ▸ ho) ?_
      rw [hl]
      exact hbytes
    · have hge : it.end.val ≤ it.start.val := by
        rw [hend, alloc.vec.Vec.len_val]; omega
      step with core.iter.range.IteratorRange.next_Usize_none_spec it hge
        as ⟨opt, it1, hopt, hit1⟩
      subst hopt
      simp only [WP.spec_ok]
      have hin : it.start.val = states.length := by omega
      exact ⟨hl.trans hin, hin ▸ ho⟩
  · exact ⟨rfl, hi, hlen, hout⟩

/-- `RistrettoPoint::double_and_compress_batch`: entry `i` is RFC 9496's encoding of `2 P_i` for
the points `P_i` the input yields; limbs `< 2^52`. -/
@[step]
theorem double_and_compress_batch_spec {I Clause0_IntoIter : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«x86_64-no-tables» Clause0_IntoIter)
    (points : I) (ps : List RistrettoPoint.«x86_64-no-tables»)
    (hpoints : pointsInst.Yields points ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve) (hlen : ps.length ≤ Usize.max) :
    double_and_compress_batch pointsInst points ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = ps.length ∧
        ∀ i < ps.length, r[i]!.asNat = Ristretto.encodeRep (2 • (ps[i]!).toPoint) ⦄ := by
  unfold double_and_compress_batch
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ps ⦄ := hpoints
  step with hpoints' as ⟨it, hit⟩
  step with states_spec pointsInst it ps hit (fun P hP => (hps P hP).1) hlen as ⟨states, hsts⟩
  have hpslen : ps.length = states.length := hsts.length_eq
  have hst : ∀ k < states.length, (states[k]!).eg.LimbsLt 52 ∧ (states[k]!).fh.LimbsLt 52 :=
    fun k hk => by
      have h := forall₂_getElem! hsts k (hpslen ▸ hk)
      rw [alloc.vec.Vec.getElem!_Nat_eq]
      exact ⟨h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩
  simp only [SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter,
    core.slice.Slice.iter, bind_ok]
  step with loop0_spec states hst (alloc.vec.Vec.with_capacity FieldElement51 states.len) 0
    (by simp) (by rfl) (fun k hk => absurd hk (by simp)) as ⟨invs1, hinvs1len, hinvs1⟩
  simp only [alloc.vec.Vec.index_mut, pure]
  have hsb : ∀ k < invs1.slice.length, (invs1.slice[k]!).LimbsLt 54 := fun k hk => by
    rw [alloc.vec.Vec.getElem!_slice]
    exact limbs_lt_of_le (by decide) (hinvs1 k (hinvs1len ▸ hk)).2
  step as ⟨s1, hs1len, hs1⟩
  have hslen : invs1.slice.length = states.length := hinvs1len
  have hinvs : ∀ k < states.length, ({ slice := s1 } : alloc.vec.Vec FieldElement51)[k]!.toField =
      ((states[k]!).eg.toField * (states[k]!).fh.toField)⁻¹ ∧
      (({ slice := s1 } : alloc.vec.Vec FieldElement51)[k]!).LimbsLt 52 := by
    intro k hk
    obtain ⟨h0, h1⟩ := hs1 k (hslen ▸ hk)
    obtain ⟨hv, hb⟩ := hinvs1 k hk
    rw [alloc.vec.Vec.getElem!_slice] at h0 h1
    rw [alloc.vec.Vec.getElem!_mk, ← hv]
    exact toField_inv_of_batch h0 h1 hb
  step with loop1_spec states ps hsts (fun P hP => (hps P hP).2) _ hinvs
    (by rw [alloc.vec.Vec.length]; exact hs1len.trans hslen)
    (alloc.vec.Vec.with_capacity CompressedRistretto states.len) 0#usize (by simp) (by rfl)
    (fun k hk => absurd hk (by simp)) as ⟨r, hrlen, hr⟩
  exact ⟨hrlen.trans hpslen.symm, fun k hk => hr k (hpslen ▸ hk)⟩

end «RistrettoPointx86_64-no-tables»

namespace «RistrettoPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

open double_and_compress_batch

open scoped Helpers.IndexStep in
/-- The first loop: the products `e g · f h` of the states. -/
private theorem loop0_spec (states : alloc.vec.Vec double_and_compress_batch.BatchCompressState)
    (hst : ∀ k < states.length, (states[k]!).eg.LimbsLt 26 ∧ (states[k]!).fh.LimbsLt 26)
    (invs : alloc.vec.Vec FieldElement2625) (i : ℕ) (hi : i ≤ states.length)
    (hlen : invs.length = i)
    (hinvs : ∀ k < i, invs[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧
      (invs[k]!).LimbsLt 26) :
    double_and_compress_batch_loop1 { slice := states.deref, i } invs
      ⦃ (r : alloc.vec.Vec FieldElement2625) =>
      r.length = states.length ∧ ∀ k < states.length,
        r[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧
          (r[k]!).LimbsLt 26 ⦄ := by
  unfold double_and_compress_batch_loop1
  apply loop.spec_decr_nat (measure := fun (it, _) => states.length - it.i)
    (inv := fun (it, z) => it.slice = states.deref ∧ it.i ≤ states.length ∧
      z.length = it.i ∧ ∀ k < it.i,
      z[k]!.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧
        (z[k]!).LimbsLt 26)
  · rintro ⟨it, z⟩ ⟨hs, hi', hl, hz⟩
    unfold double_and_compress_batch_loop1.body
    have hsval : it.slice.val = states.val := by rw [hs]; exact Slice.from_val _ _
    by_cases hlt : it.i < states.length
    · have hnext : core.slice.iter.IteratorSliceIter.next it
          ⦃ o it1 => o = some (states[it.i]!) ∧
            it1 = { slice := it.slice, i := it.i + 1 } ⦄ := by
        have h := Curve25519Dalek.EdwardsOps.sliceNextSome it.slice it.i
          (by simpa [hsval] using hlt)
        apply spec_mono h
        rintro ⟨o, it1⟩ ⟨ho, hit⟩
        refine ⟨?_, hit⟩
        rw [ho, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos states.val it.i hlt]
        congr 1
        have hslt : it.i < it.slice.val.length := by simpa [hsval] using hlt
        change it.slice.val[it.i] = states.val[it.i]
        simp only [hsval]
      step with hnext as ⟨o, it1, ho, hit1⟩
      subst ho hit1
      obtain ⟨h1, h2⟩ := hst it.i hlt
      step with efgh_spec _ h1 h2 as ⟨fe, hfe, hfeb⟩
      step as ⟨z1, hz1⟩
      refine ⟨hs, by omega, ?_, ?_, by omega⟩
      · rw [alloc.vec.Vec.length_of_val_eq_append hz1, hl]
      · rw [← hl]
        exact alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x =>
          x.toField = (states[k]!).eg.toField * (states[k]!).fh.toField ∧ x.LimbsLt 26)
          hz1 (hl ▸ hz) (by rw [hl]; exact ⟨hfe, hfeb⟩)
    · have hnext : core.slice.iter.IteratorSliceIter.next it
          ⦃ o it1 => o = none ∧ it1 = it ⦄ := by
        have h := Curve25519Dalek.EdwardsOps.sliceNextNone it.slice it.i
          (by simpa [hsval] using Nat.le_of_not_gt hlt)
        simpa using h
      step with hnext as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have hin : it.i = states.length := by omega
      exact ⟨hl.trans hin, hin ▸ hz⟩
  · exact ⟨rfl, hi, hlen, hinvs⟩

set_option linter.hashCommand false in
#decompose double_and_compress_batch_loop2.body loop1_body_eq
  afterLets (branch 1 (letRange 2 23)) => compressState

/-- The encoding step of `double_and_compress_batch`'s second loop: the bytes of `2 P` from the
state of `P` and the inverse of `e g · f h`. -/
add_decl_doc compressState

private theorem compressState_eq (st : BatchCompressState) (inv : FieldElement2625) :
    compressState st inv =
      Backend.compressStateBody Backend.U32 st.e st.f st.g st.h st.eg st.fh inv := rfl

/-- The encoding step of the second loop: from the state of `P` and the inverse of `e g · f h`,
the bytes of `2 P`. -/
private theorem compressState_spec (P : RistrettoPoint.«i686-no-tables») (hP : P.OnCurve)
    (st : BatchCompressState) (hst : StateOf P st) (inv : FieldElement2625)
    (Inv : inv.toField = (st.eg.toField * st.fh.toField)⁻¹) (Invb : inv.LimbsLt 26) :
    compressState st inv ⦃ (bytes : CompressedRistretto) =>
      bytes.asNat = Ristretto.encodeRep (2 • P.toPoint) ⦄ := by
  obtain ⟨Se, Sf, Sg, Sh, Seg, Sfh, Seb, Sfb, Sgb, Shb, Segb, Sfhb⟩ := hst
  rw [edwards.EdwardsPoint.«i686-no-tables».onCurve_iff,
    edwards.EdwardsPoint.«i686-no-tables».toExtended_def] at hP
  rw [compressState_eq, edwards.EdwardsPoint.«i686-no-tables».toPoint_def,
    edwards.EdwardsPoint.«i686-no-tables».toExtended_def]
  exact Backend.compressStateBody_spec Backend.U32
    Backend.U32.sub_spec Backend.U32.mul_spec Backend.U32.neg_spec Backend.U32.sqrtM1_spec
    Backend.U32.invsqrtAMinusD_spec Backend.U32.is_negative_spec Backend.U32.conditional_assign_spec
    Backend.U32.conditional_negate_spec Backend.U32.to_bytes_spec _ _ _ _ _ _ _ hP Se Sf Sg Sh Seg
    Sfh Seb Sfb Sgb Shb Segb Sfhb Inv Invb


open scoped Helpers.IndexStep in
/-- The second loop: entry `k` encodes `2 P_k`, from the state and the inverse of `e g · f h`. -/
private theorem loop1_spec (states : alloc.vec.Vec double_and_compress_batch.BatchCompressState)
    (ps : List RistrettoPoint.«i686-no-tables») (hsts : List.Forall₂ StateOf ps states.val)
    (hon : ∀ P ∈ ps, P.OnCurve) (invs : alloc.vec.Vec FieldElement2625)
    (hinvs : ∀ k < states.length, invs[k]!.toField =
      ((states[k]!).eg.toField * (states[k]!).fh.toField)⁻¹ ∧ (invs[k]!).LimbsLt 26)
    (hinvlen : invs.length = states.length)
    (out : alloc.vec.Vec CompressedRistretto) (i : Usize) (hi : i.val ≤ states.length)
    (hlen : out.length = i.val)
    (hout : ∀ k < i.val, out[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint)) :
    double_and_compress_batch_loop2 { start := i, «end» := states.len } states invs out
      ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = states.length ∧
        ∀ k < states.length, r[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint) ⦄ := by
  have hpslen : ps.length = states.length := by
    rw [hsts.length_eq]
  unfold double_and_compress_batch_loop2
  apply loop.spec_decr_nat (measure := fun (it, _) => states.length - it.start.val)
    (inv := fun (it, o) => it.end = states.len ∧ it.start.val ≤ states.length ∧
      o.length = it.start.val ∧ ∀ k < it.start.val,
      o[k]!.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint))
  · rintro ⟨it, o⟩ ⟨hend, hi', hl, ho⟩
    dsimp only
    rw [loop1_body_eq]
    by_cases hlt : it.start.val < states.length
    · have hlt' : it.start.val < it.end.val := by
        rw [hend, alloc.vec.Vec.len_val]; exact hlt
      step with core.iter.range.IteratorRange.next_Usize_some_spec it hlt'
        as ⟨opt, it1, hopt, hstart1, hend1⟩
      subst hopt
      step as ⟨st, hst⟩
      replace hst : st = states[it.start.val]! := by
        rw [hst, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      step as ⟨inv, hinv⟩
      replace hinv : inv = invs[it.start.val]! := by
        rw [hinv, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos]
      obtain ⟨Inv, Invb⟩ := hinvs it.start.val hlt
      rw [← hst, ← hinv] at Inv
      rw [← hinv] at Invb
      rw [alloc.vec.Vec.getElem!_Nat_eq] at hst
      have hPmem : ps[it.start.val]! ∈ ps := by
        rw [getElem!_pos ps it.start.val (hpslen ▸ hlt)]
        exact List.getElem_mem _
      have hS := forall₂_getElem! hsts it.start.val (hpslen ▸ hlt)
      rw [← hst] at hS
      step with compressState_spec _ (hon _ hPmem) st hS inv Inv Invb as ⟨bytes, hbytes⟩
      step as ⟨o1, ho1⟩
      refine ⟨hend1.trans hend, by scalar_tac,
        by rw [alloc.vec.Vec.length_of_val_eq_append ho1, hl, hstart1], ?_, by scalar_tac⟩
      rw [hstart1, ← hl]
      refine alloc.vec.Vec.forall_lt_of_val_eq_append (P := fun k x =>
        x.asNat = Ristretto.encodeRep (2 • (ps[k]!).toPoint)) ho1 (hl ▸ ho) ?_
      rw [hl]
      exact hbytes
    · have hge : it.end.val ≤ it.start.val := by
        rw [hend, alloc.vec.Vec.len_val]; omega
      step with core.iter.range.IteratorRange.next_Usize_none_spec it hge
        as ⟨opt, it1, hopt, hit1⟩
      subst hopt
      simp only [WP.spec_ok]
      have hin : it.start.val = states.length := by omega
      exact ⟨hl.trans hin, hin ▸ ho⟩
  · exact ⟨rfl, hi, hlen, hout⟩

/-- `RistrettoPoint::double_and_compress_batch`: entry `i` is RFC 9496's encoding of `2 P_i` for
the points `P_i` the input yields; limbs `< 2^26`. -/
@[step]
theorem double_and_compress_batch_spec {I Clause0_IntoIter : Type}
    (pointsInst :
      core.iter.traits.collect.IntoIterator I RistrettoPoint.«i686-no-tables» Clause0_IntoIter)
    (points : I) (ps : List RistrettoPoint.«i686-no-tables»)
    (hpoints : pointsInst.Yields points ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26 ∧ P.OnCurve) (hlen : ps.length ≤ Usize.max) :
    double_and_compress_batch pointsInst points ⦃ (r : alloc.vec.Vec CompressedRistretto) =>
      r.length = ps.length ∧
        ∀ i < ps.length, r[i]!.asNat = Ristretto.encodeRep (2 • (ps[i]!).toPoint) ⦄ := by
  unfold double_and_compress_batch
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ps ⦄ := hpoints
  step with hpoints' as ⟨it, hit⟩
  step with states_spec pointsInst it ps hit (fun P hP => (hps P hP).1) hlen as ⟨states, hsts⟩
  have hpslen : ps.length = states.length := hsts.length_eq
  have hst : ∀ k < states.length, (states[k]!).eg.LimbsLt 26 ∧ (states[k]!).fh.LimbsLt 26 :=
    fun k hk => by
      have h := forall₂_getElem! hsts k (hpslen ▸ hk)
      rw [alloc.vec.Vec.getElem!_Nat_eq]
      exact ⟨h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩
  simp only [SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter,
    core.slice.Slice.iter, bind_ok]
  step with loop0_spec states hst (alloc.vec.Vec.with_capacity FieldElement2625 states.len) 0
    (by simp) (by rfl) (fun k hk => absurd hk (by simp)) as ⟨invs1, hinvs1len, hinvs1⟩
  simp only [alloc.vec.Vec.index_mut, pure]
  have hsb : ∀ k < invs1.slice.length, (invs1.slice[k]!).LimbsLt 27 := fun k hk => by
    rw [alloc.vec.Vec.getElem!_slice]
    exact limbs_lt_of_le (by decide) (hinvs1 k (hinvs1len ▸ hk)).2
  step as ⟨s1, hs1len, hs1⟩
  have hslen : invs1.slice.length = states.length := hinvs1len
  have hinvs : ∀ k < states.length, ({ slice := s1 } : alloc.vec.Vec FieldElement2625)[k]!.toField =
      ((states[k]!).eg.toField * (states[k]!).fh.toField)⁻¹ ∧
      (({ slice := s1 } : alloc.vec.Vec FieldElement2625)[k]!).LimbsLt 26 := by
    intro k hk
    obtain ⟨h0, h1⟩ := hs1 k (hslen ▸ hk)
    obtain ⟨hv, hb⟩ := hinvs1 k hk
    rw [alloc.vec.Vec.getElem!_slice] at h0 h1
    rw [alloc.vec.Vec.getElem!_mk, ← hv]
    exact toField_inv_of_batch h0 h1 hb
  step with loop1_spec states ps hsts (fun P hP => (hps P hP).2) _ hinvs
    (by rw [alloc.vec.Vec.length]; exact hs1len.trans hslen)
    (alloc.vec.Vec.with_capacity CompressedRistretto states.len) 0#usize (by simp) (by rfl)
    (fun k hk => absurd hk (by simp)) as ⟨r, hrlen, hr⟩
  exact ⟨hrlen.trans hpslen.symm, fun k hk => hr k (hpslen ▸ hk)⟩

end «RistrettoPointi686-no-tables»

end Curve25519Dalek.ristretto
