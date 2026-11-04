/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
import Proofs.Helpers.AsInt
import Proofs.Helpers.Iterator
import Proofs.Helpers.StepSpecs
import Proofs.Scalar.AsRadix16
public import Proofs.Helpers.EdwardsOps
public section

/-! # `variable_base::mul`: the generic part

The proofs over `EdwardsOps`, apart from the instances (`Mul.lean`).

Constant-time variable-base scalar multiplication: the radix-`16` digits `d[0], …, d[63]` of the
scalar (`as_radix_16`), Horner's rule from the top digit down, with `16 • Q` by four doublings and
`d[i] • P` from the lookup table of `P, 2 P, …, 8 P`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.variable_base

/-- The value `∑_{k < 64 - e} 16^k d[e + k]` of the top digits `d[e], …, d[63]`. -/
private def digitSum (d : Array I8 64#usize) (e : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (64 - e), 16 ^ k * d[e + k]!.val

private theorem digitSum_eq (d : Array I8 64#usize) (e : ℕ) (he : e < 64) :
    digitSum d e = d[e]!.val + 16 * digitSum d (e + 1) := by
  unfold digitSum
  rw [show 64 - e = 64 - (e + 1) + 1 by omega, Finset.sum_range_succ', Finset.mul_sum,
    pow_zero, one_mul, add_zero, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_succ, show e + (k + 1) = e + 1 + k by omega]
  ring

private theorem digitSum_sixtyThree (d : Array I8 64#usize) : digitSum d 63 = d[63]!.val := by
  simp [digitSum]

private theorem digitSum_zero (d : Array I8 64#usize) : digitSum d 0 = d.asInt 4 := by
  rw [Array.asInt_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zero_add, pow_mul]
  norm_num

/-- One Horner step on points: four doublings of `z • P`, plus `d • P`. -/
private theorem horner_step (z d : ℤ) (P : curve25519.edwards.Point) :
    2 • 2 • 2 • 2 • (z • P) + d • P = (d + 16 * z) • P := by
  simp only [← natCast_zsmul, smul_smul, ← add_smul]
  congr 1
  push_cast
  ring


end Curve25519Dalek.backend.serial.scalar_mul.variable_base

/-! ## The loop over a configuration's point operations -/

namespace Curve25519Dalek.EdwardsOps

open Curve25519Dalek.backend.serial.scalar_mul.variable_base

variable (O : EdwardsOps)

open ControlFlow

/-- `mul_loop.body` over the point operations. -/
@[expose] def vbLoopBody (lookup_table : window.LookupTable O.N)
    (scalar_digits : Array I8 64#usize)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (_tmp3 : O.E) (tmp1 : O.C) :
    Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) × O.E × O.C)
      O.C) := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter
  match o with
  | none => ok (done tmp1)
  | some i =>
    let tmp2 ← O.cAsProjective tmp1
    let tmp11 ← O.pDouble tmp2
    let tmp21 ← O.cAsProjective tmp11
    let tmp12 ← O.pDouble tmp21
    let tmp22 ← O.cAsProjective tmp12
    let tmp13 ← O.pDouble tmp22
    let tmp23 ← O.cAsProjective tmp13
    let tmp14 ← O.pDouble tmp23
    let tmp31 ← O.asExtended tmp14
    let i1 ← Array.index_usize scalar_digits i
    let pnp ← O.ltSelect lookup_table i1
    let tmp15 ← O.addN tmp31 pnp
    ok (cont (iter1, tmp31, tmp15))

/-- `mul_loop` over the point operations. -/
@[expose] def vbLoop (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (lookup_table : window.LookupTable O.N) (scalar_digits : Array I8 64#usize) (tmp3 : O.E)
    (tmp1 : O.C) : Result O.C := do
  loop (fun (iter1, tmp31, tmp11) => O.vbLoopBody lookup_table scalar_digits iter1 tmp31 tmp11)
    (iter, tmp3, tmp1)

/-- `variable_base::mul` over the point operations. -/
@[expose] def vbMul (point : O.E) (s : scalar.Scalar) : Result O.E := do
  let lookup_table ← O.ltFrom point
  let scalar_digits ← scalar.Scalar.as_radix_16 s
  let tmp3 ← O.identity
  let i ← Array.index_usize scalar_digits 63#usize
  let pnp ← O.ltSelect lookup_table i
  let tmp1 ← O.addN tmp3 pnp
  let iter ←
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
      { start := 0#usize, «end» := 63#usize }
  let tmp11 ← O.vbLoop iter lookup_table scalar_digits tmp3 tmp1
  O.asExtended tmp11

open scoped Helpers.IndexStep in
/-- The loop of `mul`: after the digits `d[e], …, d[62]`, the accumulator represents
`digitSum d e • P`. -/
private theorem vbLoop_spec (haddN : O.AddNSpec) (hasE : O.AsExtendedSpec) (hsel : O.LtSelectSpec)
    (hdbl : O.PDoubleSpec) (hasP : O.CAsProjectiveSpec)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (lookup_table : window.LookupTable O.N) (scalar_digits : Array I8 64#usize) (tmp3 : O.E)
    (tmp1 : O.C) (P : curve25519.edwards.Point)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 63)
    (htab : lookup_table.LimbsLt O.nB) (hP : lookup_table.Represents P)
    (hd : ∀ i : ℕ, i < 64 → -8 ≤ scalar_digits[i]!.val ∧ scalar_digits[i]!.val ≤ 8)
    (hon : O.cOnCurve tmp1) (hb : O.cBnd tmp1)
    (h1 : O.cToPoint tmp1 = digitSum scalar_digits iter.iter.end.val • P) :
    O.vbLoop iter lookup_table scalar_digits tmp3 tmp1 ⦃ (r : O.C) =>
        O.cOnCurve r ∧ O.cToPoint r = digitSum scalar_digits 0 • P ∧ O.cBnd r ⦄ := by
  unfold vbLoop
  apply loop.spec_decr_nat (measure := fun (it, _, _) => it.iter.end.val)
    (inv := fun (it, _, t) => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 63 ∧ O.cOnCurve t ∧
      O.cBnd t ∧ O.cToPoint t = digitSum scalar_digits it.iter.end.val • P)
  · rintro ⟨it, t3, t⟩ ⟨hst, hen, hton, htb, htp⟩
    unfold vbLoopBody
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, i, ho, hi, hstart1, hend1⟩
      subst ho
      step with hasP t htb hton as ⟨p1, hp1on, hp1, hp1b⟩
      step with hdbl p1 hp1b hp1on as ⟨c1, hc1on, hc1, hc1b⟩
      step with hasP c1 hc1b hc1on as ⟨p2, hp2on, hp2, hp2b⟩
      step with hdbl p2 hp2b hp2on as ⟨c2, hc2on, hc2, hc2b⟩
      step with hasP c2 hc2b hc2on as ⟨p3, hp3on, hp3, hp3b⟩
      step with hdbl p3 hp3b hp3on as ⟨c3, hc3on, hc3, hc3b⟩
      step with hasP c3 hc3b hc3on as ⟨p4, hp4on, hp4, hp4b⟩
      step with hdbl p4 hp4b hp4on as ⟨c4, hc4on, hc4, hc4b⟩
      step with hasE c4 hc4b hc4on as ⟨e, heon, he, heb⟩
      step as ⟨di, hdi⟩
      step with hsel lookup_table di P htab hP as ⟨q, hqon, hq, hqb⟩
      step with haddN e q heb hqb heon hqon as ⟨t', ht'on, ht', ht'b⟩
      refine ⟨by rw [hstart1, hst], by scalar_tac, ht'on, ht'b, ?_, by scalar_tac⟩
      rw [ht', he, hc4, hp4, hc3, hp3, hc2, hp2, hc1, hp1, htp, hq, hdi, horner_step, hend1, ← hi,
        digitSum_eq _ i.val (by scalar_tac)]
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      rw [show it.iter.end.val = 0 by omega] at htp
      exact ⟨hton, htp, htb⟩
  · exact ⟨hstart, hend, hon, hb, h1⟩

open scoped Helpers.IndexStep in
/-- `variable_base::mul`: `s • P` for the unreduced value of `s` (`s.asNat < 2^255`). -/
theorem vbMul_spec (hid : O.IdentitySpec) (haddN : O.AddNSpec) (hasE : O.AsExtendedSpec)
    (hsel : O.LtSelectSpec) (hfrom : O.LtFromSpec) (hdbl : O.PDoubleSpec)
    (hasP : O.CAsProjectiveSpec) (point : O.E) (s : scalar.Scalar)
    (hpoint : O.Bnd point) (hon : O.OnCurve point) (hs : s.asNat < 2 ^ 255) :
    O.vbMul point s ⦃ (r : O.E) =>
      O.OnCurve r ∧ O.toPoint r = s.asNat • O.toPoint point ∧ O.Bnd r ⦄ := by
  unfold vbMul
  step with hfrom point hpoint hon as ⟨table, hrep, htab⟩
  step as ⟨d, hval, hlow, h63l, h63u⟩
  have hd : ∀ i : ℕ, i < 64 → -8 ≤ d[i]!.val ∧ d[i]!.val ≤ 8 := fun i hi => by
    rcases Nat.lt_or_ge i 63 with h | h
    · exact ⟨(hlow i h).1, (hlow i h).2.le⟩
    · rw [show i = 63 by omega]; exact ⟨h63l, h63u⟩
  apply spec_bind hid
  rintro t3 ⟨ht3on, ht3, ht3b⟩
  step as ⟨d63, hd63⟩
  step with hsel table d63 (O.toPoint point) htab hrep as ⟨q, hqon, hq, hqb⟩
  step with haddN t3 q ht3b hqb ht3on hqon as ⟨t1, ht1on, ht1, ht1b⟩
  step as ⟨iter, hiter⟩
  have h1 : O.cToPoint t1 = digitSum d iter.iter.end.val • O.toPoint point := by
    rw [ht1, ht3, hq, hd63, zero_add, hiter]
    exact congrArg (· • O.toPoint point) (digitSum_sixtyThree d).symm
  step with O.vbLoop_spec haddN hasE hsel hdbl hasP iter table d t3 t1 (O.toPoint point)
    (by rw [hiter]; rfl) (by rw [hiter]; decide) htab hrep hd ht1on ht1b h1 as ⟨t, hton, htp, htb⟩
  step with hasE t htb hton as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, htp, digitSum_zero, hval, natCast_zsmul]

end Curve25519Dalek.EdwardsOps
