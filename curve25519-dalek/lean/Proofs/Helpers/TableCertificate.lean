/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Curve25519.Proofs.Edwards.Certs
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Mathlib.Tactic.LinearCombination
public import Proofs.Helpers.ByteValues
public section

/-! # Certifying the precomputed tables

A translated table constant is a chain of `from_limbs` binds followed by a value built from the
field elements. `Result.bind` does not reduce (it is a coinductive fixed point), so the chain is
reflected once: `bindList xs k` is the shape, `bindList_eq` evaluates it, and `collect_limbs`
reads the limb arrays off the translated constant; the equation `constant = bindList limbs k` is
then checked by the kernel alone (`kernel_rfl`), with no copies of the chain.

The content is certified in extended coordinates without inversion: `checkRow S Q l` checks that
the entries of `l` (three limb arrays each) are `Q, Q + S, Q + 2 S, …`, and `checkTable P fes n`
that the rows of `fes` (24 limb arrays each) are the lookup tables of `P, 2^8 P, 2^16 P, …`.
Both are `Bool` functions over the flat list, evaluated by `decide +kernel`; their soundness
(`checkRow_sound`, `checkTable_sound`) is proved once, generically. -/

open Lean Elab Command Meta
open Aeneas Aeneas.Std Result curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.TableCertificate

/-! ### The bind chain -/

theorem bind_from_limbs {β : Type} (a : FieldElement51) (f : FieldElement51 → Result β) :
    Aeneas.Std.bind (FieldElement51.from_limbs a) f = f a := by
  unfold FieldElement51.from_limbs
  simp

/-- The shape of a translated table constant: a chain of `from_limbs` binds, then a value built
from the field elements. -/
@[expose] def bindList {β : Type} :
    List FieldElement51 → (List FieldElement51 → Result β) → Result β
  | [], k => k []
  | l :: xs, k =>
    Aeneas.Std.bind (FieldElement51.from_limbs l) fun fe => bindList xs fun fes => k (fe :: fes)

theorem bindList_eq {β : Type} (xs : List FieldElement51)
    (k : List FieldElement51 → Result β) : bindList xs k = k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons l xs ih => simp only [bindList, bind_from_limbs, ih]

/-- `collect_limbs xs from c` defines `xs : List FieldElement51` as the limb arrays of the
`from_limbs` bind chain of the translated constant `c`, in order. -/
syntax (name := collectLimbs) "collect_limbs " ident " from " ident : command

elab_rules : command
  | `(collect_limbs $n:ident from $c:ident) => liftTermElabM do
  let cn ← realizeGlobalConstNoOverloadWithInfo c
  let some body ← withTransparency .all (unfoldDefinition? (mkConst cn))
    | throwError "collect_limbs: cannot unfold {cn}"
  let mut e := body
  let mut xs : Array Expr := #[]
  while e.isAppOfArity ``Aeneas.Std.bind 4 do
    let #[_, _, x, f] := e.getAppArgs | unreachable!
    unless x.isAppOfArity ``Curve25519Dalek.backend.serial.u64.field.FieldElement51.from_limbs 1 do
      throwError "collect_limbs: a bind of {x.getAppFn}, not of from_limbs"
    let a := x.appArg!
    if a.hasLooseBVars then throwError "collect_limbs: a limb array depends on earlier binds"
    xs := xs.push a
    e := f.bindingBody!
  unless e.isAppOfArity ``Aeneas.Std.Result.ok 2 do
    throwError "collect_limbs: the chain ends in {e.getAppFn}, not in ok"
  let ty := mkConst ``Curve25519Dalek.backend.serial.u64.field.FieldElement51
  let lst ← mkListLit ty xs.toList
  addDecl <| .defnDecl (mkDefinitionValEx n.getId [] (← inferType lst) lst .abbrev .safe [])
  addDocStringCore n.getId s!"The limb arrays of `{cn}`, in order (`collect_limbs`)."

/-- Closes a goal `a = b` by `Eq.refl a`, checked by the kernel only: the elaborator's
definitional-equality check is skipped. -/
syntax (name := kernelRfl) "kernel_rfl" : tactic

elab_rules : tactic
  | `(tactic| kernel_rfl) => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let some (_, lhs, _) := (← g.getType).eq? | throwError "kernel_rfl: not an equation"
  g.assign (← mkEqRefl lhs)

/-! ### Limbs as numbers -/

/-- The value of five radix-`2^51` limbs (`asNat`, in a form the kernel evaluates). -/
@[expose] def limbsNat (a : FieldElement51) : ℕ :=
  match a.val with
  | [l0, l1, l2, l3, l4] =>
    l0.val + l1.val * 2 ^ 51 + l2.val * 2 ^ 102 + l3.val * 2 ^ 153 + l4.val * 2 ^ 204
  | _ => 0

theorem limbsNat_eq_asNat (a : FieldElement51) : limbsNat a = a.asNat := by
  rw [asNat_def, Array.asNat_def]
  have hl : a.val.length = 5 := by simp
  match h : a.val, hl with
  | [l0, l1, l2, l3, l4], _ =>
    simp only [limbsNat, h, List.map, Nat.ofDigits_cons, Nat.ofDigits_nil]
    ring

/-! ### The checker -/

variable (E : TwistedEdwardsModel (ZMod p))

/-- The basepoint in extended coordinates `(x : y : 1 : x y)`, as numerals. -/
@[expose] noncomputable def basepointExt : E.Extended :=
  ⟨15112221349535400772501151409588531511454012693041857206046113283949847762202,
    46316835694926478169428394003475163141307993866256225615783033603165251855960, 1,
    15112221349535400772501151409588531511454012693041857206046113283949847762202 *
      46316835694926478169428394003475163141307993866256225615783033603165251855960⟩

/-- `Q = (X : Y : Z : T)` is the point with affine Niels limbs `(y + x, y - x, 2 d x y)`:
`2 X = (a - b) Z`, `2 Y = (a + b) Z` and `c Z² = 2 d X Y`. -/
@[expose] noncomputable def checkEntry (Q : E.Extended) (ya yb c : FieldElement51) : Bool :=
  let a : ZMod p := limbsNat ya
  let b : ZMod p := limbsNat yb
  let c' : ZMod p := limbsNat c
  decide (2 * Q.X = (a - b) * Q.Z ∧ 2 * Q.Y = (a + b) * Q.Z ∧
    c' * Q.Z * Q.Z = 2 * E.d * Q.X * Q.Y)

/-- The entries of `l` (three limb arrays each) are `Q, Q + S, Q + 2 S, …`. -/
@[expose] noncomputable def checkRow (S : E.Extended) : E.Extended → List FieldElement51 → Bool
  | _, [] => true
  | Q, ya :: yb :: c :: rest => checkEntry E Q ya yb c && checkRow S (Q.add S) rest
  | _, _ => false

/-- `n` doublings. -/
@[expose] noncomputable def pow2 (n : ℕ) (P : E.Extended) : E.Extended :=
  Extended.double^[n] P

/-- The rows of `fes` (24 limb arrays each) are the lookup tables of `P, 2^8 P, 2^16 P, …`. -/
@[expose] noncomputable def checkTable : E.Extended → List FieldElement51 → ℕ → Bool
  | _, fes, 0 => fes.isEmpty
  | P, fes, n + 1 => checkRow E P P (fes.take 24) && checkTable (pow2 E 8 P) (fes.drop 24) n

/-! ### Soundness -/

theorem two_ne_zero' : (2 : ZMod p) ≠ 0 := IsComplete.two_ne_zero (E := edwards)

theorem onCurve_basepointExt : (basepointExt edwards).OnCurve := by
  have h : basepoint.toExtended = basepointExt edwards := by
    rw [Point.toExtended, basepoint_x_eq, basepoint_y_eq]
    rfl
  rw [← h]
  exact Point.onCurve_toExtended basepoint

theorem toPoint_basepointExt : (basepointExt edwards).toPoint = basepoint := by
  have h : basepoint.toExtended = basepointExt edwards := by
    rw [Point.toExtended, basepoint_x_eq, basepoint_y_eq]
    rfl
  rw [← h]
  exact Point.toPoint_toExtended basepoint

theorem pow2_onCurve {P : edwards.Extended} (h : P.OnCurve) (n : ℕ) :
    (pow2 edwards n P).OnCurve := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [pow2, Function.iterate_succ_apply']
    exact Extended.double_onCurve ih

theorem toPoint_pow2 {P : edwards.Extended} (h : P.OnCurve) (n : ℕ) :
    (pow2 edwards n P).toPoint = 2 ^ n • P.toPoint := by
  induction n with
  | zero => simp [pow2]
  | succ n ih =>
    have e : pow2 edwards (n + 1) P = (pow2 edwards n P).double := by
      simp only [pow2, Function.iterate_succ_apply']
    rw [e, Extended.toPoint_double (pow2_onCurve h n), ih, smul_smul, pow_succ, mul_comm]

/-- An entry passing `checkEntry` against `Q` on the curve represents `Q`. -/
theorem checkEntry_sound {Q : edwards.Extended} (hQ : Q.OnCurve) {ya yb c : FieldElement51}
    (h : checkEntry edwards Q ya yb c = true) :
    (⟨ya, yb, c⟩ : AffineNielsPoint.«x86_64-tables»).OnCurve ∧
      (⟨ya, yb, c⟩ : AffineNielsPoint.«x86_64-tables»).toPoint = Q.toPoint := by
  simp only [checkEntry, decide_eq_true_eq, limbsNat_eq_asNat, ← toField_def] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hZ : Q.Z ≠ 0 := hQ.1
  have hX := Extended.X_eq_toPoint_x_mul_Z hQ
  have hY := Extended.Y_eq_toPoint_y_mul_Z hQ
  set x := Q.toPoint.x with hx
  set y := Q.toPoint.y with hy
  have e1 : 2 * x = ya.toField - yb.toField :=
    mul_right_cancel₀ hZ (by rw [mul_assoc, ← hX]; exact h1)
  have e2 : 2 * y = ya.toField + yb.toField :=
    mul_right_cancel₀ hZ (by rw [mul_assoc, ← hY]; exact h2)
  have ha : ya.toField = y + x := mul_left_cancel₀ two_ne_zero' (by linear_combination -e1 - e2)
  have hb : yb.toField = y - x := mul_left_cancel₀ two_ne_zero' (by linear_combination -e2 + e1)
  have hc : c.toField = 2 * d * x * y := by
    have h0 : (c.toField - 2 * d * x * y) * (Q.Z * Q.Z) = 0 := by
      rw [hX, hY, edwards_d] at h3
      linear_combination h3
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd (mul_self_eq_zero.mp h0) hZ
  have hx' : (⟨ya, yb, c⟩ : AffineNielsPoint.«x86_64-tables»).toAffineNiels.x = x := by
    rw [AffineNielsPoint.«x86_64-tables».toAffineNiels_x]
    simp only
    rw [ha, hb, show y + x - (y - x) = 2 * x by ring, mul_div_cancel_left₀ x two_ne_zero']
  have hy' : (⟨ya, yb, c⟩ : AffineNielsPoint.«x86_64-tables»).toAffineNiels.y = y := by
    rw [AffineNielsPoint.«x86_64-tables».toAffineNiels_y]
    simp only
    rw [ha, hb, show y + x + (y - x) = 2 * y by ring, mul_div_cancel_left₀ y two_ne_zero']
  have hon : (⟨ya, yb, c⟩ : AffineNielsPoint.«x86_64-tables»).OnCurve := by
    rw [AffineNielsPoint.«x86_64-tables».onCurve_iff_equation, hx', hy']
    exact ⟨Q.toPoint.equation, hc⟩
  refine ⟨hon, Point.ext ?_ ?_⟩
  · rw [AffineNielsPoint.«x86_64-tables».toPoint_x hon, hx']
  · rw [AffineNielsPoint.«x86_64-tables».toPoint_y hon, hy']

/-- Entry `j` of a list passing `checkRow S Q` represents `Q + j • S`. -/
theorem checkRow_sound {S : edwards.Extended} (hS : S.OnCurve) :
    ∀ {Q : edwards.Extended} {l : List FieldElement51}, Q.OnCurve →
      checkRow edwards S Q l = true → ∀ j, 3 * j + 2 < l.length →
      (⟨l[3 * j]!, l[3 * j + 1]!, l[3 * j + 2]!⟩ : AffineNielsPoint.«x86_64-tables»).OnCurve ∧
        (⟨l[3 * j]!, l[3 * j + 1]!, l[3 * j + 2]!⟩ :
          AffineNielsPoint.«x86_64-tables»).toPoint = Q.toPoint + j • S.toPoint
  | _, [], _, _, j, hj => absurd hj (by simp)
  | _, [_], _, h, _, _ => by simp [checkRow] at h
  | _, [_, _], _, h, _, _ => by simp [checkRow] at h
  | Q, ya :: yb :: c :: rest, hQ, h, 0, _ => by
    simp only [checkRow, Bool.and_eq_true] at h
    simpa using checkEntry_sound hQ h.1
  | Q, ya :: yb :: c :: rest, hQ, h, j + 1, hj => by
    simp only [checkRow, Bool.and_eq_true] at h
    have ih := checkRow_sound hS (Extended.add_onCurve hQ hS) h.2 j
      (by simp only [List.length_cons] at hj; omega)
    rw [Extended.toPoint_add hQ hS, add_assoc, ← succ_nsmul'] at ih
    rw [show 3 * (j + 1) = 3 * j + 2 + 1 by ring,
      show 3 * j + 2 + 1 + 1 = 3 * j + 1 + 1 + 1 + 1 by ring,
      show 3 * j + 2 + 1 + 2 = 3 * j + 2 + 1 + 1 + 1 by ring]
    simpa only [List.getElem!_cons_succ] using ih

theorem getElem!_take_of_lt {l : List FieldElement51} {n i : ℕ} (h : i < n) :
    (l.take n)[i]! = l[i]! := by
  simp [List.getElem!_eq_getElem?_getD, h]

theorem getElem!_drop (l : List FieldElement51) (n i : ℕ) : (l.drop n)[i]! = l[n + i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop]

/-- Entry `j` of row `i` of a list passing `checkTable P · n` represents
`(j + 1) • 2^(8 i) • P`. -/
theorem checkTable_sound :
    ∀ {n : ℕ} {P : edwards.Extended} {fes : List FieldElement51}, P.OnCurve →
      checkTable edwards P fes n = true → fes.length = 24 * n → ∀ i < n, ∀ j : ℕ, j < 8 →
      (⟨fes[24 * i + 3 * j]!, fes[24 * i + 3 * j + 1]!, fes[24 * i + 3 * j + 2]!⟩ :
        AffineNielsPoint.«x86_64-tables»).OnCurve ∧
      (⟨fes[24 * i + 3 * j]!, fes[24 * i + 3 * j + 1]!, fes[24 * i + 3 * j + 2]!⟩ :
        AffineNielsPoint.«x86_64-tables»).toPoint = (j + 1) • 2 ^ (8 * i) • P.toPoint
  | 0, _, _, _, _, _, i, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, P, fes, hP, h, hlen, i, hi, j, hj => by
    simp only [checkTable, Bool.and_eq_true] at h
    cases i with
    | zero =>
      have hrow := checkRow_sound hP hP h.1 j (by simp only [List.length_take]; omega)
      rw [← succ_nsmul'] at hrow
      simpa only [Nat.mul_zero, Nat.zero_add, pow_zero, one_nsmul, getElem!_take_of_lt
        (show 3 * j < 24 by omega), getElem!_take_of_lt (show 3 * j + 1 < 24 by omega),
        getElem!_take_of_lt (show 3 * j + 2 < 24 by omega)] using hrow
    | succ i =>
      have ih := checkTable_sound (pow2_onCurve hP 8) h.2
        (by simp only [List.length_drop]; omega) i (by omega) j hj
      rw [toPoint_pow2 hP, smul_smul (2 ^ (8 * i)) (2 ^ 8), ← pow_add, getElem!_drop, getElem!_drop,
        getElem!_drop] at ih
      rw [show 24 * (i + 1) + 3 * j + 2 = 24 + (24 * i + 3 * j + 2) by ring,
        show 24 * (i + 1) + 3 * j + 1 = 24 + (24 * i + 3 * j + 1) by ring,
        show 24 * (i + 1) + 3 * j = 24 + (24 * i + 3 * j) by ring,
        show 8 * (i + 1) = 8 * i + 8 by ring]
      exact ih

/-! ### Projective Niels entries -/

/-- `Q = (X : Y : Z : T)` is the point with projective Niels limbs `(Y' + X', Y' - X', Z', 2 d T')`:
`Z' ≠ 0`, `2 X Z' = (a - b) Z`, `2 Y Z' = (a + b) Z` and `2 t Z' = d (a - b) (a + b)`. -/
@[expose] noncomputable def checkEntryProj (Q : E.Extended) (ya yb z t : FieldElement51) : Bool :=
  let a : ZMod p := limbsNat ya
  let b : ZMod p := limbsNat yb
  let z' : ZMod p := limbsNat z
  let t' : ZMod p := limbsNat t
  decide (z' ≠ 0 ∧ 2 * Q.X * z' = (a - b) * Q.Z ∧ 2 * Q.Y * z' = (a + b) * Q.Z ∧
    2 * t' * z' = E.d * (a - b) * (a + b))

/-- The entries of `l` (four limb arrays each) are `Q, Q + S, Q + 2 S, …`. -/
@[expose] noncomputable def checkRowProj (S : E.Extended) :
    E.Extended → List FieldElement51 → Bool
  | _, [] => true
  | Q, ya :: yb :: z :: t :: rest =>
    checkEntryProj E Q ya yb z t && checkRowProj S (Q.add S) rest
  | _, _ => false

/-- An entry passing `checkEntryProj` against `Q` on the curve represents `Q`. -/
theorem checkEntryProj_sound {Q : edwards.Extended} (hQ : Q.OnCurve)
    {ya yb z t : FieldElement51} (h : checkEntryProj edwards Q ya yb z t = true) :
    (⟨ya, yb, z, t⟩ : ProjectiveNielsPoint.«x86_64-tables»).OnCurve ∧
      (⟨ya, yb, z, t⟩ : ProjectiveNielsPoint.«x86_64-tables»).toPoint = Q.toPoint := by
  simp only [checkEntryProj, decide_eq_true_eq, limbsNat_eq_asNat, ← toField_def] at h
  obtain ⟨hz, h1, h2, h3⟩ := h
  have hZ : Q.Z ≠ 0 := hQ.1
  have hX := Extended.X_eq_toPoint_x_mul_Z hQ
  have hY := Extended.Y_eq_toPoint_y_mul_Z hQ
  set x := Q.toPoint.x with hx
  set y := Q.toPoint.y with hy
  have e1 : 2 * x * z.toField = ya.toField - yb.toField :=
    mul_right_cancel₀ hZ (by rw [hX] at h1; linear_combination h1)
  have e2 : 2 * y * z.toField = ya.toField + yb.toField :=
    mul_right_cancel₀ hZ (by rw [hY] at h2; linear_combination h2)
  have ha : ya.toField = (y + x) * z.toField :=
    mul_left_cancel₀ two_ne_zero' (by linear_combination -e1 - e2)
  have hb : yb.toField = (y - x) * z.toField :=
    mul_left_cancel₀ two_ne_zero' (by linear_combination -e2 + e1)
  have hX' : (⟨ya, yb, z, t⟩ : ProjectiveNielsPoint.«x86_64-tables»).toProjectiveNiels.X =
      x * z.toField := by
    rw [ProjectiveNielsPoint.«x86_64-tables».toProjectiveNiels_X]
    simp only
    rw [ha, hb, show (y + x) * z.toField - (y - x) * z.toField = 2 * (x * z.toField) by ring,
      mul_div_cancel_left₀ _ two_ne_zero']
  have hY' : (⟨ya, yb, z, t⟩ : ProjectiveNielsPoint.«x86_64-tables»).toProjectiveNiels.Y =
      y * z.toField := by
    rw [ProjectiveNielsPoint.«x86_64-tables».toProjectiveNiels_Y]
    simp only
    rw [ha, hb, show (y + x) * z.toField + (y - x) * z.toField = 2 * (y * z.toField) by ring,
      mul_div_cancel_left₀ _ two_ne_zero']
  have ht : t.toField * z.toField = 2 * d * (x * z.toField) * (y * z.toField) := by
    refine mul_left_cancel₀ two_ne_zero' ?_
    rw [ha, hb, edwards_d] at h3
    linear_combination h3
  have hon : (⟨ya, yb, z, t⟩ : ProjectiveNielsPoint.«x86_64-tables»).OnCurve := by
    rw [ProjectiveNielsPoint.«x86_64-tables».onCurve_iff_equation, hX', hY']
    refine ⟨hz, ?_, ht⟩
    rw [mul_div_cancel_right₀ x hz, mul_div_cancel_right₀ y hz]
    exact Q.toPoint.equation
  refine ⟨hon, Point.ext ?_ ?_⟩
  · rw [ProjectiveNielsPoint.«x86_64-tables».toPoint_x hon, hX']
    exact mul_div_cancel_right₀ x hz
  · rw [ProjectiveNielsPoint.«x86_64-tables».toPoint_y hon, hY']
    exact mul_div_cancel_right₀ y hz

/-- Entry `k` of a list passing `checkRowProj S Q` represents `Q + k • S`. -/
theorem checkRowProj_sound {S : edwards.Extended} (hS : S.OnCurve) :
    ∀ {Q : edwards.Extended} {l : List FieldElement51}, Q.OnCurve →
      checkRowProj edwards S Q l = true → ∀ k, 4 * k + 3 < l.length →
      (⟨l[4 * k]!, l[4 * k + 1]!, l[4 * k + 2]!, l[4 * k + 3]!⟩ :
        ProjectiveNielsPoint.«x86_64-tables»).OnCurve ∧
        (⟨l[4 * k]!, l[4 * k + 1]!, l[4 * k + 2]!, l[4 * k + 3]!⟩ :
          ProjectiveNielsPoint.«x86_64-tables»).toPoint = Q.toPoint + k • S.toPoint
  | _, [], _, _, k, hk => absurd hk (by simp)
  | _, [_], _, h, _, _ => by simp [checkRowProj] at h
  | _, [_, _], _, h, _, _ => by simp [checkRowProj] at h
  | _, [_, _, _], _, h, _, _ => by simp [checkRowProj] at h
  | Q, ya :: yb :: z :: t :: rest, hQ, h, 0, _ => by
    simp only [checkRowProj, Bool.and_eq_true] at h
    simpa using checkEntryProj_sound hQ h.1
  | Q, ya :: yb :: z :: t :: rest, hQ, h, k + 1, hk => by
    simp only [checkRowProj, Bool.and_eq_true] at h
    have ih := checkRowProj_sound hS (Extended.add_onCurve hQ hS) h.2 k
      (by simp only [List.length_cons] at hk; omega)
    rw [Extended.toPoint_add hQ hS, add_assoc, ← succ_nsmul'] at ih
    rw [show 4 * (k + 1) = 4 * k + 3 + 1 by ring]
    simpa only [List.getElem!_cons_succ] using ih

/-- The odd multiples of `2^n • B` as a row: `2^n • B + k • 2^(n + 1) • B`. -/
theorem odd_smul_eq (B : edwards.Point) (n k : ℕ) :
    2 ^ n • B + k • 2 ^ (n + 1) • B = (2 * k + 1) • 2 ^ n • B := by
  rw [succ_nsmul', smul_smul, smul_smul]
  congr 1
  congr 1
  ring

/-! ### Single points -/

/-- `Q` is on the curve (division-free form) and projectively equal to `2^n • B`. -/
@[expose] noncomputable def checkPoint (Q : E.Extended) (n : ℕ) : Bool :=
  decide (Q.Z ≠ 0 ∧ Q.X * Q.Y = Q.Z * Q.T ∧
    E.a * Q.X ^ 2 * Q.Z ^ 2 + Q.Y ^ 2 * Q.Z ^ 2 = Q.Z ^ 4 + E.d * Q.X ^ 2 * Q.Y ^ 2 ∧
    Q.ProjEq (pow2 E n (basepointExt E)))

/-- A point passing `checkPoint` is on the curve and represents `2^n • B`. -/
theorem checkPoint_sound {Q : edwards.Extended} {n : ℕ} (h : checkPoint edwards Q n = true) :
    Q.OnCurve ∧ Q.toPoint = 2 ^ n • basepoint := by
  simp only [checkPoint, decide_eq_true_eq] at h
  obtain ⟨hZ, hT, heq, hproj⟩ := h
  have hon : Q.OnCurve := (Extended.onCurve_iff_homogeneous Q).mpr ⟨hZ, hT, heq⟩
  refine ⟨hon, ?_⟩
  rw [(Extended.projEq_iff_toPoint_eq hon (pow2_onCurve onCurve_basepointExt n)).mp hproj,
    toPoint_pow2 onCurve_basepointExt, toPoint_basepointExt]

/-! ### Tables from flat lists

The constructors consume the list sequentially, so that the kernel compares `mk fes` with the
translated structure in linear time (indexing into `fes` there cost 8 s for 768 elements). The
index lemmas serve the proofs. -/

/-- Affine Niels entries, three limb arrays each. -/
@[expose] def entries : List FieldElement51 → List AffineNielsPoint.«x86_64-tables»
  | ya :: yb :: c :: rest => ⟨ya, yb, c⟩ :: entries rest
  | _ => []

/-- Projective Niels entries, four limb arrays each. -/
@[expose] def entriesProj : List FieldElement51 → List ProjectiveNielsPoint.«x86_64-tables»
  | ya :: yb :: z :: t :: rest => ⟨ya, yb, z, t⟩ :: entriesProj rest
  | _ => []

/-- Lookup tables of eight entries each. -/
@[expose] def rows {T : Type} : List T → List (window.LookupTable T)
  | e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: rest =>
    Array.make 8#usize [e0, e1, e2, e3, e4, e5, e6, e7] :: rows rest
  | _ => []

theorem entries_length : ∀ l : List FieldElement51, (entries l).length = l.length / 3
  | [] | [_] | [_, _] => by simp [entries]
  | _ :: _ :: _ :: rest => by
    simp only [entries, List.length_cons, entries_length rest]
    omega

theorem entries_getElem! : ∀ (l : List FieldElement51) (k : ℕ), 3 * k + 2 < l.length →
    (entries l)[k]! =
      (⟨l[3 * k]!, l[3 * k + 1]!, l[3 * k + 2]!⟩ : AffineNielsPoint.«x86_64-tables»)
  | [], _, h | [_], _, h | [_, _], _, h =>
    absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | _ :: _ :: _ :: _, 0, _ => by simp [entries]
  | _ :: _ :: _ :: rest, k + 1, h => by
    have ih := entries_getElem! rest k (by simp only [List.length_cons] at h; omega)
    rw [show 3 * (k + 1) = 3 * k + 2 + 1 by ring]
    simpa only [entries, List.getElem!_cons_succ] using ih

theorem entriesProj_length : ∀ l : List FieldElement51, (entriesProj l).length = l.length / 4
  | [] | [_] | [_, _] | [_, _, _] => by simp [entriesProj]
  | _ :: _ :: _ :: _ :: rest => by
    simp only [entriesProj, List.length_cons, entriesProj_length rest]
    omega

theorem entriesProj_getElem! : ∀ (l : List FieldElement51) (k : ℕ), 4 * k + 3 < l.length →
    (entriesProj l)[k]! =
      (⟨l[4 * k]!, l[4 * k + 1]!, l[4 * k + 2]!, l[4 * k + 3]!⟩ :
        ProjectiveNielsPoint.«x86_64-tables»)
  | [], _, h | [_], _, h | [_, _], _, h | [_, _, _], _, h =>
    absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | _ :: _ :: _ :: _ :: _, 0, _ => by simp [entriesProj]
  | _ :: _ :: _ :: _ :: rest, k + 1, h => by
    have ih := entriesProj_getElem! rest k (by simp only [List.length_cons] at h; omega)
    rw [show 4 * (k + 1) = 4 * k + 3 + 1 by ring]
    simpa only [entriesProj, List.getElem!_cons_succ] using ih

theorem rows_length {T : Type} : ∀ l : List T, (rows l).length = l.length / 8
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
  | [_, _, _, _, _, _, _] => by simp [rows]
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest => by
    simp only [rows, List.length_cons, rows_length rest]
    omega

theorem rows_getElem!_getElem! {T : Type} [Inhabited T] :
    ∀ (l : List T) (i j : ℕ), 8 * i + 7 < l.length → j < 8 → ((rows l)[i]!)[j]! = l[8 * i + j]!
  | [], _, _, h, _ | [_], _, _, h, _ | [_, _], _, _, h, _ | [_, _, _], _, _, h, _
  | [_, _, _, _], _, _, h, _ | [_, _, _, _, _], _, _, h, _ | [_, _, _, _, _, _], _, _, h, _
  | [_, _, _, _, _, _, _], _, _, h, _ =>
    absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, 0, j, _, hj => by
    simp only [rows, List.getElem!_cons_zero, Array.getElem!_Nat_eq, Array.make_val, Nat.mul_zero,
      Nat.zero_add]
    interval_cases j <;> rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest, i + 1, j, h, hj => by
    have ih := rows_getElem!_getElem! rest i j (by simp only [List.length_cons] at h; omega) hj
    rw [show 8 * (i + 1) + j = 8 * i + j + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by ring]
    simpa only [rows, List.getElem!_cons_succ] using ih

/-! ### Limb bounds -/

/-- Every limb of every element of a list passing the bound check is `< 2^54`. -/
theorem limbs_lt_of_all {fes : List FieldElement51}
    (h : fes.all (fun a => a.val.all fun l => decide (l.val < 2 ^ 54)) = true) {k : ℕ}
    (hk : k < fes.length) : (fes[k]!).LimbsLt 54 := by
  rw [List.all_eq_true] at h
  have ha := h (fes[k]) (List.getElem_mem hk)
  rw [List.all_eq_true] at ha
  intro i hi
  have hlen : (fes[k]).val.length = 5 := by simp
  rw [getElem!_pos fes k hk, Array.getElem!_Nat_eq, getElem!_pos _ i (by omega)]
  simpa using ha _ (List.getElem_mem (by omega))

end Curve25519Dalek.TableCertificate
