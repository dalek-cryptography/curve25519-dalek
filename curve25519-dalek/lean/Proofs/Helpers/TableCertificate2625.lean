/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Proofs.Helpers.TableCertificate
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField2625
import Proofs.Helpers.FieldElement2625
import Mathlib.Tactic.LinearCombination
public section

/-! # Certifying the precomputed tables (u32 backend)

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
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.TableCertificate2625

open Curve25519Dalek.TableCertificate

/-! ### The bind chain -/

theorem bind_from_limbs {β : Type} (a : FieldElement2625) (f : FieldElement2625 → Result β) :
    Aeneas.Std.bind (FieldElement2625.from_limbs a) f = f a := by
  unfold FieldElement2625.from_limbs
  simp

/-- The shape of a translated table constant: a chain of `from_limbs` binds, then a value built
from the field elements. -/
@[expose] def bindList {β : Type} :
    List FieldElement2625 → (List FieldElement2625 → Result β) → Result β
  | [], k => k []
  | l :: xs, k =>
    Aeneas.Std.bind (FieldElement2625.from_limbs l) fun fe => bindList xs fun fes => k (fe :: fes)

theorem bindList_eq {β : Type} (xs : List FieldElement2625)
    (k : List FieldElement2625 → Result β) : bindList xs k = k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons l xs ih => simp only [bindList, bind_from_limbs, ih]

/-- `collect_limbs xs from c` defines `xs : List FieldElement2625` as the limb arrays of the
`from_limbs` bind chain of the translated constant `c`, in order. -/
syntax (name := collectLimbs2625) "collect_limbs_u32 " ident " from " ident : command

elab_rules : command
  | `(collect_limbs_u32 $n:ident from $c:ident) => liftTermElabM do
  let cn ← realizeGlobalConstNoOverloadWithInfo c
  let some body ← withTransparency .all (unfoldDefinition? (mkConst cn))
    | throwError "collect_limbs_u32: cannot unfold {cn}"
  let mut e := body
  let mut xs : Array Expr := #[]
  while e.isAppOfArity ``Aeneas.Std.bind 4 do
    let #[_, _, x, f] := e.getAppArgs | unreachable!
    unless x.isAppOfArity
        ``Curve25519Dalek.backend.serial.u32.field.FieldElement2625.from_limbs 1 do
      throwError "collect_limbs_u32: a bind of {x.getAppFn}, not of from_limbs"
    let a := x.appArg!
    if a.hasLooseBVars then throwError "collect_limbs_u32: a limb array depends on earlier binds"
    xs := xs.push a
    e := f.bindingBody!
  unless e.isAppOfArity ``Aeneas.Std.Result.ok 2 do
    throwError "collect_limbs_u32: the chain ends in {e.getAppFn}, not in ok"
  let ty := mkConst ``Curve25519Dalek.backend.serial.u32.field.FieldElement2625
  let lst ← mkListLit ty xs.toList
  addDecl <| .defnDecl (mkDefinitionValEx n.getId [] (← inferType lst) lst .abbrev .safe [])
  addDocStringCore n.getId s!"The limb arrays of `{cn}`, in order (`collect_limbs_u32`)."

/-! ### Limbs as numbers -/

/-- The value of ten radix-`2^25.5` limbs (`asNat`, in a form the kernel evaluates). -/
@[expose] def limbsNat (a : FieldElement2625) : ℕ :=
  match a.val with
  | [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9] =>
    l0.val + l1.val * 2 ^ 26 + l2.val * 2 ^ 51 + l3.val * 2 ^ 77 + l4.val * 2 ^ 102 +
      l5.val * 2 ^ 128 + l6.val * 2 ^ 153 + l7.val * 2 ^ 179 + l8.val * 2 ^ 204 + l9.val * 2 ^ 230
  | _ => 0

theorem limbsNat_eq_asNat (a : FieldElement2625) : limbsNat a = a.asNat := by
  rw [asNat_expand]
  have hl : a.val.length = 10 := by simp
  match h : a.val, hl with
  | [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9], _ =>
    simp only [limbsNat, h, Array.getElem!_Nat_eq, List.getElem!_cons_zero,
      List.getElem!_cons_succ]
    ring

/-! ### The checker -/

variable (E : TwistedEdwardsModel (ZMod p))

/-- `Q = (X : Y : Z : T)` is the point with affine Niels limbs `(y + x, y - x, 2 d x y)`:
`2 X = (a - b) Z`, `2 Y = (a + b) Z` and `c Z² = 2 d X Y`. -/
@[expose] noncomputable def checkEntry (Q : E.Extended) (ya yb c : FieldElement2625) : Bool :=
  let a : ZMod p := limbsNat ya
  let b : ZMod p := limbsNat yb
  let c' : ZMod p := limbsNat c
  decide (2 * Q.X = (a - b) * Q.Z ∧ 2 * Q.Y = (a + b) * Q.Z ∧
    c' * Q.Z * Q.Z = 2 * E.d * Q.X * Q.Y)

/-- The entries of `l` (three limb arrays each) are `Q, Q + S, Q + 2 S, …`. -/
@[expose] noncomputable def checkRow (S : E.Extended) : E.Extended → List FieldElement2625 → Bool
  | _, [] => true
  | Q, ya :: yb :: c :: rest => checkEntry E Q ya yb c && checkRow S (Q.add S) rest
  | _, _ => false

/-- The rows of `fes` (24 limb arrays each) are the lookup tables of `P, 2^8 P, 2^16 P, …`. -/
@[expose] noncomputable def checkTable : E.Extended → List FieldElement2625 → ℕ → Bool
  | _, fes, 0 => fes.isEmpty
  | P, fes, n + 1 => checkRow E P P (fes.take 24) && checkTable (pow2 E 8 P) (fes.drop 24) n

/-! ### Soundness -/

/-- An entry passing `checkEntry` against `Q` on the curve represents `Q`. -/
theorem checkEntry_sound {Q : edwards.Extended} (hQ : Q.OnCurve) {ya yb c : FieldElement2625}
    (h : checkEntry edwards Q ya yb c = true) :
    (⟨ya, yb, c⟩ : AffineNielsPoint.«i686-tables»).OnCurve ∧
      (⟨ya, yb, c⟩ : AffineNielsPoint.«i686-tables»).toPoint = Q.toPoint := by
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
  have hx' : (⟨ya, yb, c⟩ : AffineNielsPoint.«i686-tables»).toAffineNiels.x = x := by
    rw [AffineNielsPoint.«i686-tables».toAffineNiels_x]
    simp only
    rw [ha, hb, show y + x - (y - x) = 2 * x by ring, mul_div_cancel_left₀ x two_ne_zero']
  have hy' : (⟨ya, yb, c⟩ : AffineNielsPoint.«i686-tables»).toAffineNiels.y = y := by
    rw [AffineNielsPoint.«i686-tables».toAffineNiels_y]
    simp only
    rw [ha, hb, show y + x + (y - x) = 2 * y by ring, mul_div_cancel_left₀ y two_ne_zero']
  have hon : (⟨ya, yb, c⟩ : AffineNielsPoint.«i686-tables»).OnCurve := by
    rw [AffineNielsPoint.«i686-tables».onCurve_iff_equation, hx', hy']
    exact ⟨Q.toPoint.equation, hc⟩
  refine ⟨hon, Point.ext ?_ ?_⟩
  · rw [AffineNielsPoint.«i686-tables».toPoint_x hon, hx']
  · rw [AffineNielsPoint.«i686-tables».toPoint_y hon, hy']

/-- Entry `j` of a list passing `checkRow S Q` represents `Q + j • S`. -/
theorem checkRow_sound {S : edwards.Extended} (hS : S.OnCurve) :
    ∀ {Q : edwards.Extended} {l : List FieldElement2625}, Q.OnCurve →
      checkRow edwards S Q l = true → ∀ j, 3 * j + 2 < l.length →
      (⟨l[3 * j]!, l[3 * j + 1]!, l[3 * j + 2]!⟩ : AffineNielsPoint.«i686-tables»).OnCurve ∧
        (⟨l[3 * j]!, l[3 * j + 1]!, l[3 * j + 2]!⟩ :
          AffineNielsPoint.«i686-tables»).toPoint = Q.toPoint + j • S.toPoint
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

theorem getElem!_take_of_lt {l : List FieldElement2625} {n i : ℕ} (h : i < n) :
    (l.take n)[i]! = l[i]! := by
  simp [List.getElem!_eq_getElem?_getD, h]

theorem getElem!_drop (l : List FieldElement2625) (n i : ℕ) : (l.drop n)[i]! = l[n + i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop]

/-- Entry `j` of row `i` of a list passing `checkTable P · n` represents
`(j + 1) • 2^(8 i) • P`. -/
theorem checkTable_sound :
    ∀ {n : ℕ} {P : edwards.Extended} {fes : List FieldElement2625}, P.OnCurve →
      checkTable edwards P fes n = true → fes.length = 24 * n → ∀ i < n, ∀ j : ℕ, j < 8 →
      (⟨fes[24 * i + 3 * j]!, fes[24 * i + 3 * j + 1]!, fes[24 * i + 3 * j + 2]!⟩ :
        AffineNielsPoint.«i686-tables»).OnCurve ∧
      (⟨fes[24 * i + 3 * j]!, fes[24 * i + 3 * j + 1]!, fes[24 * i + 3 * j + 2]!⟩ :
        AffineNielsPoint.«i686-tables»).toPoint = (j + 1) • 2 ^ (8 * i) • P.toPoint
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
@[expose] noncomputable def checkEntryProj (Q : E.Extended) (ya yb z t : FieldElement2625) : Bool :=
  let a : ZMod p := limbsNat ya
  let b : ZMod p := limbsNat yb
  let z' : ZMod p := limbsNat z
  let t' : ZMod p := limbsNat t
  decide (z' ≠ 0 ∧ 2 * Q.X * z' = (a - b) * Q.Z ∧ 2 * Q.Y * z' = (a + b) * Q.Z ∧
    2 * t' * z' = E.d * (a - b) * (a + b))

/-- The entries of `l` (four limb arrays each) are `Q, Q + S, Q + 2 S, …`. -/
@[expose] noncomputable def checkRowProj (S : E.Extended) :
    E.Extended → List FieldElement2625 → Bool
  | _, [] => true
  | Q, ya :: yb :: z :: t :: rest =>
    checkEntryProj E Q ya yb z t && checkRowProj S (Q.add S) rest
  | _, _ => false

/-- An entry passing `checkEntryProj` against `Q` on the curve represents `Q`. -/
theorem checkEntryProj_sound {Q : edwards.Extended} (hQ : Q.OnCurve)
    {ya yb z t : FieldElement2625} (h : checkEntryProj edwards Q ya yb z t = true) :
    (⟨ya, yb, z, t⟩ : ProjectiveNielsPoint.«i686-tables»).OnCurve ∧
      (⟨ya, yb, z, t⟩ : ProjectiveNielsPoint.«i686-tables»).toPoint = Q.toPoint := by
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
  have hX' : (⟨ya, yb, z, t⟩ : ProjectiveNielsPoint.«i686-tables»).toProjectiveNiels.X =
      x * z.toField := by
    rw [ProjectiveNielsPoint.«i686-tables».toProjectiveNiels_X]
    simp only
    rw [ha, hb, show (y + x) * z.toField - (y - x) * z.toField = 2 * (x * z.toField) by ring,
      mul_div_cancel_left₀ _ two_ne_zero']
  have hY' : (⟨ya, yb, z, t⟩ : ProjectiveNielsPoint.«i686-tables»).toProjectiveNiels.Y =
      y * z.toField := by
    rw [ProjectiveNielsPoint.«i686-tables».toProjectiveNiels_Y]
    simp only
    rw [ha, hb, show (y + x) * z.toField + (y - x) * z.toField = 2 * (y * z.toField) by ring,
      mul_div_cancel_left₀ _ two_ne_zero']
  have ht : t.toField * z.toField = 2 * d * (x * z.toField) * (y * z.toField) := by
    refine mul_left_cancel₀ two_ne_zero' ?_
    rw [ha, hb, edwards_d] at h3
    linear_combination h3
  have hon : (⟨ya, yb, z, t⟩ : ProjectiveNielsPoint.«i686-tables»).OnCurve := by
    rw [ProjectiveNielsPoint.«i686-tables».onCurve_iff_equation, hX', hY']
    refine ⟨hz, ?_, ht⟩
    rw [mul_div_cancel_right₀ x hz, mul_div_cancel_right₀ y hz]
    exact Q.toPoint.equation
  refine ⟨hon, Point.ext ?_ ?_⟩
  · rw [ProjectiveNielsPoint.«i686-tables».toPoint_x hon, hX']
    exact mul_div_cancel_right₀ x hz
  · rw [ProjectiveNielsPoint.«i686-tables».toPoint_y hon, hY']
    exact mul_div_cancel_right₀ y hz

/-- Entry `k` of a list passing `checkRowProj S Q` represents `Q + k • S`. -/
theorem checkRowProj_sound {S : edwards.Extended} (hS : S.OnCurve) :
    ∀ {Q : edwards.Extended} {l : List FieldElement2625}, Q.OnCurve →
      checkRowProj edwards S Q l = true → ∀ k, 4 * k + 3 < l.length →
      (⟨l[4 * k]!, l[4 * k + 1]!, l[4 * k + 2]!, l[4 * k + 3]!⟩ :
        ProjectiveNielsPoint.«i686-tables»).OnCurve ∧
        (⟨l[4 * k]!, l[4 * k + 1]!, l[4 * k + 2]!, l[4 * k + 3]!⟩ :
          ProjectiveNielsPoint.«i686-tables»).toPoint = Q.toPoint + k • S.toPoint
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

/-! ### Single points -/

/-! ### Tables from flat lists

The constructors consume the list sequentially, so that the kernel compares `mk fes` with the
translated structure in linear time (indexing into `fes` there cost 8 s for 768 elements). The
index lemmas serve the proofs. -/

/-- Affine Niels entries, three limb arrays each. -/
@[expose] def entries : List FieldElement2625 → List AffineNielsPoint.«i686-tables»
  | ya :: yb :: c :: rest => ⟨ya, yb, c⟩ :: entries rest
  | _ => []

/-- Projective Niels entries, four limb arrays each. -/
@[expose] def entriesProj : List FieldElement2625 → List ProjectiveNielsPoint.«i686-tables»
  | ya :: yb :: z :: t :: rest => ⟨ya, yb, z, t⟩ :: entriesProj rest
  | _ => []

theorem entries_length : ∀ l : List FieldElement2625, (entries l).length = l.length / 3
  | [] | [_] | [_, _] => by simp [entries]
  | _ :: _ :: _ :: rest => by
    simp only [entries, List.length_cons, entries_length rest]
    omega

theorem entries_getElem! : ∀ (l : List FieldElement2625) (k : ℕ), 3 * k + 2 < l.length →
    (entries l)[k]! =
      (⟨l[3 * k]!, l[3 * k + 1]!, l[3 * k + 2]!⟩ : AffineNielsPoint.«i686-tables»)
  | [], _, h | [_], _, h | [_, _], _, h =>
    absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | _ :: _ :: _ :: _, 0, _ => by simp [entries]
  | _ :: _ :: _ :: rest, k + 1, h => by
    have ih := entries_getElem! rest k (by simp only [List.length_cons] at h; omega)
    rw [show 3 * (k + 1) = 3 * k + 2 + 1 by ring]
    simpa only [entries, List.getElem!_cons_succ] using ih

theorem entriesProj_length : ∀ l : List FieldElement2625, (entriesProj l).length = l.length / 4
  | [] | [_] | [_, _] | [_, _, _] => by simp [entriesProj]
  | _ :: _ :: _ :: _ :: rest => by
    simp only [entriesProj, List.length_cons, entriesProj_length rest]
    omega

theorem entriesProj_getElem! : ∀ (l : List FieldElement2625) (k : ℕ), 4 * k + 3 < l.length →
    (entriesProj l)[k]! =
      (⟨l[4 * k]!, l[4 * k + 1]!, l[4 * k + 2]!, l[4 * k + 3]!⟩ :
        ProjectiveNielsPoint.«i686-tables»)
  | [], _, h | [_], _, h | [_, _], _, h | [_, _, _], _, h =>
    absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  | _ :: _ :: _ :: _ :: _, 0, _ => by simp [entriesProj]
  | _ :: _ :: _ :: _ :: rest, k + 1, h => by
    have ih := entriesProj_getElem! rest k (by simp only [List.length_cons] at h; omega)
    rw [show 4 * (k + 1) = 4 * k + 3 + 1 by ring]
    simpa only [entriesProj, List.getElem!_cons_succ] using ih

/-! ### Limb bounds -/

/-- Every limb of every element of a list passing the bound check is `< 2^27`. -/
theorem limbs_lt_of_all {fes : List FieldElement2625}
    (h : fes.all (fun a => a.val.all fun l => decide (l.val < 2 ^ 27)) = true) {k : ℕ}
    (hk : k < fes.length) : (fes[k]!).LimbsLt 27 := by
  rw [List.all_eq_true] at h
  have ha := h (fes[k]) (List.getElem_mem hk)
  rw [List.all_eq_true] at ha
  intro i hi
  have hlen : (fes[k]).val.length = 10 := by simp
  rw [getElem!_pos fes k hk, Array.getElem!_Nat_eq, getElem!_pos _ i (by omega)]
  simpa using ha _ (List.getElem_mem (by omega))

end Curve25519Dalek.TableCertificate2625
