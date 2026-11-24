module
public import Mathlib.Data.ZMod.Basic
public section

/-! # Lemmas about `ZMod` -/

namespace ZMod

theorem natCast_eq_natCast_of_mod_eq {n x y : ℕ} (h : x % n = y) : (x : ZMod n) = y := by
  rw [← natCast_mod, h]

theorem eq_val_of_natCast_eq {n x : ℕ} {X : ZMod n} (hx : x < n) (h : (x : ZMod n) = X) :
    x = X.val := by
  rw [← h, val_natCast_of_lt hx]

theorem natCast_eq_zero_iff_mod {n a : ℕ} : (a : ZMod n) = 0 ↔ a % n = 0 := by
  rw [natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

end ZMod
