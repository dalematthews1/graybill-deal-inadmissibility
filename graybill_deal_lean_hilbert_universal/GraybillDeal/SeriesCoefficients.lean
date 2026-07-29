import GraybillDeal.Coefficients
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp

/-!
# Derivation of the fixed-`n = 13` series coefficients

This file connects the coefficient sequence `q13` to the coefficients obtained
by multiplying the paired numerator polynomial by `(1 - z * x^2)⁻⁵` and then
using the moment recurrence

`M_m / M_(m+1) = (2m+15) / (2m+1)`.
-/

namespace GraybillDeal

private theorem cast_choose_two_poly (m : ℕ) :
    (Nat.choose m 2 : ℚ) =
      (m : ℚ) * ((m : ℚ) - 1) / 2 := by
  cases m with
  | zero => norm_num [Nat.choose]
  | succ m =>
      rw [Nat.cast_choose_two]

private theorem cast_choose_three_poly (m : ℕ) :
    (Nat.choose m 3 : ℚ) =
      (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) / 6 := by
  induction m with
  | zero => norm_num [Nat.choose]
  | succ m ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.cast_add, Nat.cast_succ]
      rw [cast_choose_two_poly, ih]
      ring

private theorem cast_choose_four_poly (m : ℕ) :
    (Nat.choose m 4 : ℚ) =
      (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) * ((m : ℚ) - 3) / 24 := by
  induction m with
  | zero => norm_num [Nat.choose]
  | succ m ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.cast_add, Nat.cast_succ]
      rw [cast_choose_three_poly, ih]
      ring

/--
The coefficient obtained directly from the paired polynomial and the
order-four negative-binomial coefficients, after applying the moment ratio.
-/
def rawQ13 (m : ℕ) : ℚ :=
  (4 / 11) * (Nat.choose (m + 4) 4 : ℚ)
    + (Nat.choose (m + 3) 4 : ℚ)
      * ((2 / 11) * ((2 * (m : ℚ) + 15) / (2 * (m : ℚ) + 1)) - 70 / 11)
    + (Nat.choose (m + 2) 4 : ℚ)
      * ((180 / 11) * ((2 * (m : ℚ) + 15) / (2 * (m : ℚ) + 1)) - 200 / 11)
    + (Nat.choose (m + 1) 4 : ℚ)
      * ((106 / 11) * ((2 * (m : ℚ) + 15) / (2 * (m : ℚ) + 1)) - 2)

@[simp]
theorem rawQ13_zero : rawQ13 0 = q13 0 := by
  norm_num [rawQ13, Nat.choose]

@[simp]
theorem rawQ13_one : rawQ13 1 = q13 1 := by
  norm_num [rawQ13, Nat.choose]

@[simp]
theorem rawQ13_two : rawQ13 2 = q13 2 := by
  norm_num [rawQ13, Nat.choose]

/-- The directly derived coefficients agree with the certified sequence. -/
theorem rawQ13_eq_q13 (m : ℕ) : rawQ13 m = q13 m := by
  rcases m with _ | m
  · exact rawQ13_zero
  rcases m with _ | m
  · exact rawQ13_one
  rcases m with _ | m
  · exact rawQ13_two
  simp only [q13]
  unfold rawQ13 gd13TailQ
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_ofNat]
  field_simp
  simp [Nat.choose]
  rw [cast_choose_two_poly, cast_choose_three_poly, cast_choose_four_poly]
  ring

end GraybillDeal
