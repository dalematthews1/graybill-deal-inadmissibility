import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebraic core of the `n = 13` Graybill--Deal certificate

This file isolates exact rational and polynomial inequalities used by the
proposed inadmissibility certificate. It deliberately does not yet formalize
the probability-theoretic reduction or the integral/series argument.
-/

namespace GraybillDeal

/-- The proposed perturbation is smaller than the certified uniform bound. -/
theorem epsilon_lt_uniform_bound :
    (1 / 2000 : ℚ) < 23824 / 40585545 := by
  norm_num

/--
The finite arithmetic obligation in the ratio-free version of the risk
certificate. Here `1696 / 165` is the upper bound for the quadratic term,
`1024 / 45045` is the required beta moment, and `1489 / 5610` is the
completed-square lower bound.
-/
theorem epsilon_times_quadratic_bound_lt_linear_bound :
    (1 / 2000 : ℚ) * (1696 / 165)
      < (1024 / 45045) * (1489 / 5610) := by
  norm_num

/-- Completing the square gives the exact lower bound used in the note. -/
theorem certificate_quadratic_eq (z : ℝ) :
    (4 / 11 : ℝ) - (116 / 187) * z + (3480 / 3553) * z ^ 2
      =
    1489 / 5610 + (3480 / 3553) * (z - 19 / 60) ^ 2 := by
  ring

theorem certificate_quadratic_pos (z : ℝ) :
    0 <
      (4 / 11 : ℝ) - (116 / 187) * z + (3480 / 3553) * z ^ 2 := by
  rw [certificate_quadratic_eq]
  positivity

theorem certificate_minimum_pos : (0 : ℚ) < 1489 / 5610 := by
  norm_num

/--
The numerator on the right side of formula (10) is positive. The strictly
positive constant term makes the inequality independent of `m`.
-/
theorem gd13_tail_numerator_pos (m : ℕ) :
    0 <
      (8232 : ℚ)
        + 20148 * (Nat.choose (m - 3) 1 : ℚ)
        + 23236 * (Nat.choose (m - 3) 2 : ℚ)
        + 13040 * (Nat.choose (m - 3) 3 : ℚ)
        + 2880 * (Nat.choose (m - 3) 4 : ℚ) := by
  have h1 : (0 : ℚ) ≤ (Nat.choose (m - 3) 1 : ℚ) := by positivity
  have h2 : (0 : ℚ) ≤ (Nat.choose (m - 3) 2 : ℚ) := by positivity
  have h3 : (0 : ℚ) ≤ (Nat.choose (m - 3) 3 : ℚ) := by positivity
  have h4 : (0 : ℚ) ≤ (Nat.choose (m - 3) 4 : ℚ) := by positivity
  linarith

def gd13TailQ (m : ℕ) : ℚ :=
  ((8232 : ℚ)
      + 20148 * Nat.choose (m - 3) 1
      + 23236 * Nat.choose (m - 3) 2
      + 13040 * Nat.choose (m - 3) 3
      + 2880 * Nat.choose (m - 3) 4)
    / (11 * (2 * m + 1))

theorem gd13_tail_Q_pos (m : ℕ) : 0 < gd13TailQ m := by
  unfold gd13TailQ
  apply div_pos
  · exact gd13_tail_numerator_pos m
  · positivity

/-!
The next five lemmas certify positivity of the general-`ν` tail
coefficients after multiplication by `4(ν - 1)`.
-/

theorem tail_D0_pos (ν : ℝ) (hν : 8 ≤ ν) :
    0 < 308 * ν ^ 2 - 896 * ν - 672 := by
  nlinarith [sq_nonneg (ν - 8)]

theorem tail_D1_pos (ν : ℝ) (hν : 8 ≤ ν) :
    0 < 712 * ν ^ 2 - 1774 * ν - 648 := by
  nlinarith [sq_nonneg (ν - 8)]

theorem tail_D2_pos (ν : ℝ) (hν : 8 ≤ ν) :
    0 < 798 * ν ^ 2 - 1804 * ν - 320 := by
  nlinarith [sq_nonneg (ν - 8)]

theorem tail_D3_pos (ν : ℝ) (hν : 8 ≤ ν) :
    0 < 440 * ν ^ 2 - 928 * ν - 64 := by
  nlinarith [sq_nonneg (ν - 8)]

theorem tail_D4_pos (ν : ℝ) (hν : 8 ≤ ν) :
    0 < 96 * ν ^ 2 - 192 * ν := by
  nlinarith

theorem general_Q2_pos (ν : ℝ) (hν : 8 ≤ ν) :
    0 < (5 * ν ^ 2 - 19 * ν - 28) / (2 * (ν - 1)) := by
  apply div_pos
  · nlinarith [sq_nonneg (ν - 8)]
  · nlinarith

end GraybillDeal
