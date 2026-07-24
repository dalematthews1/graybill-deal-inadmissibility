import GraybillDeal.Algebra

/-!
# Coefficients in the fixed-`n = 13` series certificate

This file packages the coefficient sequence in equations (9)--(10) of the
counterexample note. The derivation of the series expansion is deliberately
left to the later analytic module; here we certify the exact initial
coefficients and positivity of every tail coefficient.
-/

namespace GraybillDeal

/-- The coefficient sequence `Q_m` for the fixed-`n = 13` series. -/
def q13 : ℕ → ℚ
  | 0 => 4 / 11
  | 1 => -116 / 33
  | 2 => 232 / 11
  | m + 3 => gd13TailQ (m + 3)

@[simp]
theorem q13_zero : q13 0 = 4 / 11 := rfl

@[simp]
theorem q13_one : q13 1 = -116 / 33 := rfl

@[simp]
theorem q13_two : q13 2 = 232 / 11 := rfl

theorem q13_add_three_pos (m : ℕ) : 0 < q13 (m + 3) := by
  simp only [q13]
  exact gd13_tail_Q_pos (m + 3)

theorem q13_add_three_nonneg (m : ℕ) : 0 ≤ q13 (m + 3) :=
  (q13_add_three_pos m).le

/--
After substituting the exact moment ratios
`M₂ / M₁ = 3 / 17` and `M₃ / M₁ = 15 / 323`, the first three terms of the
series give exactly the quadratic used in the lower bound.
-/
theorem first_three_normalized_eq (z : ℝ) :
    (4 / 11 : ℝ)
        + (3 / 17) * (-116 / 33) * z
        + (15 / 323) * (232 / 11) * z ^ 2
      =
    (4 / 11 : ℝ) - (116 / 187) * z + (3480 / 3553) * z ^ 2 := by
  ring

theorem first_three_normalized_pos (z : ℝ) :
    0 <
      (4 / 11 : ℝ)
        + (3 / 17) * (-116 / 33) * z
        + (15 / 323) * (232 / 11) * z ^ 2 := by
  rw [first_three_normalized_eq]
  exact certificate_quadratic_pos z

end GraybillDeal
