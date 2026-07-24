import GraybillDeal.AnalyticKernel
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The geometric expansion of the paired denominator

For `|s| < 1` and `|x| ≤ 1`, the paired Graybill--Deal kernel has denominator
`(1 - s² x²)⁵`.  This file specializes Mathlib's binomial geometric-series
theorem to that denominator.
-/

namespace GraybillDeal

noncomputable section

theorem sq_mul_sq_norm_lt_one {s x : ℝ}
    (hs : |s| < 1) (hx : |x| ≤ 1) :
    ‖s ^ 2 * x ^ 2‖ < 1 := by
  have hs0 : 0 ≤ |s| := abs_nonneg s
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hs2 : |s| ^ 2 < 1 := by nlinarith [sq_nonneg (|s| - 1)]
  have hx2 : |x| ^ 2 ≤ 1 := by nlinarith [sq_nonneg (|x| - 1)]
  have hprod : |s| ^ 2 * |x| ^ 2 ≤ |s| ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg |s|) (sub_nonneg.mpr hx2)]
  simpa [Real.norm_eq_abs, abs_mul, abs_pow] using lt_of_le_of_lt hprod hs2

/-- The order-four binomial geometric series, written with real coefficients. -/
theorem hasSum_choose_four_mul_geometric {t : ℝ} (ht : ‖t‖ < 1) :
    HasSum
      (fun m : ℕ => ((m + 4).choose 4 : ℝ) * t ^ m)
      (1 / (1 - t) ^ 5) := by
  simpa using hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 4 ht

theorem summable_choose_four_mul_geometric {t : ℝ} (ht : ‖t‖ < 1) :
    Summable (fun m : ℕ => ((m + 4).choose 4 : ℝ) * t ^ m) :=
  (hasSum_choose_four_mul_geometric ht).summable

theorem tsum_choose_four_mul_geometric {t : ℝ} (ht : ‖t‖ < 1) :
    ∑' m : ℕ, ((m + 4).choose 4 : ℝ) * t ^ m
      = 1 / (1 - t) ^ 5 :=
  (hasSum_choose_four_mul_geometric ht).tsum_eq

/--
The exact expansion used for the denominator of the paired `n = 13` kernel.
-/
theorem hasSum_paired_denominator {s x : ℝ}
    (hs : |s| < 1) (hx : |x| ≤ 1) :
    HasSum
      (fun m : ℕ =>
        ((m + 4).choose 4 : ℝ) * (s ^ 2 * x ^ 2) ^ m)
      (1 / (1 - s ^ 2 * x ^ 2) ^ 5) :=
  hasSum_choose_four_mul_geometric (sq_mul_sq_norm_lt_one hs hx)

theorem tsum_paired_denominator {s x : ℝ}
    (hs : |s| < 1) (hx : |x| ≤ 1) :
    ∑' m : ℕ,
        ((m + 4).choose 4 : ℝ) * (s ^ 2 * x ^ 2) ^ m
      =
    1 / (1 - s ^ 2 * x ^ 2) ^ 5 :=
  (hasSum_paired_denominator hs hx).tsum_eq

end

end GraybillDeal
