import GraybillDeal.UnequalFixedDifferenceFourRealCollectedAlgebra

/-!
# Real-parameter linear bounds for the difference-four family

This module closes the one-sided linear analytic step by combining the exact
real-parameter coefficient normalization with the generic termwise-integration
theorem.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

/-- Concrete right-chart analytic integral for real `m`. -/
def unequalFixedDifferenceFourRealPlusAnalyticH
    (m s : ℝ) : ℝ :=
  unequalFixedDifferenceFourRealPlusH
    (unequalFixedDifferenceFourRealPlusDensity m) m s

/-- Concrete swapped-chart analytic integral for real `m`. -/
def unequalFixedDifferenceFourRealMinusAnalyticH
    (m s : ℝ) : ℝ :=
  unequalFixedDifferenceFourRealMinusH
    (unequalFixedDifferenceFourRealMinusDensity m) m s

/-- The right-chart analytic integral is uniformly bounded by the negative
pivot margin for every real `m ≥ 7`. -/
theorem unequalFixedDifferenceFourRealPlusAnalyticH_le_neg_b0
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourRealPlusAnalyticH m s
      ≤ -unequalFixedDifferenceFourRealB0 m := by
  unfold unequalFixedDifferenceFourRealPlusAnalyticH
  exact
    unequalFixedDifferenceFourRealPlusH_le_neg_b0_of_coefficient_identity
      (continuous_unequalFixedDifferenceFourRealPlusDensity hm)
      hm
      (unequalFixedDifferenceFourRealPlusIntegratedCoefficient_eq_coeff hm)
      hs0 hs1

/-- The swapped-chart analytic integral has the same uniform bound. -/
theorem unequalFixedDifferenceFourRealMinusAnalyticH_le_neg_b0
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourRealMinusAnalyticH m s
      ≤ -unequalFixedDifferenceFourRealB0 m := by
  unfold unequalFixedDifferenceFourRealMinusAnalyticH
  exact
    unequalFixedDifferenceFourRealMinusH_le_neg_b0_of_coefficient_identity
      (continuous_unequalFixedDifferenceFourRealMinusDensity hm)
      hm
      (unequalFixedDifferenceFourRealMinusIntegratedCoefficient_eq_coeff hm)
      hs0 hs1

end

end GraybillDeal
