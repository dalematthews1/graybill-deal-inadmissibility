import GraybillDeal.UnequalFixedDifferenceFourRealLinearBounds
import GraybillDeal.UnequalFixedDifferenceFourRealEnvelopeIntegrals

/-!
# Real-parameter reduced analytic certificate for the difference-four family

This module assembles the two one-sided analytic charts for every real
parameter `m ≥ 7`.

The linear coefficients are the positive chart prefactors times the concrete
beta-density integrals from `UnequalFixedDifferenceFourRealLinearBounds`.
The quadratic coefficients are the corresponding beta expectations from
`UnequalFixedDifferenceFourRealEnvelopeIntegrals`.  Both charts use the same
fixed perturbation size `unequalFixedDifferenceFourRealEpsilon m`.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

/-! ## Concrete chart quantities -/

/-- The real-parameter right-chart reduced linear coefficient. -/
def unequalFixedDifferenceFourRealPlusB (m s : ℝ) : ℝ :=
  (1 - s) ^ 2 / (1 - unequalFixedDifferenceFourRealQ m * s)
    * unequalFixedDifferenceFourRealPlusAnalyticH m s

/-- The real-parameter sample-swapped reduced linear coefficient. -/
def unequalFixedDifferenceFourRealMinusB (m s : ℝ) : ℝ :=
  (1 - s) ^ 2 / (1 - unequalFixedDifferenceFourRealT m * s)
    * unequalFixedDifferenceFourRealMinusAnalyticH m s

/-- The real-parameter right-chart reduced quadratic coefficient. -/
def unequalFixedDifferenceFourRealPlusC (m s : ℝ) : ℝ :=
  ∫ y, unequalFixedDifferenceFourRealPlusCIntegrand m s y
    ∂betaMeasure (m + 1) (m - 1)

/-- The real-parameter sample-swapped reduced quadratic coefficient. -/
def unequalFixedDifferenceFourRealMinusC (m s : ℝ) : ℝ :=
  ∫ y, unequalFixedDifferenceFourRealMinusCIntegrand m s y
    ∂betaMeasure (m - 1) (m + 1)

/-! ## Positive one-sided prefactors -/

private theorem unequalFD4Real_oneSided_prefactor_nonneg
    {q s : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    0 ≤ (1 - s) ^ 2 / (1 - q * s) := by
  exact div_nonneg (sq_nonneg _)
    (one_sub_qs_pos hq0 hq1 hs0 hs1).le

private theorem unequalFD4Real_neg_b0_prefactor_le
    {m : ℝ} (hm : 7 ≤ m)
    {q s : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (1 - s) ^ 2 / (1 - q * s)
          * (-unequalFixedDifferenceFourRealB0 m)
      ≤
    -unequalFixedDifferenceFourRealB0 m * (1 - s) ^ 2 := by
  have hdpos : 0 < 1 - q * s :=
    one_sub_qs_pos hq0 hq1 hs0 hs1
  have hdle : 1 - q * s ≤ 1 := by
    have hqs : 0 ≤ q * s := mul_nonneg hq0 hs0
    linarith
  have hnum :
      0 ≤ unequalFixedDifferenceFourRealB0 m * (1 - s) ^ 2 :=
    mul_nonneg (unequalFixedDifferenceFourRealB0_pos hm).le
      (sq_nonneg _)
  have hdiv :
      unequalFixedDifferenceFourRealB0 m * (1 - s) ^ 2
        ≤
      unequalFixedDifferenceFourRealB0 m * (1 - s) ^ 2
        / (1 - q * s) := by
    apply (le_div_iff₀ hdpos).2
    calc
      unequalFixedDifferenceFourRealB0 m * (1 - s) ^ 2
            * (1 - q * s)
          ≤
        unequalFixedDifferenceFourRealB0 m * (1 - s) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hdle hnum
      _ = unequalFixedDifferenceFourRealB0 m * (1 - s) ^ 2 := by
        ring
  calc
    (1 - s) ^ 2 / (1 - q * s)
          * (-unequalFixedDifferenceFourRealB0 m)
        =
      -(unequalFixedDifferenceFourRealB0 m * (1 - s) ^ 2
          / (1 - q * s)) := by
            ring
    _ ≤ -(unequalFixedDifferenceFourRealB0 m * (1 - s) ^ 2) :=
      neg_le_neg hdiv
    _ = -unequalFixedDifferenceFourRealB0 m * (1 - s) ^ 2 := by
      ring

/-! ## Linear bounds after restoring the chart prefactors -/

/-- Uniform real-parameter right-chart linear bound. -/
theorem unequalFixedDifferenceFourRealPlusB_le
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourRealPlusB m s
      ≤ -unequalFixedDifferenceFourRealB0 m * (1 - s) ^ 2 := by
  have hH :=
    unequalFixedDifferenceFourRealPlusAnalyticH_le_neg_b0
      hm hs0 hs1
  unfold unequalFixedDifferenceFourRealPlusB
  calc
    (1 - s) ^ 2
          / (1 - unequalFixedDifferenceFourRealQ m * s)
          * unequalFixedDifferenceFourRealPlusAnalyticH m s
        ≤
      (1 - s) ^ 2
          / (1 - unequalFixedDifferenceFourRealQ m * s)
          * (-unequalFixedDifferenceFourRealB0 m) := by
            exact mul_le_mul_of_nonneg_left hH
              (unequalFD4Real_oneSided_prefactor_nonneg
                (unequalFixedDifferenceFourRealQ_pos hm).le
                (unequalFixedDifferenceFourRealQ_le_one hm)
                hs0 hs1)
    _ ≤ -unequalFixedDifferenceFourRealB0 m * (1 - s) ^ 2 :=
      unequalFD4Real_neg_b0_prefactor_le hm
        (unequalFixedDifferenceFourRealQ_pos hm).le
        (unequalFixedDifferenceFourRealQ_le_one hm)
        hs0 hs1

/-- Uniform real-parameter sample-swapped linear bound. -/
theorem unequalFixedDifferenceFourRealMinusB_le
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourRealMinusB m s
      ≤ -unequalFixedDifferenceFourRealB0 m * (1 - s) ^ 2 := by
  have hH :=
    unequalFixedDifferenceFourRealMinusAnalyticH_le_neg_b0
      hm hs0 hs1
  unfold unequalFixedDifferenceFourRealMinusB
  calc
    (1 - s) ^ 2
          / (1 - unequalFixedDifferenceFourRealT m * s)
          * unequalFixedDifferenceFourRealMinusAnalyticH m s
        ≤
      (1 - s) ^ 2
          / (1 - unequalFixedDifferenceFourRealT m * s)
          * (-unequalFixedDifferenceFourRealB0 m) := by
            exact mul_le_mul_of_nonneg_left hH
              (unequalFD4Real_oneSided_prefactor_nonneg
                (unequalFixedDifferenceFourRealT_pos hm).le
                (unequalFixedDifferenceFourRealT_le_one hm)
                hs0 hs1)
    _ ≤ -unequalFixedDifferenceFourRealB0 m * (1 - s) ^ 2 :=
      unequalFD4Real_neg_b0_prefactor_le hm
        (unequalFixedDifferenceFourRealT_pos hm).le
        (unequalFixedDifferenceFourRealT_le_one hm)
        hs0 hs1

/-! ## Quadratic bounds -/

/-- Uniform real-parameter right-chart quadratic bound. -/
theorem unequalFixedDifferenceFourRealPlusC_le
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourRealPlusC m s
      ≤ unequalFixedDifferenceFourRealMPlus m * (1 - s) ^ 2 := by
  simpa only [unequalFixedDifferenceFourRealPlusC] using
    (integral_unequalFixedDifferenceFourRealPlusC_le hm hs0 hs1)

/-- Uniform real-parameter swapped-chart quadratic bound, enlarged to the
common right-chart envelope constant. -/
theorem unequalFixedDifferenceFourRealMinusC_le
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourRealMinusC m s
      ≤ unequalFixedDifferenceFourRealMPlus m * (1 - s) ^ 2 := by
  simpa only [unequalFixedDifferenceFourRealMinusC] using
    (integral_unequalFixedDifferenceFourRealMinusC_le hm hs0 hs1)

/-! ## Fixed-epsilon reduced-risk inequalities -/

/-- The real-parameter family perturbation has strictly negative reduced risk
on the right chart. -/
theorem unequalFixedDifferenceFourRealPlusReducedRisk_neg
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    2 * unequalFixedDifferenceFourRealEpsilon m
          * unequalFixedDifferenceFourRealPlusB m s
        + unequalFixedDifferenceFourRealEpsilon m ^ 2
          * unequalFixedDifferenceFourRealPlusC m s
      < 0 := by
  exact unequalFixedDifferenceFourReal_reducedRisk_neg_of_bounds
    hm hs1
    (unequalFixedDifferenceFourRealPlusB_le hm hs0 hs1)
    (unequalFixedDifferenceFourRealPlusC_le hm hs0 hs1)

/-- The same fixed perturbation has strictly negative reduced risk on the
sample-swapped chart. -/
theorem unequalFixedDifferenceFourRealMinusReducedRisk_neg
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    2 * unequalFixedDifferenceFourRealEpsilon m
          * unequalFixedDifferenceFourRealMinusB m s
        + unequalFixedDifferenceFourRealEpsilon m ^ 2
          * unequalFixedDifferenceFourRealMinusC m s
      < 0 := by
  exact unequalFixedDifferenceFourReal_reducedRisk_neg_of_bounds
    hm hs1
    (unequalFixedDifferenceFourRealMinusB_le hm hs0 hs1)
    (unequalFixedDifferenceFourRealMinusC_le hm hs0 hs1)

end

end GraybillDeal
