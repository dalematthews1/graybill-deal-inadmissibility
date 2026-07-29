import GraybillDeal.UnequalFixedDifferenceFourCollectedAlgebra
import GraybillDeal.UnequalFixedDifferenceFourEnvelopeIntegrals

/-!
# Reduced analytic certificate for the fixed-difference-four family

This module assembles the two one-sided analytic charts for

`(n₁, n₂) = (2m - 1, 2m + 3)`, `m ≥ 7`.

The linear coefficients are the positive chart prefactors times the
concrete beta-density integrals obtained from the series bridge.  The
quadratic coefficients are the corresponding beta expectations of the
two family `C` integrands.  Both sides use the same fixed perturbation
size `unequalFixedDifferenceFourEpsilon m`.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

/-! ## Concrete chart quantities -/

/-- The concrete right-chart analytic integral. -/
def unequalFixedDifferenceFourPlusAnalyticH
    (m : ℕ) (s : ℝ) : ℝ :=
  unequalFixedDifferenceFourPlusH
    (unequalFixedDifferenceFourPlusDensity m) m s

/-- The concrete sample-swapped analytic integral. -/
def unequalFixedDifferenceFourMinusAnalyticH
    (m : ℕ) (s : ℝ) : ℝ :=
  unequalFixedDifferenceFourMinusH
    (unequalFixedDifferenceFourMinusDensity m) m s

/-- The right-chart reduced linear coefficient. -/
def unequalFixedDifferenceFourPlusB
    (m : ℕ) (s : ℝ) : ℝ :=
  (1 - s) ^ 2
      / (1 - unequalFixedDifferenceFourQ m * s)
    * unequalFixedDifferenceFourPlusAnalyticH m s

/-- The sample-swapped reduced linear coefficient. -/
def unequalFixedDifferenceFourMinusB
    (m : ℕ) (s : ℝ) : ℝ :=
  (1 - s) ^ 2
      / (1 - unequalFixedDifferenceFourT m * s)
    * unequalFixedDifferenceFourMinusAnalyticH m s

/-- The right-chart reduced quadratic coefficient. -/
def unequalFixedDifferenceFourPlusC
    (m : ℕ) (s : ℝ) : ℝ :=
  ∫ y, unequalFixedDifferenceFourPlusCIntegrand m s y
    ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1)

/-- The sample-swapped reduced quadratic coefficient. -/
def unequalFixedDifferenceFourMinusC
    (m : ℕ) (s : ℝ) : ℝ :=
  ∫ y, unequalFixedDifferenceFourMinusCIntegrand m s y
    ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1)

/-! ## Generic prefactor lemmas -/

private theorem unequalFD4_oneSided_prefactor_nonneg
    {q s : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    0 ≤ (1 - s) ^ 2 / (1 - q * s) := by
  exact div_nonneg (sq_nonneg _)
    (one_sub_qs_pos hq0 hq1 hs0 hs1).le

private theorem unequalFD4_neg_b0_prefactor_le
    {m : ℕ} (hm : 7 ≤ m)
    {q s : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (1 - s) ^ 2 / (1 - q * s)
          * (-unequalFixedDifferenceFourB0 m)
      ≤
    -unequalFixedDifferenceFourB0 m * (1 - s) ^ 2 := by
  have hdpos : 0 < 1 - q * s :=
    one_sub_qs_pos hq0 hq1 hs0 hs1
  have hdle : 1 - q * s ≤ 1 := by
    have hqs : 0 ≤ q * s := mul_nonneg hq0 hs0
    linarith
  have hnum :
      0 ≤ unequalFixedDifferenceFourB0 m * (1 - s) ^ 2 :=
    mul_nonneg (unequalFixedDifferenceFourB0_pos hm).le
      (sq_nonneg _)
  have hdiv :
      unequalFixedDifferenceFourB0 m * (1 - s) ^ 2
        ≤
      unequalFixedDifferenceFourB0 m * (1 - s) ^ 2
        / (1 - q * s) := by
    apply (le_div_iff₀ hdpos).2
    calc
      unequalFixedDifferenceFourB0 m * (1 - s) ^ 2
            * (1 - q * s)
          ≤
        unequalFixedDifferenceFourB0 m * (1 - s) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hdle hnum
      _ = unequalFixedDifferenceFourB0 m * (1 - s) ^ 2 := by
        ring
  calc
    (1 - s) ^ 2 / (1 - q * s)
          * (-unequalFixedDifferenceFourB0 m)
        =
      -(unequalFixedDifferenceFourB0 m * (1 - s) ^ 2
          / (1 - q * s)) := by
            ring
    _ ≤
      -(unequalFixedDifferenceFourB0 m * (1 - s) ^ 2) :=
        neg_le_neg hdiv
    _ = -unequalFixedDifferenceFourB0 m * (1 - s) ^ 2 := by
      ring

/-! ## Linear integral and prefactor bounds -/

/-- The concrete right-chart integral is uniformly bounded by the
negative pivot margin. -/
theorem unequalFixedDifferenceFourPlusAnalyticH_le_neg_b0
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourPlusAnalyticH m s
      ≤ -unequalFixedDifferenceFourB0 m := by
  unfold unequalFixedDifferenceFourPlusAnalyticH
  apply
    unequalFixedDifferenceFourPlusH_le_neg_b0_of_coefficient_identity
      (continuous_unequalFixedDifferenceFourPlusDensity m)
      hm ?_ hs0 hs1
  intro n
  calc
    unequalDampedIntegratedCoefficient
          (unequalFixedDifferenceFourPlusDensity m)
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourKappa m)
          (unequalFixedDifferenceFourC m)
          (unequalFixedDifferenceFourK m) n
        =
      unequalFixedDifferenceFourPlusPolynomialCoefficient m n :=
        unequalFixedDifferenceFourPlusIntegratedCoefficient_eq_polynomial
          hm n
    _ = unequalFixedDifferenceFourPlusCoeff m n :=
      unequalFixedDifferenceFourPlusPolynomialCoefficient_eq_coeff hm n

/-- The concrete sample-swapped integral has the same uniform bound. -/
theorem unequalFixedDifferenceFourMinusAnalyticH_le_neg_b0
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourMinusAnalyticH m s
      ≤ -unequalFixedDifferenceFourB0 m := by
  unfold unequalFixedDifferenceFourMinusAnalyticH
  apply
    unequalFixedDifferenceFourMinusH_le_neg_b0_of_coefficient_identity
      (continuous_unequalFixedDifferenceFourMinusDensity m)
      hm ?_ hs0 hs1
  intro n
  calc
    unequalDampedIntegratedCoefficient
          (unequalFixedDifferenceFourMinusDensity m)
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourT m)
          (-unequalFixedDifferenceFourKappa m)
          (unequalFixedDifferenceFourC m)
          (unequalFixedDifferenceFourK m) n
        =
      unequalFixedDifferenceFourMinusPolynomialCoefficient m n :=
        unequalFixedDifferenceFourMinusIntegratedCoefficient_eq_polynomial
          hm n
    _ = unequalFixedDifferenceFourMinusCoeff m n :=
      unequalFixedDifferenceFourMinusPolynomialCoefficient_eq_coeff hm n

/-- Uniform right-chart linear bound after restoring its positive
coordinate prefactor. -/
theorem unequalFixedDifferenceFourPlusB_le
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourPlusB m s
      ≤ -unequalFixedDifferenceFourB0 m * (1 - s) ^ 2 := by
  have hH :=
    unequalFixedDifferenceFourPlusAnalyticH_le_neg_b0
      hm hs0 hs1
  unfold unequalFixedDifferenceFourPlusB
  calc
    (1 - s) ^ 2
          / (1 - unequalFixedDifferenceFourQ m * s)
          * unequalFixedDifferenceFourPlusAnalyticH m s
        ≤
      (1 - s) ^ 2
          / (1 - unequalFixedDifferenceFourQ m * s)
          * (-unequalFixedDifferenceFourB0 m) := by
            exact mul_le_mul_of_nonneg_left hH
              (unequalFD4_oneSided_prefactor_nonneg
                (unequalFixedDifferenceFourQ_pos hm).le
                (unequalFixedDifferenceFourQ_le_one hm)
                hs0 hs1)
    _ ≤ -unequalFixedDifferenceFourB0 m * (1 - s) ^ 2 :=
      unequalFD4_neg_b0_prefactor_le hm
        (unequalFixedDifferenceFourQ_pos hm).le
        (unequalFixedDifferenceFourQ_le_one hm)
        hs0 hs1

/-- Uniform sample-swapped linear bound after restoring its positive
coordinate prefactor. -/
theorem unequalFixedDifferenceFourMinusB_le
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourMinusB m s
      ≤ -unequalFixedDifferenceFourB0 m * (1 - s) ^ 2 := by
  have hH :=
    unequalFixedDifferenceFourMinusAnalyticH_le_neg_b0
      hm hs0 hs1
  unfold unequalFixedDifferenceFourMinusB
  calc
    (1 - s) ^ 2
          / (1 - unequalFixedDifferenceFourT m * s)
          * unequalFixedDifferenceFourMinusAnalyticH m s
        ≤
      (1 - s) ^ 2
          / (1 - unequalFixedDifferenceFourT m * s)
          * (-unequalFixedDifferenceFourB0 m) := by
            exact mul_le_mul_of_nonneg_left hH
              (unequalFD4_oneSided_prefactor_nonneg
                (unequalFixedDifferenceFourT_pos hm).le
                (unequalFixedDifferenceFourT_le_one hm)
                hs0 hs1)
    _ ≤ -unequalFixedDifferenceFourB0 m * (1 - s) ^ 2 :=
      unequalFD4_neg_b0_prefactor_le hm
        (unequalFixedDifferenceFourT_pos hm).le
        (unequalFixedDifferenceFourT_le_one hm)
        hs0 hs1

/-! ## Quadratic bounds -/

/-- Uniform right-chart quadratic bound. -/
theorem unequalFixedDifferenceFourPlusC_le
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourPlusC m s
      ≤ unequalFixedDifferenceFourMPlus m * (1 - s) ^ 2 := by
  simpa only [unequalFixedDifferenceFourPlusC] using
    (integral_unequalFixedDifferenceFourPlusC_le hm hs0 hs1)

/-- Uniform sample-swapped quadratic bound, enlarged to the common
right-chart envelope constant. -/
theorem unequalFixedDifferenceFourMinusC_le
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourMinusC m s
      ≤ unequalFixedDifferenceFourMPlus m * (1 - s) ^ 2 := by
  simpa only [unequalFixedDifferenceFourMinusC] using
    (integral_unequalFixedDifferenceFourMinusC_le hm hs0 hs1)

/-! ## Fixed-epsilon reduced-risk inequalities -/

/-- The family perturbation has strictly negative reduced risk on the
right chart. -/
theorem unequalFixedDifferenceFourPlusReducedRisk_neg
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    2 * unequalFixedDifferenceFourEpsilon m
          * unequalFixedDifferenceFourPlusB m s
        + unequalFixedDifferenceFourEpsilon m ^ 2
          * unequalFixedDifferenceFourPlusC m s
      < 0 := by
  exact unequalFixedDifferenceFour_reducedRisk_neg_of_bounds
    hm hs1
    (unequalFixedDifferenceFourPlusB_le hm hs0 hs1)
    (unequalFixedDifferenceFourPlusC_le hm hs0 hs1)

/-- The same fixed family perturbation has strictly negative reduced risk
on the sample-swapped chart. -/
theorem unequalFixedDifferenceFourMinusReducedRisk_neg
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    2 * unequalFixedDifferenceFourEpsilon m
          * unequalFixedDifferenceFourMinusB m s
        + unequalFixedDifferenceFourEpsilon m ^ 2
          * unequalFixedDifferenceFourMinusC m s
      < 0 := by
  exact unequalFixedDifferenceFour_reducedRisk_neg_of_bounds
    hm hs1
    (unequalFixedDifferenceFourMinusB_le hm hs0 hs1)
    (unequalFixedDifferenceFourMinusC_le hm hs0 hs1)

end

end GraybillDeal
