import GraybillDeal.RawNormalSummary
import GraybillDeal.SummaryIndependence

/-!
# Strict canonical risk improvement from two raw normal samples

This file applies the canonical risk theorem to the component laws assembled
from two samples of thirteen independent normal observations.

The only probabilistic inputs not already contained in `TwoNormalSamples13`
are the two fixed-size Cochran laws

`normalRawU13 variance X g ∼ Gamma(6, 1/2)`.

Thus this theorem is the final risk-level bridge to which the residual
chi-square formalisation can be attached.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/--
Strict improvement of the clipped canonical estimator, derived directly
from the raw two-sample normal model and the two marginal residual Gamma
laws.

Here the canonical variables are the actual raw summaries:

* the centered error of the known-variance estimator;
* the difference of the two sample means;
* the ratio and sum of the standardized residual sums of squares;
* the population variance sum and variance contrast.
-/
theorem canonicalClippedEstimatorRiskDifference13_neg_of_raw_normal_and_scaledResidual_gamma
    {X : Fin 2 → Fin 13 → Ω → ℝ}
    {Pmeasure : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}
    (h : TwoNormalSamples13 X Pmeasure μ variance)
    (hXmeas : ∀ g i, Measurable (X g i))
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ))
    (hU :
      ∀ g,
        HasLaw (normalRawU13 variance X g)
          (gammaMeasure 6 (1 / 2)) Pmeasure) :
    sqRisk μ
        (fun ω =>
          μ
            + oracleCenteredError13 μ
                (oracleVarianceWeight13 variance) X ω
            + meanDifference13 X ω
              * (canonicalClippedWeight13 epsilon13
                    (rawVarianceContrast
                      (variance 0 : ℝ) (variance 1 : ℝ))
                    (normalRawP13 variance X ω)
                    (normalRawL13 variance X ω)
                    (standardizedDifference13
                      (normalVarianceSum13 variance)
                      (meanDifference13 X ω))
                  - canonicalTheta
                    (rawVarianceContrast
                      (variance 0 : ℝ) (variance 1 : ℝ)))) Pmeasure
      <
    sqRisk μ
        (fun ω =>
          μ
            + oracleCenteredError13 μ
                (oracleVarianceWeight13 variance) X ω
            + meanDifference13 X ω
              * (canonicalR
                    (rawVarianceContrast
                      (variance 0 : ℝ) (variance 1 : ℝ))
                    (normalRawP13 variance X ω)
                  - canonicalTheta
                    (rawVarianceContrast
                      (variance 0 : ℝ) (variance 1 : ℝ)))) Pmeasure := by
  have hlaws :
      RawNormalSummaryLaws13 μ variance X Pmeasure :=
    rawNormalSummaryLaws13_of_scaledResidual_gamma
      h hXmeas hvariance₀ hvariance₁ hU
  have hvarianceSum :
      0 < normalVarianceSum13 variance := by
    unfold normalVarianceSum13
    exact add_pos hvariance₀ hvariance₁
  have hs :
      |rawVarianceContrast
          (variance 0 : ℝ) (variance 1 : ℝ)| < 1 :=
    abs_rawVarianceContrast_lt_one hvariance₀ hvariance₁
  have hDmeas :
      Measurable (meanDifference13 X) :=
    measurable_meanDifference13 hXmeas
  have hcenteredMeas :
      Measurable
        (oracleCenteredError13 μ
          (oracleVarianceWeight13 variance) X) :=
    measurable_oracleCenteredError13 hXmeas _ _
  have hUmeas :
      ∀ g, Measurable (normalRawU13 variance X g) := by
    intro g
    exact
      measurable_scaledResidualSumSquares13
        (hXmeas g) (variance g)
  have hPmeas :
      Measurable (normalRawP13 variance X) := by
    unfold normalRawP13
    fun_prop
  have hLmeas :
      Measurable (normalRawL13 variance X) := by
    unfold normalRawL13
    fun_prop
  exact
    canonicalClippedEstimatorRiskDifference13_neg_of_summary_laws_iIndep
      μ
      (normalVarianceSum13 variance)
      (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
      (oracleCenteredError13 μ (oracleVarianceWeight13 variance) X)
      (meanDifference13 X)
      (normalRawP13 variance X)
      (normalRawL13 variance X)
      Pmeasure
      hvarianceSum hs hPmeas hLmeas hDmeas hcenteredMeas
      hlaws.p_law hlaws.l_law hlaws.v_law hlaws.summary_iIndep
      hlaws.centered_sq hlaws.centered_zero

/--
Strict canonical risk improvement derived directly from two measurable raw
normal samples.  The residual Gamma hypotheses of the preceding theorem are
discharged by the fixed-size Cochran theorem.
-/
theorem canonicalClippedEstimatorRiskDifference13_neg_of_raw_normal
    {X : Fin 2 → Fin 13 → Ω → ℝ}
    {Pmeasure : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}
    (h : TwoNormalSamples13 X Pmeasure μ variance)
    (hXmeas : ∀ g i, Measurable (X g i))
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    sqRisk μ
        (fun ω =>
          μ
            + oracleCenteredError13 μ
                (oracleVarianceWeight13 variance) X ω
            + meanDifference13 X ω
              * (canonicalClippedWeight13 epsilon13
                    (rawVarianceContrast
                      (variance 0 : ℝ) (variance 1 : ℝ))
                    (normalRawP13 variance X ω)
                    (normalRawL13 variance X ω)
                    (standardizedDifference13
                      (normalVarianceSum13 variance)
                      (meanDifference13 X ω))
                  - canonicalTheta
                    (rawVarianceContrast
                      (variance 0 : ℝ) (variance 1 : ℝ)))) Pmeasure
      <
    sqRisk μ
        (fun ω =>
          μ
            + oracleCenteredError13 μ
                (oracleVarianceWeight13 variance) X ω
            + meanDifference13 X ω
              * (canonicalR
                    (rawVarianceContrast
                      (variance 0 : ℝ) (variance 1 : ℝ))
                    (normalRawP13 variance X ω)
                  - canonicalTheta
                    (rawVarianceContrast
                      (variance 0 : ℝ) (variance 1 : ℝ)))) Pmeasure := by
  apply
    canonicalClippedEstimatorRiskDifference13_neg_of_raw_normal_and_scaledResidual_gamma
      h hXmeas hvariance₀ hvariance₁
  intro g
  fin_cases g
  · exact h.hasLaw_scaledResidualSumSquares13 0 hvariance₀
  · exact h.hasLaw_scaledResidualSumSquares13 1 hvariance₁

end

end GraybillDeal
