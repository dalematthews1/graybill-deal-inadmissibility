import GraybillDeal.GeneralCanonicalSummary
import GraybillDeal.GeneralRawNormalSummary
import GraybillDeal.RawCoordinates

/-!
# Strict canonical risk improvement from arbitrary-size raw normal samples

This file applies the all-sample-size canonical summary theorem to two raw
normal samples with residual degrees of freedom `ν`.  Thus each sample has
size `ν + 1`, and the hypothesis `9 ≤ ν` is exactly the range of common
sample sizes `n ≥ 10`.

The perturbation coefficient is the fixed
`generalGraybillDealEpsilon ν`.  In particular, it depends only on the
sample size and not on the unknown population variances.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/--
For every pair of measurable normal samples with residual degrees of freedom
`ν ≥ 9`, the fixed clipped canonical perturbation has strictly smaller
squared-error risk than the canonical Graybill--Deal estimator.

The component beta/gamma laws, four-way summary independence, and
centered-error moments are all derived internally from `TwoNormalSamplesN`.
-/
theorem generalCanonicalClippedEstimatorRiskDifference_neg_of_raw_normal
    (ν : ℕ) (hν : 9 ≤ ν)
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
    {Pmeasure : Measure Ω} {μ : ℝ}
    {variance : Fin 2 → NNReal}
    (h : TwoNormalSamplesN ν X Pmeasure μ variance)
    (hXmeas : ∀ g i, Measurable (X g i))
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    sqRisk μ
        (fun ω =>
          μ
            + oracleCenteredErrorN ν μ variance X ω
            + meanDifferenceN ν X ω
              * (generalCanonicalClippedWeight
                    (generalGraybillDealEpsilon ν) (ν : ℝ)
                    (rawVarianceContrast
                      (variance 0 : ℝ) (variance 1 : ℝ))
                    (normalRawPN ν variance X ω)
                    (normalRawLN ν variance X ω)
                    (normalRawVN ν variance X ω)
                  - canonicalTheta
                    (rawVarianceContrast
                      (variance 0 : ℝ) (variance 1 : ℝ)))) Pmeasure
      <
    sqRisk μ
        (fun ω =>
          μ
            + oracleCenteredErrorN ν μ variance X ω
            + meanDifferenceN ν X ω
              * (canonicalR
                    (rawVarianceContrast
                      (variance 0 : ℝ) (variance 1 : ℝ))
                    (normalRawPN ν variance X ω)
                  - canonicalTheta
                    (rawVarianceContrast
                      (variance 0 : ℝ) (variance 1 : ℝ)))) Pmeasure := by
  have hlaws :
      RawNormalSummaryLawsN ν μ variance X Pmeasure :=
    rawNormalSummaryLawsN_of_normal_samples
      ν hν h hXmeas hvariance₀ hvariance₁
  have hvarianceSum :
      0 < normalVarianceSumN variance := by
    unfold normalVarianceSumN
    exact add_pos hvariance₀ hvariance₁
  have hs :
      |rawVarianceContrast
          (variance 0 : ℝ) (variance 1 : ℝ)| < 1 :=
    abs_rawVarianceContrast_lt_one hvariance₀ hvariance₁
  have hV :
      HasLaw
        (fun ω =>
          generalStandardizedDifference (ν : ℝ)
            (normalVarianceSumN variance) (meanDifferenceN ν X ω))
        (gammaMeasure (1 / 2) (1 / 2)) Pmeasure := by
    change
      HasLaw (normalRawVN ν variance X)
        (gammaMeasure (1 / 2) (1 / 2)) Pmeasure
    exact hlaws.v_law
  have hrisk :=
    generalCanonicalClippedEstimatorRiskDifference_neg_of_iIndepFun_summary4
      ν hν μ
      (normalVarianceSumN variance)
      (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
      (oracleCenteredErrorN ν μ variance X)
      (meanDifferenceN ν X)
      (normalRawPN ν variance X)
      (normalRawLN ν variance X)
      Pmeasure
      hvarianceSum hs
      (measurable_normalRawPN hXmeas)
      (measurable_normalRawLN hXmeas)
      (measurable_meanDifferenceN hXmeas)
      (measurable_oracleCenteredErrorN hXmeas)
      hlaws.p_law hlaws.l_law
      hV
      hlaws.summary_iIndep
      hlaws.centered_sq hlaws.centered_zero
  exact hrisk

end

end GraybillDeal
