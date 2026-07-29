import GraybillDeal.GeneralRawEstimatorAE
import GraybillDeal.GeneralRawRiskBridge

/-!
# Final all-sample-size raw Graybill--Deal dominance theorem

This module transports the generic canonical risk inequality across the
almost-everywhere coordinate identities.  For residual degrees of freedom
`ν ≥ 9`, hence equal sample size `ν + 1 ≥ 10`, it proves strict squared-risk
improvement of the literal clipped perturbation over the ordinary
Graybill--Deal estimator.

The coefficient `generalGraybillDealEpsilon ν` is fixed by `ν` alone and
does not depend on the unknown population variances.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem sqRisk_congr_ae_general
    {μ : ℝ} {estimator₁ estimator₂ : Ω → ℝ} {P : Measure Ω}
    (h : estimator₁ =ᵐ[P] estimator₂) :
    sqRisk μ estimator₁ P = sqRisk μ estimator₂ P := by
  unfold sqRisk
  apply integral_congr_ae
  filter_upwards [h] with ω hω
  rw [hω]

/--
The literal clipped perturbation with the fixed coefficient
`generalGraybillDealEpsilon ν` has strictly smaller squared-error risk than
the literal Graybill--Deal estimator.
-/
theorem rawClippedPerturbedEstimatorN_sqRisk_lt_rawGraybillDealEstimatorN
    (ν : ℕ) (hν : 9 ≤ ν)
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}
    (h : TwoNormalSamplesN ν X P μ variance)
    (hXmeas : ∀ g i, Measurable (X g i))
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    sqRisk μ
        (rawClippedPerturbedEstimatorN
          (generalGraybillDealEpsilon ν) ν X) P
      <
    sqRisk μ (rawGraybillDealEstimatorN ν X) P := by
  have hcanonical :=
    generalCanonicalClippedEstimatorRiskDifference_neg_of_raw_normal
      ν hν h hXmeas hvariance₀ hvariance₁
  have hclipped :=
    h.ae_eq_rawClippedPerturbedEstimatorN_of_normal_samples
      (generalGraybillDealEpsilon ν) hν hvariance₀ hvariance₁
  have hbase :=
    h.ae_eq_rawGraybillDealEstimatorN_of_normal_samples
      hν hvariance₀ hvariance₁
  rw [sqRisk_congr_ae_general hclipped,
    sqRisk_congr_ae_general hbase] at hcanonical
  exact hcanonical

/--
The final theorem with both estimators expanded into literal sample-mean and
sample-variance formulas.

For `ν ≥ 9`, put

`r = S₀² / (S₀² + S₁²)` and
`q = (ν+1)D² / (S₀² + S₁²)`.

Then the estimator using

`clip01 (r + ε_ν r(1-r)(1-2r)(4-q))`

strictly dominates the ordinary Graybill--Deal estimator, where
`ε_ν = generalGraybillDealEpsilon ν > 0`.
-/
theorem rawGraybillDealEstimatorN_strictly_dominated
    (ν : ℕ) (hν : 9 ≤ ν)
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}
    (h : TwoNormalSamplesN ν X P μ variance)
    (hXmeas : ∀ g i, Measurable (X g i))
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    sqRisk μ
        (fun ω =>
          let r :=
            sampleVarianceN ν (X 0) ω
              / (sampleVarianceN ν (X 0) ω
                + sampleVarianceN ν (X 1) ω)
          let q :=
            ((ν : ℝ) + 1) * meanDifferenceN ν X ω ^ 2
              / (sampleVarianceN ν (X 0) ω
                + sampleVarianceN ν (X 1) ω)
          sampleMeanN ν (X 0) ω
            + clip01
                (r + generalGraybillDealEpsilon ν
                  * r * (1 - r) * (1 - 2 * r) * (4 - q))
              * meanDifferenceN ν X ω) P
      <
    sqRisk μ
        (fun ω =>
          sampleMeanN ν (X 0) ω
            + (sampleVarianceN ν (X 0) ω
                / (sampleVarianceN ν (X 0) ω
                  + sampleVarianceN ν (X 1) ω))
              * meanDifferenceN ν X ω) P := by
  change
    sqRisk μ
        (rawClippedPerturbedEstimatorN
          (generalGraybillDealEpsilon ν) ν X) P
      <
    sqRisk μ (rawGraybillDealEstimatorN ν X) P
  exact
    rawClippedPerturbedEstimatorN_sqRisk_lt_rawGraybillDealEstimatorN
      ν hν h hXmeas hvariance₀ hvariance₁

end

end GraybillDeal
