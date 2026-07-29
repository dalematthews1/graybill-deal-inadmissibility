import GraybillDeal.RawEstimatorCoordinates
import GraybillDeal.RawPositivity
import GraybillDeal.RawRiskBridge

/-!
# Final raw-estimator risk theorem

This file transports the canonical strict risk inequality across the
almost-everywhere coordinate identities.  It concludes that, for two
independent normal samples of size thirteen with positive variances, the
explicit clipped perturbation

`clip01 (r + epsilon13 * r * (1-r) * (1-2r) * (4-q))`

strictly dominates the ordinary Graybill--Deal estimator, where

* `r = S₀² / (S₀² + S₁²)`, and
* `q = 13 * (bar X₁ - bar X₀)² / (S₀² + S₁²)`.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Squared-error risk is unchanged by almost-everywhere modification. -/
theorem sqRisk_congr_ae
    {μ : ℝ} {estimator₁ estimator₂ : Ω → ℝ} {P : Measure Ω}
    (h : estimator₁ =ᵐ[P] estimator₂) :
    sqRisk μ estimator₁ P = sqRisk μ estimator₂ P := by
  unfold sqRisk
  apply integral_congr_ae
  filter_upwards [h] with ω hω
  rw [hω]

/--
Under the raw normal model, the full canonical baseline estimator agrees
almost everywhere with the ordinary Graybill--Deal estimator.
-/
theorem canonicalBaseEstimator13_ae_eq_rawGraybillDealEstimator13
    {X : Fin 2 → Fin 13 → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}
    (h : TwoNormalSamples13 X P μ variance)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    (fun ω =>
      μ
        + oracleCenteredError13 μ
            (oracleVarianceWeight13 variance) X ω
        + meanDifference13 X ω
          * (canonicalR
                (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
                (normalRawP13 variance X ω)
              - canonicalTheta
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ))))
      =ᵐ[P]
    rawGraybillDealEstimator13 X := by
  filter_upwards
    [h.ae_ne_normalRawL13 hvariance₀ hvariance₁,
      h.ae_ne_sampleVarianceSum13 hvariance₀ hvariance₁] with ω hL hSsum
  exact
    canonicalBaseEstimator13_eq_rawGraybillDealEstimator13
      hvariance₀ hvariance₁ hL hSsum

/--
Under the raw normal model, the full canonical clipped estimator agrees
almost everywhere with the explicit raw clipped perturbation.
-/
theorem canonicalClippedEstimator13_ae_eq_rawClippedPerturbedEstimator13
    {X : Fin 2 → Fin 13 → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}
    (h : TwoNormalSamples13 X P μ variance)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    (fun ω =>
      μ
        + oracleCenteredError13 μ
            (oracleVarianceWeight13 variance) X ω
        + meanDifference13 X ω
          * (canonicalClippedWeight13 epsilon13
                (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
                (normalRawP13 variance X ω)
                (normalRawL13 variance X ω)
                (standardizedDifference13
                  (normalVarianceSum13 variance)
                  (meanDifference13 X ω))
              - canonicalTheta
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ))))
      =ᵐ[P]
    rawClippedPerturbedEstimator13 X := by
  filter_upwards
    [h.ae_ne_normalRawL13 hvariance₀ hvariance₁,
      h.ae_ne_sampleVarianceSum13 hvariance₀ hvariance₁] with ω hL hSsum
  simpa only [normalRawV13] using
    canonicalClippedEstimator13_eq_rawClippedPerturbedEstimator13
      (μ := μ) hvariance₀ hvariance₁ hL hSsum

/--
The explicit clipped perturbation strictly dominates the ordinary
Graybill--Deal estimator under squared-error loss.
-/
theorem rawClippedPerturbedEstimator13_sqRisk_lt_rawGraybillDealEstimator13
    {X : Fin 2 → Fin 13 → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}
    (h : TwoNormalSamples13 X P μ variance)
    (hXmeas : ∀ g i, Measurable (X g i))
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    sqRisk μ (rawClippedPerturbedEstimator13 X) P
      <
    sqRisk μ (rawGraybillDealEstimator13 X) P := by
  have hcanonical :=
    canonicalClippedEstimatorRiskDifference13_neg_of_raw_normal
      h hXmeas hvariance₀ hvariance₁
  have hclipped :
      (fun ω =>
        μ
          + oracleCenteredError13 μ
              (oracleVarianceWeight13 variance) X ω
          + meanDifference13 X ω
            * (canonicalClippedWeight13 epsilon13
                  (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
                  (normalRawP13 variance X ω)
                  (normalRawL13 variance X ω)
                  (standardizedDifference13
                    (normalVarianceSum13 variance)
                    (meanDifference13 X ω))
                - canonicalTheta
                  (rawVarianceContrast
                    (variance 0 : ℝ) (variance 1 : ℝ))))
        =ᵐ[P]
      rawClippedPerturbedEstimator13 X :=
    canonicalClippedEstimator13_ae_eq_rawClippedPerturbedEstimator13
      h hvariance₀ hvariance₁
  have hbase :
      (fun ω =>
        μ
          + oracleCenteredError13 μ
              (oracleVarianceWeight13 variance) X ω
          + meanDifference13 X ω
            * (canonicalR
                  (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
                  (normalRawP13 variance X ω)
                - canonicalTheta
                  (rawVarianceContrast
                    (variance 0 : ℝ) (variance 1 : ℝ))))
        =ᵐ[P]
      rawGraybillDealEstimator13 X :=
    canonicalBaseEstimator13_ae_eq_rawGraybillDealEstimator13
      h hvariance₀ hvariance₁
  rw [sqRisk_congr_ae hclipped, sqRisk_congr_ae hbase] at hcanonical
  exact hcanonical

/--
The same dominance theorem with both estimators expanded into their literal
sample-mean and sample-variance formulas.
-/
theorem rawGraybillDealEstimator13_strictly_dominated
    {X : Fin 2 → Fin 13 → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}
    (h : TwoNormalSamples13 X P μ variance)
    (hXmeas : ∀ g i, Measurable (X g i))
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    sqRisk μ
        (fun ω =>
          let r :=
            sampleVariance13 (X 0) ω
              / (sampleVariance13 (X 0) ω
                + sampleVariance13 (X 1) ω)
          let q :=
            13 * meanDifference13 X ω ^ 2
              / (sampleVariance13 (X 0) ω
                + sampleVariance13 (X 1) ω)
          sampleMean13 (X 0) ω
            + clip01
                (r + epsilon13 * r * (1 - r) * (1 - 2 * r) * (4 - q))
              * meanDifference13 X ω) P
      <
    sqRisk μ
        (fun ω =>
          sampleMean13 (X 0) ω
            + (sampleVariance13 (X 0) ω
                / (sampleVariance13 (X 0) ω
                  + sampleVariance13 (X 1) ω))
      * meanDifference13 X ω) P := by
  change
    sqRisk μ (rawClippedPerturbedEstimator13 X) P
      < sqRisk μ (rawGraybillDealEstimator13 X) P
  exact
    rawClippedPerturbedEstimator13_sqRisk_lt_rawGraybillDealEstimator13
      h hXmeas hvariance₀ hvariance₁

end

end GraybillDeal
