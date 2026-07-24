import GraybillDeal.GeneralCanonicalClipping
import GraybillDeal.GeneralRawPositivity

/-!
# Literal Graybill--Deal estimators at arbitrary equal sample size

For residual degrees of freedom `ν` (sample size `ν+1`), write

* `D = sampleMean₁ - sampleMean₀`,
* `r = S₀² / (S₀² + S₁²)`,
* `q = (ν+1)D² / (S₀² + S₁²)`.

The ordinary Graybill--Deal estimator is `sampleMean₀ + rD`.  Its generic
competitor replaces `r` by

`clip01 (r + ε r(1-r)(1-2r)(4-q))`.

This file identifies those literal raw expressions pointwise, and then
almost everywhere under the two-normal-sample model, with the canonical
expressions used by the all-`n` risk theorem.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The observed Graybill--Deal weight. -/
def rawGraybillDealWeightN
    (ν : ℕ) (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleVarianceN ν (X 0) ω
    / (sampleVarianceN ν (X 0) ω + sampleVarianceN ν (X 1) ω)

/-- The raw quadratic statistic in the perturbation direction. -/
def rawQuadraticStatisticN
    (ν : ℕ) (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  ((ν : ℝ) + 1) * meanDifferenceN ν X ω ^ 2
    / (sampleVarianceN ν (X 0) ω + sampleVarianceN ν (X 1) ω)

/-- The ordinary Graybill--Deal estimator. -/
def rawGraybillDealEstimatorN
    (ν : ℕ) (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleMeanN ν (X 0) ω
    + rawGraybillDealWeightN ν X ω * meanDifferenceN ν X ω

/-- The literal un-clipped perturbed Graybill--Deal weight. -/
def rawPerturbedWeightN
    (ε : ℝ) (ν : ℕ)
    (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  let r := rawGraybillDealWeightN ν X ω
  let q := rawQuadraticStatisticN ν X ω
  r + ε * r * (1 - r) * (1 - 2 * r) * (4 - q)

/-- The literal clipped perturbed Graybill--Deal weight. -/
def rawClippedPerturbedWeightN
    (ε : ℝ) (ν : ℕ)
    (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  clip01 (rawPerturbedWeightN ε ν X ω)

/-- The raw estimator with the un-clipped perturbed weight. -/
def rawPerturbedEstimatorN
    (ε : ℝ) (ν : ℕ)
    (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleMeanN ν (X 0) ω
    + rawPerturbedWeightN ε ν X ω * meanDifferenceN ν X ω

/-- The raw estimator with the clipped perturbed weight. -/
def rawClippedPerturbedEstimatorN
    (ε : ℝ) (ν : ℕ)
    (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleMeanN ν (X 0) ω
    + rawClippedPerturbedWeightN ε ν X ω * meanDifferenceN ν X ω

/-- The canonical population weight equals the oracle inverse-variance weight. -/
theorem canonicalTheta_eq_oracleVarianceWeightN
    {variance : Fin 2 → NNReal}
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    canonicalTheta
        (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
      =
    oracleVarianceWeightN variance := by
  rw [canonicalTheta_rawVarianceContrast]
  · rfl
  · unfold rawVarianceSum
    exact ne_of_gt (add_pos hvariance₀ hvariance₁)

/-- The probabilistic coordinate `U_g` is exactly `ν S_g² / variance_g`. -/
theorem normalRawUN_eq_rawResidualScaleN
    {ν : ℕ} (hν : 0 < ν)
    (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) (g : Fin 2) (ω : Ω) :
    normalRawUN ν variance X g ω
      =
    rawResidualScaleN ν
      (variance g) (sampleVarianceN ν (X g) ω) := by
  unfold normalRawUN scaledResidualSumSquaresN rawResidualScaleN
  rw [residualDF_mul_sampleVarianceN hν (X g) ω]

/-- The probabilistic beta ratio agrees with `rawResidualPN`. -/
theorem normalRawPN_eq_rawResidualPN
    {ν : ℕ} (hν : 0 < ν)
    (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) (ω : Ω) :
    normalRawPN ν variance X ω
      =
    rawResidualPN ν
      (variance 0) (variance 1)
      (sampleVarianceN ν (X 0) ω)
      (sampleVarianceN ν (X 1) ω) := by
  unfold normalRawPN rawResidualPN rawResidualLN
  rw [normalRawUN_eq_rawResidualScaleN hν,
    normalRawUN_eq_rawResidualScaleN hν]

/-- The probabilistic gamma sum agrees with `rawResidualLN`. -/
theorem normalRawLN_eq_rawResidualLN
    {ν : ℕ} (hν : 0 < ν)
    (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) (ω : Ω) :
    normalRawLN ν variance X ω
      =
    rawResidualLN ν
      (variance 0) (variance 1)
      (sampleVarianceN ν (X 0) ω)
      (sampleVarianceN ν (X 1) ω) := by
  unfold normalRawLN rawResidualLN
  rw [normalRawUN_eq_rawResidualScaleN hν,
    normalRawUN_eq_rawResidualScaleN hν]

/-- The canonical squared-mean coordinate is the raw standardized difference. -/
theorem normalRawVN_eq_raw_generalStandardizedDifference
    (ν : ℕ) (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) (ω : Ω) :
    normalRawVN ν variance X ω
      =
    generalStandardizedDifference (ν : ℝ)
      (rawVarianceSum (variance 0) (variance 1))
      (meanDifferenceN ν X ω) := by
  rfl

/-- The canonical base weight is exactly the observed Graybill--Deal weight. -/
theorem canonicalR_eq_rawGraybillDealWeightN
    {ν : ℕ} {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ} {ω : Ω}
    (hν : 0 < ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ))
    (hL : normalRawLN ν variance X ω ≠ 0)
    (hSsum :
      sampleVarianceN ν (X 0) ω
        + sampleVarianceN ν (X 1) ω ≠ 0) :
    canonicalR
        (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
        (normalRawPN ν variance X ω)
      =
    rawGraybillDealWeightN ν X ω := by
  rw [normalRawPN_eq_rawResidualPN hν]
  unfold rawGraybillDealWeightN
  apply canonicalR_rawResidualPN hν
  · exact ne_of_gt hvariance₀
  · exact ne_of_gt hvariance₁
  · unfold rawVarianceSum
    exact ne_of_gt (add_pos hvariance₀ hvariance₁)
  · rwa [← normalRawLN_eq_rawResidualLN hν]
  · exact hSsum

/--
The canonical `q` statistic is exactly
`(ν+1)D²/(S₀²+S₁²)`.
-/
theorem canonicalQ_eq_rawQuadraticStatisticN
    {ν : ℕ} {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ} {ω : Ω}
    (hν : 0 < ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ))
    (hL : normalRawLN ν variance X ω ≠ 0)
    (hSsum :
      sampleVarianceN ν (X 0) ω
        + sampleVarianceN ν (X 1) ω ≠ 0) :
    canonicalQ (ν : ℝ)
        (canonicalTheta
          (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ)))
        (normalRawPN ν variance X ω)
        (normalRawLN ν variance X ω)
        (normalRawVN ν variance X ω)
      =
    rawQuadraticStatisticN ν X ω := by
  rw [normalRawPN_eq_rawResidualPN hν,
    normalRawLN_eq_rawResidualLN hν,
    normalRawVN_eq_raw_generalStandardizedDifference]
  unfold rawQuadraticStatisticN
  apply canonicalQ_rawResidual_coordinates hν
  · exact ne_of_gt hvariance₀
  · exact ne_of_gt hvariance₁
  · unfold rawVarianceSum
    exact ne_of_gt (add_pos hvariance₀ hvariance₁)
  · rwa [← normalRawLN_eq_rawResidualLN hν]
  · exact hSsum

/-- The un-clipped canonical weight is exactly the literal raw perturbation. -/
theorem generalCanonicalWeight_eq_rawPerturbedWeightN
    {ε : ℝ} {ν : ℕ} {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ} {ω : Ω}
    (hν : 0 < ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ))
    (hL : normalRawLN ν variance X ω ≠ 0)
    (hSsum :
      sampleVarianceN ν (X 0) ω
        + sampleVarianceN ν (X 1) ω ≠ 0) :
    generalCanonicalWeight ε (ν : ℝ)
        (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
        (normalRawPN ν variance X ω)
        (normalRawLN ν variance X ω)
        (normalRawVN ν variance X ω)
      =
    rawPerturbedWeightN ε ν X ω := by
  unfold generalCanonicalWeight perturbation rawPerturbedWeightN
  rw [generalCanonicalH_eq]
  rw [canonicalR_eq_rawGraybillDealWeightN
      hν hvariance₀ hvariance₁ hL hSsum,
    canonicalQ_eq_rawQuadraticStatisticN
      hν hvariance₀ hvariance₁ hL hSsum]
  unfold weightPolynomial
  ring

/-- The clipped canonical weight is exactly the literal clipped perturbation. -/
theorem generalCanonicalClippedWeight_eq_rawClippedPerturbedWeightN
    {ε : ℝ} {ν : ℕ} {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ} {ω : Ω}
    (hν : 0 < ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ))
    (hL : normalRawLN ν variance X ω ≠ 0)
    (hSsum :
      sampleVarianceN ν (X 0) ω
        + sampleVarianceN ν (X 1) ω ≠ 0) :
    generalCanonicalClippedWeight ε (ν : ℝ)
        (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
        (normalRawPN ν variance X ω)
        (normalRawLN ν variance X ω)
        (normalRawVN ν variance X ω)
      =
    rawClippedPerturbedWeightN ε ν X ω := by
  unfold generalCanonicalClippedWeight rawClippedPerturbedWeightN
  rw [generalCanonicalWeight_eq_rawPerturbedWeightN
    hν hvariance₀ hvariance₁ hL hSsum]

/-- The ordinary estimator has its familiar symmetric numerator form. -/
theorem rawGraybillDealEstimatorN_eq_ratio
    {ν : ℕ} {X : Fin 2 → Fin (ν + 1) → Ω → ℝ} {ω : Ω}
    (hSsum :
      sampleVarianceN ν (X 0) ω
        + sampleVarianceN ν (X 1) ω ≠ 0) :
    rawGraybillDealEstimatorN ν X ω
      =
    (sampleVarianceN ν (X 1) ω * sampleMeanN ν (X 0) ω
        + sampleVarianceN ν (X 0) ω * sampleMeanN ν (X 1) ω)
      / (sampleVarianceN ν (X 0) ω
          + sampleVarianceN ν (X 1) ω) := by
  unfold rawGraybillDealEstimatorN rawGraybillDealWeightN
  unfold meanDifferenceN
  field_simp [hSsum]
  ring

/-- The full canonical baseline is exactly the ordinary Graybill--Deal estimator. -/
theorem generalCanonicalBaseEstimator_eq_rawGraybillDealEstimatorN
    {ν : ℕ} {μ : ℝ} {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ} {ω : Ω}
    (hν : 0 < ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ))
    (hL : normalRawLN ν variance X ω ≠ 0)
    (hSsum :
      sampleVarianceN ν (X 0) ω
        + sampleVarianceN ν (X 1) ω ≠ 0) :
    μ
        + oracleCenteredErrorN ν μ variance X ω
        + meanDifferenceN ν X ω
          * (canonicalR
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ))
                (normalRawPN ν variance X ω)
              - canonicalTheta
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ)))
      =
    rawGraybillDealEstimatorN ν X ω := by
  rw [canonicalR_eq_rawGraybillDealWeightN
      hν hvariance₀ hvariance₁ hL hSsum,
    canonicalTheta_eq_oracleVarianceWeightN
      hvariance₀ hvariance₁]
  unfold oracleCenteredErrorN rawGraybillDealEstimatorN
  ring

/-- The full un-clipped canonical competitor is the literal raw competitor. -/
theorem generalCanonicalEstimator_eq_rawPerturbedEstimatorN
    {ε : ℝ} {ν : ℕ} {μ : ℝ} {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ} {ω : Ω}
    (hν : 0 < ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ))
    (hL : normalRawLN ν variance X ω ≠ 0)
    (hSsum :
      sampleVarianceN ν (X 0) ω
        + sampleVarianceN ν (X 1) ω ≠ 0) :
    μ
        + oracleCenteredErrorN ν μ variance X ω
        + meanDifferenceN ν X ω
          * (generalCanonicalWeight ε (ν : ℝ)
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ))
                (normalRawPN ν variance X ω)
                (normalRawLN ν variance X ω)
                (normalRawVN ν variance X ω)
              - canonicalTheta
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ)))
      =
    rawPerturbedEstimatorN ε ν X ω := by
  rw [generalCanonicalWeight_eq_rawPerturbedWeightN
      hν hvariance₀ hvariance₁ hL hSsum,
    canonicalTheta_eq_oracleVarianceWeightN
      hvariance₀ hvariance₁]
  unfold oracleCenteredErrorN rawPerturbedEstimatorN
  ring

/-- The full clipped canonical competitor is the literal raw clipped competitor. -/
theorem generalCanonicalClippedEstimator_eq_rawClippedPerturbedEstimatorN
    {ε : ℝ} {ν : ℕ} {μ : ℝ} {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ} {ω : Ω}
    (hν : 0 < ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ))
    (hL : normalRawLN ν variance X ω ≠ 0)
    (hSsum :
      sampleVarianceN ν (X 0) ω
        + sampleVarianceN ν (X 1) ω ≠ 0) :
    μ
        + oracleCenteredErrorN ν μ variance X ω
        + meanDifferenceN ν X ω
          * (generalCanonicalClippedWeight ε (ν : ℝ)
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ))
                (normalRawPN ν variance X ω)
                (normalRawLN ν variance X ω)
                (normalRawVN ν variance X ω)
              - canonicalTheta
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ)))
      =
    rawClippedPerturbedEstimatorN ε ν X ω := by
  rw [generalCanonicalClippedWeight_eq_rawClippedPerturbedWeightN
      hν hvariance₀ hvariance₁ hL hSsum,
    canonicalTheta_eq_oracleVarianceWeightN
      hvariance₀ hvariance₁]
  unfold oracleCenteredErrorN rawClippedPerturbedEstimatorN
  ring

namespace TwoNormalSamplesN

variable {ν : ℕ}
  {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}

/-- Almost-everywhere transport of the canonical base weight to raw data. -/
theorem ae_eq_canonicalR_rawGraybillDealWeightN
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    (fun ω =>
      canonicalR
        (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
        (normalRawPN ν variance X ω))
      =ᵐ[P]
    rawGraybillDealWeightN ν X := by
  filter_upwards
    [h.ae_ne_normalRawLN hν hvariance₀ hvariance₁,
      h.ae_ne_sampleVarianceSumN
        hν hvariance₀ hvariance₁] with ω hL hSsum
  exact canonicalR_eq_rawGraybillDealWeightN
    (by omega) hvariance₀ hvariance₁ hL hSsum

/-- Almost-everywhere transport of the canonical quadratic statistic. -/
theorem ae_eq_canonicalQ_rawQuadraticStatisticN
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    (fun ω =>
      canonicalQ (ν : ℝ)
        (canonicalTheta
          (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ)))
        (normalRawPN ν variance X ω)
        (normalRawLN ν variance X ω)
        (normalRawVN ν variance X ω))
      =ᵐ[P]
    rawQuadraticStatisticN ν X := by
  filter_upwards
    [h.ae_ne_normalRawLN hν hvariance₀ hvariance₁,
      h.ae_ne_sampleVarianceSumN
        hν hvariance₀ hvariance₁] with ω hL hSsum
  exact canonicalQ_eq_rawQuadraticStatisticN
    (by omega) hvariance₀ hvariance₁ hL hSsum

/-- Almost-everywhere transport of the un-clipped perturbed weight. -/
theorem ae_eq_generalCanonicalWeight_rawPerturbedWeightN
    (ε : ℝ)
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    (fun ω =>
      generalCanonicalWeight ε (ν : ℝ)
        (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
        (normalRawPN ν variance X ω)
        (normalRawLN ν variance X ω)
        (normalRawVN ν variance X ω))
      =ᵐ[P]
    rawPerturbedWeightN ε ν X := by
  filter_upwards
    [h.ae_ne_normalRawLN hν hvariance₀ hvariance₁,
      h.ae_ne_sampleVarianceSumN
        hν hvariance₀ hvariance₁] with ω hL hSsum
  exact generalCanonicalWeight_eq_rawPerturbedWeightN
    (by omega) hvariance₀ hvariance₁ hL hSsum

/-- Almost-everywhere transport of the clipped perturbed weight. -/
theorem ae_eq_generalCanonicalClippedWeight_rawClippedPerturbedWeightN
    (ε : ℝ)
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    (fun ω =>
      generalCanonicalClippedWeight ε (ν : ℝ)
        (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
        (normalRawPN ν variance X ω)
        (normalRawLN ν variance X ω)
        (normalRawVN ν variance X ω))
      =ᵐ[P]
    rawClippedPerturbedWeightN ε ν X := by
  filter_upwards
    [h.ae_ne_normalRawLN hν hvariance₀ hvariance₁,
      h.ae_ne_sampleVarianceSumN
        hν hvariance₀ hvariance₁] with ω hL hSsum
  exact generalCanonicalClippedWeight_eq_rawClippedPerturbedWeightN
    (by omega) hvariance₀ hvariance₁ hL hSsum

/-- Almost-everywhere transport of the canonical baseline estimator. -/
theorem ae_eq_generalCanonicalBaseEstimator_rawGraybillDealEstimatorN
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
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
                  (variance 0 : ℝ) (variance 1 : ℝ))))
      =ᵐ[P]
    rawGraybillDealEstimatorN ν X := by
  filter_upwards
    [h.ae_ne_normalRawLN hν hvariance₀ hvariance₁,
      h.ae_ne_sampleVarianceSumN
        hν hvariance₀ hvariance₁] with ω hL hSsum
  exact generalCanonicalBaseEstimator_eq_rawGraybillDealEstimatorN
    (by omega) hvariance₀ hvariance₁ hL hSsum

/-- Almost-everywhere transport of the un-clipped canonical estimator. -/
theorem ae_eq_generalCanonicalEstimator_rawPerturbedEstimatorN
    (ε : ℝ)
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    (fun ω =>
      μ
        + oracleCenteredErrorN ν μ variance X ω
        + meanDifferenceN ν X ω
          * (generalCanonicalWeight ε (ν : ℝ)
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ))
                (normalRawPN ν variance X ω)
                (normalRawLN ν variance X ω)
                (normalRawVN ν variance X ω)
              - canonicalTheta
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ))))
      =ᵐ[P]
    rawPerturbedEstimatorN ε ν X := by
  filter_upwards
    [h.ae_ne_normalRawLN hν hvariance₀ hvariance₁,
      h.ae_ne_sampleVarianceSumN
        hν hvariance₀ hvariance₁] with ω hL hSsum
  exact generalCanonicalEstimator_eq_rawPerturbedEstimatorN
    (by omega) hvariance₀ hvariance₁ hL hSsum

/-- Almost-everywhere transport of the clipped canonical estimator. -/
theorem ae_eq_generalCanonicalClippedEstimator_rawClippedPerturbedEstimatorN
    (ε : ℝ)
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    (fun ω =>
      μ
        + oracleCenteredErrorN ν μ variance X ω
        + meanDifferenceN ν X ω
          * (generalCanonicalClippedWeight ε (ν : ℝ)
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ))
                (normalRawPN ν variance X ω)
                (normalRawLN ν variance X ω)
                (normalRawVN ν variance X ω)
              - canonicalTheta
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ))))
      =ᵐ[P]
    rawClippedPerturbedEstimatorN ε ν X := by
  filter_upwards
    [h.ae_ne_normalRawLN hν hvariance₀ hvariance₁,
      h.ae_ne_sampleVarianceSumN
        hν hvariance₀ hvariance₁] with ω hL hSsum
  exact
    generalCanonicalClippedEstimator_eq_rawClippedPerturbedEstimatorN
      (by omega) hvariance₀ hvariance₁ hL hSsum

end TwoNormalSamplesN

end

end GraybillDeal
