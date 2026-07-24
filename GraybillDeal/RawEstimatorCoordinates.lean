import GraybillDeal.CanonicalClipping
import GraybillDeal.RawNormalSummary

/-!
# Identification of the canonical and ordinary raw estimators

This file is the deterministic endpoint of the raw-sample bridge.  For two
samples of size thirteen, write

* `D = sampleMean₁ - sampleMean₀`,
* `r = S₀² / (S₀² + S₁²)`,
* `q = 13 D² / (S₀² + S₁²)`.

The ordinary Graybill--Deal estimator is `sampleMean₀ + r D`.  Its proposed
competitor replaces `r` by

`clip01 (r + epsilon13 * r * (1-r) * (1-2r) * (4-q))`.

Under the explicit nonvanishing assumptions needed by the ratios, the
theorems below identify these raw expressions pointwise with the canonical
expressions used by the risk theorem.
-/

namespace GraybillDeal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The observed Graybill--Deal weight for two samples of size thirteen. -/
def rawGraybillDealWeight13
    (X : Fin 2 → Fin 13 → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleVariance13 (X 0) ω
    / (sampleVariance13 (X 0) ω + sampleVariance13 (X 1) ω)

/-- The raw quadratic statistic occurring in the perturbation direction. -/
def rawQuadraticStatistic13
    (X : Fin 2 → Fin 13 → Ω → ℝ) (ω : Ω) : ℝ :=
  13 * meanDifference13 X ω ^ 2
    / (sampleVariance13 (X 0) ω + sampleVariance13 (X 1) ω)

/-- The ordinary Graybill--Deal estimator. -/
def rawGraybillDealEstimator13
    (X : Fin 2 → Fin 13 → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleMean13 (X 0) ω
    + rawGraybillDealWeight13 X ω * meanDifference13 X ω

/--
The proposed clipped perturbation of the observed Graybill--Deal weight.
-/
def rawClippedPerturbedWeight13
    (X : Fin 2 → Fin 13 → Ω → ℝ) (ω : Ω) : ℝ :=
  let r := rawGraybillDealWeight13 X ω
  let q := rawQuadraticStatistic13 X ω
  clip01
    (r + epsilon13 * r * (1 - r) * (1 - 2 * r) * (4 - q))

/-- The raw estimator obtained from the clipped perturbed weight. -/
def rawClippedPerturbedEstimator13
    (X : Fin 2 → Fin 13 → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleMean13 (X 0) ω
    + rawClippedPerturbedWeight13 X ω * meanDifference13 X ω

/--
The canonical population weight is the oracle inverse-variance weight.
-/
theorem canonicalTheta_eq_oracleVarianceWeight13
    {variance : Fin 2 → NNReal}
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    canonicalTheta
        (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
      =
    oracleVarianceWeight13 variance := by
  rw [canonicalTheta_rawVarianceContrast]
  · rfl
  · unfold rawVarianceSum
    exact ne_of_gt (add_pos hvariance₀ hvariance₁)

/--
The raw standardized residual coordinate `U_g` is exactly
`12 S_g² / variance_g`.
-/
theorem normalRawU13_eq_rawResidualScale13
    (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin 13 → Ω → ℝ) (g : Fin 2) (ω : Ω) :
    normalRawU13 variance X g ω
      =
    rawResidualScale13 (variance g) (sampleVariance13 (X g) ω) := by
  unfold normalRawU13 scaledResidualSumSquares13 rawResidualScale13
  rw [← twelve_mul_sampleVariance13]

/-- The raw beta ratio coordinate agrees with `rawResidualP13`. -/
theorem normalRawP13_eq_rawResidualP13
    (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin 13 → Ω → ℝ) (ω : Ω) :
    normalRawP13 variance X ω
      =
    rawResidualP13
      (variance 0) (variance 1)
      (sampleVariance13 (X 0) ω) (sampleVariance13 (X 1) ω) := by
  unfold normalRawP13 rawResidualP13 rawResidualL13
  rw [normalRawU13_eq_rawResidualScale13,
    normalRawU13_eq_rawResidualScale13]

/-- The raw gamma sum coordinate agrees with `rawResidualL13`. -/
theorem normalRawL13_eq_rawResidualL13
    (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin 13 → Ω → ℝ) (ω : Ω) :
    normalRawL13 variance X ω
      =
    rawResidualL13
      (variance 0) (variance 1)
      (sampleVariance13 (X 0) ω) (sampleVariance13 (X 1) ω) := by
  unfold normalRawL13 rawResidualL13
  rw [normalRawU13_eq_rawResidualScale13,
    normalRawU13_eq_rawResidualScale13]

/-- The raw squared mean-difference coordinate used in the canonical law. -/
def normalRawV13
    (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin 13 → Ω → ℝ) (ω : Ω) : ℝ :=
  standardizedDifference13
    (normalVarianceSum13 variance) (meanDifference13 X ω)

/--
`normalRawV13` is the `standardizedDifference13` coordinate associated with
the raw population-variance sum.
-/
theorem normalRawV13_eq_raw_standardizedDifference13
    (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin 13 → Ω → ℝ) (ω : Ω) :
    normalRawV13 variance X ω
      =
    standardizedDifference13
      (rawVarianceSum (variance 0) (variance 1))
      (meanDifference13 X ω) := by
  rfl

/--
The canonical base weight is exactly the observed Graybill--Deal weight.
-/
theorem canonicalR_eq_rawGraybillDealWeight13
    {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin 13 → Ω → ℝ} {ω : Ω}
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ))
    (hL :
      normalRawL13 variance X ω ≠ 0)
    (hSsum :
      sampleVariance13 (X 0) ω + sampleVariance13 (X 1) ω ≠ 0) :
    canonicalR
        (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
        (normalRawP13 variance X ω)
      =
    rawGraybillDealWeight13 X ω := by
  rw [normalRawP13_eq_rawResidualP13]
  unfold rawGraybillDealWeight13
  apply canonicalR_rawResidualP13
  · exact ne_of_gt hvariance₀
  · exact ne_of_gt hvariance₁
  · unfold rawVarianceSum
    exact ne_of_gt (add_pos hvariance₀ hvariance₁)
  · rwa [← normalRawL13_eq_rawResidualL13]
  · exact hSsum

/--
The canonical statistic `q` is exactly the raw statistic
`13 D² / (S₀² + S₁²)`.
-/
theorem canonicalQ13_eq_rawQuadraticStatistic13
    {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin 13 → Ω → ℝ} {ω : Ω}
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ))
    (hL :
      normalRawL13 variance X ω ≠ 0)
    (hSsum :
      sampleVariance13 (X 0) ω + sampleVariance13 (X 1) ω ≠ 0) :
    canonicalQ13
        (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
        (normalRawP13 variance X ω)
        (normalRawL13 variance X ω)
        (normalRawV13 variance X ω)
      =
    rawQuadraticStatistic13 X ω := by
  rw [normalRawP13_eq_rawResidualP13,
    normalRawL13_eq_rawResidualL13,
    normalRawV13_eq_raw_standardizedDifference13]
  unfold rawQuadraticStatistic13
  apply canonicalQ13_rawResidual_coordinates
  · exact ne_of_gt hvariance₀
  · exact ne_of_gt hvariance₁
  · unfold rawVarianceSum
    exact ne_of_gt (add_pos hvariance₀ hvariance₁)
  · rwa [← normalRawL13_eq_rawResidualL13]
  · exact hSsum

/--
The clipped canonical perturbed weight is exactly the explicit raw clipped
perturbation.
-/
theorem canonicalClippedWeight13_eq_rawClippedPerturbedWeight13
    {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin 13 → Ω → ℝ} {ω : Ω}
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ))
    (hL :
      normalRawL13 variance X ω ≠ 0)
    (hSsum :
      sampleVariance13 (X 0) ω + sampleVariance13 (X 1) ω ≠ 0) :
    canonicalClippedWeight13 epsilon13
        (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
        (normalRawP13 variance X ω)
        (normalRawL13 variance X ω)
        (normalRawV13 variance X ω)
      =
    rawClippedPerturbedWeight13 X ω := by
  unfold canonicalClippedWeight13 canonicalWeight13 canonicalH13
  unfold perturbation weightPolynomial rawClippedPerturbedWeight13
  rw [show
      canonicalR
          (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
          (normalRawP13 variance X ω)
        = rawGraybillDealWeight13 X ω from
      canonicalR_eq_rawGraybillDealWeight13
        hvariance₀ hvariance₁ hL hSsum]
  rw [show
      canonicalQ13
          (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
          (normalRawP13 variance X ω)
          (normalRawL13 variance X ω)
          (normalRawV13 variance X ω)
        = rawQuadraticStatistic13 X ω from
      canonicalQ13_eq_rawQuadraticStatistic13
        hvariance₀ hvariance₁ hL hSsum]
  congr 1
  ring

/--
The preceding identification with the raw perturbation formula displayed
literally.
-/
theorem canonicalClippedWeight13_eq_raw_formula
    {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin 13 → Ω → ℝ} {ω : Ω}
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ))
    (hL :
      normalRawL13 variance X ω ≠ 0)
    (hSsum :
      sampleVariance13 (X 0) ω + sampleVariance13 (X 1) ω ≠ 0) :
    canonicalClippedWeight13 epsilon13
        (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
        (normalRawP13 variance X ω)
        (normalRawL13 variance X ω)
        (normalRawV13 variance X ω)
      =
    let r := rawGraybillDealWeight13 X ω
    let q := rawQuadraticStatistic13 X ω
    clip01
      (r + epsilon13 * r * (1 - r) * (1 - 2 * r) * (4 - q)) := by
  exact canonicalClippedWeight13_eq_rawClippedPerturbedWeight13
    hvariance₀ hvariance₁ hL hSsum

/--
The ordinary estimator also has its familiar symmetric numerator form.
-/
theorem rawGraybillDealEstimator13_eq_ratio
    {X : Fin 2 → Fin 13 → Ω → ℝ} {ω : Ω}
    (hSsum :
      sampleVariance13 (X 0) ω + sampleVariance13 (X 1) ω ≠ 0) :
    rawGraybillDealEstimator13 X ω
      =
    (sampleVariance13 (X 1) ω * sampleMean13 (X 0) ω
        + sampleVariance13 (X 0) ω * sampleMean13 (X 1) ω)
      / (sampleVariance13 (X 0) ω + sampleVariance13 (X 1) ω) := by
  unfold rawGraybillDealEstimator13 rawGraybillDealWeight13
  unfold meanDifference13
  field_simp [hSsum]
  ring

/--
The full canonical baseline estimator expression is exactly the ordinary
Graybill--Deal estimator.
-/
theorem canonicalBaseEstimator13_eq_rawGraybillDealEstimator13
    {μ : ℝ} {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin 13 → Ω → ℝ} {ω : Ω}
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ))
    (hL :
      normalRawL13 variance X ω ≠ 0)
    (hSsum :
      sampleVariance13 (X 0) ω + sampleVariance13 (X 1) ω ≠ 0) :
    μ
        + oracleCenteredError13 μ
            (oracleVarianceWeight13 variance) X ω
        + meanDifference13 X ω
          * (canonicalR
                (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
                (normalRawP13 variance X ω)
              - canonicalTheta
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ)))
      =
    rawGraybillDealEstimator13 X ω := by
  rw [canonicalR_eq_rawGraybillDealWeight13
      hvariance₀ hvariance₁ hL hSsum,
    canonicalTheta_eq_oracleVarianceWeight13 hvariance₀ hvariance₁]
  unfold oracleCenteredError13 rawGraybillDealEstimator13
  ring

/--
The full canonical clipped estimator expression is exactly the ordinary raw
clipped perturbation.
-/
theorem canonicalClippedEstimator13_eq_rawClippedPerturbedEstimator13
    {μ : ℝ} {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin 13 → Ω → ℝ} {ω : Ω}
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ))
    (hL :
      normalRawL13 variance X ω ≠ 0)
    (hSsum :
      sampleVariance13 (X 0) ω + sampleVariance13 (X 1) ω ≠ 0) :
    μ
        + oracleCenteredError13 μ
            (oracleVarianceWeight13 variance) X ω
        + meanDifference13 X ω
          * (canonicalClippedWeight13 epsilon13
                (rawVarianceContrast (variance 0 : ℝ) (variance 1 : ℝ))
                (normalRawP13 variance X ω)
                (normalRawL13 variance X ω)
                (normalRawV13 variance X ω)
              - canonicalTheta
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ)))
      =
    rawClippedPerturbedEstimator13 X ω := by
  rw [canonicalClippedWeight13_eq_rawClippedPerturbedWeight13
      hvariance₀ hvariance₁ hL hSsum,
    canonicalTheta_eq_oracleVarianceWeight13 hvariance₀ hvariance₁]
  unfold oracleCenteredError13 rawClippedPerturbedEstimator13
  ring

end

end GraybillDeal
