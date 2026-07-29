import GraybillDeal.UnequalDampedRawPositivity
import GraybillDeal.UnequalDampedAlgebra

/-!
# Literal `(13,17)` Graybill--Deal estimators

For the first and second unbiased sample variances `S₁²,S₂²`, put

`A₁ = S₁²/13`, `A₂ = S₂²/17`.

The ordinary Graybill--Deal weight on `Ȳ-X̄` is `A₁/(A₁+A₂)`.  The fixed
competitor adds

`ε φ(r) (c - D²/(A₁+A₂))`

and clips the resulting weight to `[0,1]`.
-/

namespace GraybillDeal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Estimated variance of the first sample mean. -/
def rawMeanVariance1_13
    (X : Fin 13 → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleVarianceN 12 X ω / 13

/-- Estimated variance of the second sample mean. -/
def rawMeanVariance2_17
    (Y : Fin 17 → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleVarianceN 16 Y ω / 17

/-- Sum of the two estimated variances of the sample means. -/
def rawMeanVarianceSum13_17
    (X : Fin 13 → Ω → ℝ) (Y : Fin 17 → Ω → ℝ)
    (ω : Ω) : ℝ :=
  rawMeanVariance1_13 X ω + rawMeanVariance2_17 Y ω

/-- The observed unequal-size Graybill--Deal weight. -/
def rawGraybillDealWeight13_17
    (X : Fin 13 → Ω → ℝ) (Y : Fin 17 → Ω → ℝ)
    (ω : Ω) : ℝ :=
  rawMeanVariance1_13 X ω / rawMeanVarianceSum13_17 X Y ω

/-- The raw quadratic statistic `D²/(A₁+A₂)`. -/
def rawQuadraticStatistic13_17
    (X : Fin 13 → Ω → ℝ) (Y : Fin 17 → Ω → ℝ)
    (ω : Ω) : ℝ :=
  meanDifferenceU 12 16 X Y ω ^ 2 / rawMeanVarianceSum13_17 X Y ω

/-- The ordinary unequal-size Graybill--Deal estimator. -/
def rawGraybillDealEstimator13_17
    (X : Fin 13 → Ω → ℝ) (Y : Fin 17 → Ω → ℝ)
    (ω : Ω) : ℝ :=
  sampleMeanN 12 X ω
    + rawGraybillDealWeight13_17 X Y ω
      * meanDifferenceU 12 16 X Y ω

/-- The literal un-clipped fixed unequal-size perturbation. -/
def rawPerturbedWeight13_17
    (ε : ℝ)
    (X : Fin 13 → Ω → ℝ) (Y : Fin 17 → Ω → ℝ)
    (ω : Ω) : ℝ :=
  let r := rawGraybillDealWeight13_17 X Y ω
  let q := rawQuadraticStatistic13_17 X Y ω
  r + ε * unequalDampedPhi13_17 r * (unequalDampedC13_17 - q)

/-- The literal perturbed weight projected to `[0,1]`. -/
def rawClippedPerturbedWeight13_17
    (ε : ℝ)
    (X : Fin 13 → Ω → ℝ) (Y : Fin 17 → Ω → ℝ)
    (ω : Ω) : ℝ :=
  clip01 (rawPerturbedWeight13_17 ε X Y ω)

/-- The raw estimator using the un-clipped perturbed weight. -/
def rawPerturbedEstimator13_17
    (ε : ℝ)
    (X : Fin 13 → Ω → ℝ) (Y : Fin 17 → Ω → ℝ)
    (ω : Ω) : ℝ :=
  sampleMeanN 12 X ω
    + rawPerturbedWeight13_17 ε X Y ω
      * meanDifferenceU 12 16 X Y ω

/-- The raw estimator using the clipped perturbed weight. -/
def rawClippedPerturbedEstimator13_17
    (ε : ℝ)
    (X : Fin 13 → Ω → ℝ) (Y : Fin 17 → Ω → ℝ)
    (ω : Ω) : ℝ :=
  sampleMeanN 12 X ω
    + rawClippedPerturbedWeight13_17 ε X Y ω
      * meanDifferenceU 12 16 X Y ω

/-- The ordinary estimator in its familiar inverse-variance numerator form. -/
theorem rawGraybillDealEstimator13_17_eq_ratio
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ} {ω : Ω}
    (hA : rawMeanVarianceSum13_17 X Y ω ≠ 0) :
    rawGraybillDealEstimator13_17 X Y ω
      =
    (rawMeanVariance2_17 Y ω * sampleMeanN 12 X ω
        + rawMeanVariance1_13 X ω * sampleMeanN 16 Y ω)
      / rawMeanVarianceSum13_17 X Y ω := by
  have hsum :
      rawMeanVariance1_13 X ω + rawMeanVariance2_17 Y ω ≠ 0 := by
    simpa [rawMeanVarianceSum13_17] using hA
  unfold rawGraybillDealEstimator13_17 rawGraybillDealWeight13_17
  unfold meanDifferenceU rawMeanVarianceSum13_17
  field_simp [hsum]
  ring

end

end GraybillDeal
