import GraybillDeal.UnequalFixedDifferenceFourAllNRawSummary
import GraybillDeal.UnequalFixedDifferenceFourRealCanonical

/-!
# Literal Graybill--Deal estimators on the full difference-four diagonal

For sample sizes `(n,n+4)`, written internally with residual degrees of
freedom

* `ν₁ = n-1`;
* `ν₂ = n+3`,

put `A₁=S₁²/n` and `A₂=S₂²/(n+4)`.  The ordinary Graybill--Deal weight on
`Ȳ-X̄` is `A₁/(A₁+A₂)`.

The real analytic family parameter is

`mₙ = unequalFixedDifferenceFourSampleM n = (n+1)/2`.

The literal competitor adds

`ε Φ_{mₙ}(r) (c_{mₙ} - D²/(A₁+A₂))`

and clips the resulting weight to `[0,1]`.  No parity assumption on `n`
occurs in these definitions.
-/

namespace GraybillDeal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Estimated variance of the first sample mean, `S₁²/n`. -/
def unequalFixedDifferenceFourAllNRawMeanVariance1
    (n : ℕ)
    (X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  sampleVarianceN (unequalFixedDifferenceFourAllNResidualDF1 n) X ω
    / (unequalFixedDifferenceFourAllNResidualDF1 n + 1)

/-- Estimated variance of the second sample mean, `S₂²/(n+4)`. -/
def unequalFixedDifferenceFourAllNRawMeanVariance2
    (n : ℕ)
    (Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  sampleVarianceN (unequalFixedDifferenceFourAllNResidualDF2 n) Y ω
    / (unequalFixedDifferenceFourAllNResidualDF2 n + 1)

/-- Sum of the two estimated sample-mean variances. -/
def unequalFixedDifferenceFourAllNRawMeanVarianceSum
    (n : ℕ)
    (X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  unequalFixedDifferenceFourAllNRawMeanVariance1 n X ω
    + unequalFixedDifferenceFourAllNRawMeanVariance2 n Y ω

/-- The observed unequal-size Graybill--Deal weight. -/
def unequalFixedDifferenceFourAllNRawGraybillDealWeight
    (n : ℕ)
    (X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  unequalFixedDifferenceFourAllNRawMeanVariance1 n X ω
    / unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω

/-- The raw quadratic statistic `D²/(A₁+A₂)`. -/
def unequalFixedDifferenceFourAllNRawQuadraticStatistic
    (n : ℕ)
    (X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  meanDifferenceU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω ^ 2
    / unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω

/-- The ordinary unequal-size Graybill--Deal estimator. -/
def unequalFixedDifferenceFourAllNRawGraybillDealEstimator
    (n : ℕ)
    (X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  sampleMeanN (unequalFixedDifferenceFourAllNResidualDF1 n) X ω
    + unequalFixedDifferenceFourAllNRawGraybillDealWeight n X Y ω
      * meanDifferenceU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω

/-- The literal un-clipped difference-four perturbation. -/
def unequalFixedDifferenceFourAllNRawPerturbedWeight
    (ε : ℝ) (n : ℕ)
    (X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  let m := unequalFixedDifferenceFourSampleM n
  let r := unequalFixedDifferenceFourAllNRawGraybillDealWeight n X Y ω
  let q := unequalFixedDifferenceFourAllNRawQuadraticStatistic n X Y ω
  r + ε
    * unequalDampedPhi
        (unequalFixedDifferenceFourRealT m)
        (unequalFixedDifferenceFourRealKappa m) r
    * (unequalFixedDifferenceFourRealC m - q)

/-- The literal difference-four perturbation projected to `[0,1]`. -/
def unequalFixedDifferenceFourAllNRawClippedPerturbedWeight
    (ε : ℝ) (n : ℕ)
    (X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  clip01
    (unequalFixedDifferenceFourAllNRawPerturbedWeight ε n X Y ω)

/-- The raw estimator using the un-clipped perturbed weight. -/
def unequalFixedDifferenceFourAllNRawPerturbedEstimator
    (ε : ℝ) (n : ℕ)
    (X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  sampleMeanN (unequalFixedDifferenceFourAllNResidualDF1 n) X ω
    + unequalFixedDifferenceFourAllNRawPerturbedWeight ε n X Y ω
      * meanDifferenceU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω

/-- The raw estimator using the clipped perturbed weight. -/
def unequalFixedDifferenceFourAllNRawClippedPerturbedEstimator
    (ε : ℝ) (n : ℕ)
    (X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  sampleMeanN (unequalFixedDifferenceFourAllNResidualDF1 n) X ω
    + unequalFixedDifferenceFourAllNRawClippedPerturbedWeight ε n X Y ω
      * meanDifferenceU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω

/--
The ordinary estimator in its familiar inverse-variance numerator form.
-/
theorem unequalFixedDifferenceFourAllNRawGraybillDealEstimator_eq_ratio
    {n : ℕ}
    {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    {ω : Ω}
    (hA : unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω ≠ 0) :
    unequalFixedDifferenceFourAllNRawGraybillDealEstimator n X Y ω
      =
    (unequalFixedDifferenceFourAllNRawMeanVariance2 n Y ω
          * sampleMeanN
              (unequalFixedDifferenceFourAllNResidualDF1 n) X ω
        + unequalFixedDifferenceFourAllNRawMeanVariance1 n X ω
          * sampleMeanN
              (unequalFixedDifferenceFourAllNResidualDF2 n) Y ω)
      / unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω := by
  have hsum :
      unequalFixedDifferenceFourAllNRawMeanVariance1 n X ω
          + unequalFixedDifferenceFourAllNRawMeanVariance2 n Y ω
        ≠ 0 := by
    simpa only [unequalFixedDifferenceFourAllNRawMeanVarianceSum] using hA
  unfold unequalFixedDifferenceFourAllNRawGraybillDealEstimator
    unequalFixedDifferenceFourAllNRawGraybillDealWeight
  unfold meanDifferenceU
    unequalFixedDifferenceFourAllNRawMeanVarianceSum
  field_simp [hsum]
  ring

end

end GraybillDeal
