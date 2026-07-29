import GraybillDeal.UnequalFixedDifferenceFourRawSummary
import GraybillDeal.UnequalFixedDifferenceFourCoordinates

/-!
# Literal Graybill--Deal estimators for the fixed-difference-four family

For the unbiased sample variances `S₁²,S₂²`, put

`A₁ = S₁²/(2m-1)` and `A₂ = S₂²/(2m+3)`.

The ordinary Graybill--Deal weight on `Ȳ-X̄` is `A₁/(A₁+A₂)`.  The family
competitor adds

`ε Φₘ(r) (cₘ - D²/(A₁+A₂))`

and clips the resulting weight to `[0,1]`.

The sample index types remain in residual-degrees-of-freedom form, as in
`UnequalFixedDifferenceFourRawSummary.lean`.
-/

namespace GraybillDeal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Estimated variance of the first sample mean. -/
def unequalFixedDifferenceFourRawMeanVariance1
    (m : ℕ)
    (X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  sampleVarianceN (unequalFixedDifferenceFourResidualDF1 m) X ω
    / (unequalFixedDifferenceFourResidualDF1 m + 1)

/-- Estimated variance of the second sample mean. -/
def unequalFixedDifferenceFourRawMeanVariance2
    (m : ℕ)
    (Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  sampleVarianceN (unequalFixedDifferenceFourResidualDF2 m) Y ω
    / (unequalFixedDifferenceFourResidualDF2 m + 1)

/-- Sum of the two estimated sample-mean variances. -/
def unequalFixedDifferenceFourRawMeanVarianceSum
    (m : ℕ)
    (X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  unequalFixedDifferenceFourRawMeanVariance1 m X ω
    + unequalFixedDifferenceFourRawMeanVariance2 m Y ω

/-- The observed unequal-size Graybill--Deal weight. -/
def unequalFixedDifferenceFourRawGraybillDealWeight
    (m : ℕ)
    (X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  unequalFixedDifferenceFourRawMeanVariance1 m X ω
    / unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω

/-- The raw quadratic statistic `D²/(A₁+A₂)`. -/
def unequalFixedDifferenceFourRawQuadraticStatistic
    (m : ℕ)
    (X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  meanDifferenceU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m) X Y ω ^ 2
    / unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω

/-- The ordinary unequal-size Graybill--Deal estimator. -/
def unequalFixedDifferenceFourRawGraybillDealEstimator
    (m : ℕ)
    (X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  sampleMeanN (unequalFixedDifferenceFourResidualDF1 m) X ω
    + unequalFixedDifferenceFourRawGraybillDealWeight m X Y ω
      * meanDifferenceU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) X Y ω

/-- The literal un-clipped family perturbation. -/
def unequalFixedDifferenceFourRawPerturbedWeight
    (ε : ℝ) (m : ℕ)
    (X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  let r := unequalFixedDifferenceFourRawGraybillDealWeight m X Y ω
  let q := unequalFixedDifferenceFourRawQuadraticStatistic m X Y ω
  r + ε
    * unequalDampedPhi
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourKappa m) r
    * (unequalFixedDifferenceFourC m - q)

/-- The literal family perturbation projected to `[0,1]`. -/
def unequalFixedDifferenceFourRawClippedPerturbedWeight
    (ε : ℝ) (m : ℕ)
    (X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  clip01
    (unequalFixedDifferenceFourRawPerturbedWeight ε m X Y ω)

/-- The raw estimator using the un-clipped perturbed weight. -/
def unequalFixedDifferenceFourRawPerturbedEstimator
    (ε : ℝ) (m : ℕ)
    (X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  sampleMeanN (unequalFixedDifferenceFourResidualDF1 m) X ω
    + unequalFixedDifferenceFourRawPerturbedWeight ε m X Y ω
      * meanDifferenceU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) X Y ω

/-- The raw estimator using the clipped perturbed weight. -/
def unequalFixedDifferenceFourRawClippedPerturbedEstimator
    (ε : ℝ) (m : ℕ)
    (X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ)
    (ω : Ω) : ℝ :=
  sampleMeanN (unequalFixedDifferenceFourResidualDF1 m) X ω
    + unequalFixedDifferenceFourRawClippedPerturbedWeight ε m X Y ω
      * meanDifferenceU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) X Y ω

/--
The ordinary estimator in its familiar inverse-variance numerator form.
-/
theorem unequalFixedDifferenceFourRawGraybillDealEstimator_eq_ratio
    {m : ℕ}
    {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    {ω : Ω}
    (hA : unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω ≠ 0) :
    unequalFixedDifferenceFourRawGraybillDealEstimator m X Y ω
      =
    (unequalFixedDifferenceFourRawMeanVariance2 m Y ω
          * sampleMeanN (unequalFixedDifferenceFourResidualDF1 m) X ω
        + unequalFixedDifferenceFourRawMeanVariance1 m X ω
          * sampleMeanN (unequalFixedDifferenceFourResidualDF2 m) Y ω)
      / unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω := by
  have hsum :
      unequalFixedDifferenceFourRawMeanVariance1 m X ω
          + unequalFixedDifferenceFourRawMeanVariance2 m Y ω
        ≠ 0 := by
    simpa only [unequalFixedDifferenceFourRawMeanVarianceSum] using hA
  unfold unequalFixedDifferenceFourRawGraybillDealEstimator
    unequalFixedDifferenceFourRawGraybillDealWeight
  unfold meanDifferenceU
    unequalFixedDifferenceFourRawMeanVarianceSum
  field_simp [hsum]
  ring

end

end GraybillDeal
