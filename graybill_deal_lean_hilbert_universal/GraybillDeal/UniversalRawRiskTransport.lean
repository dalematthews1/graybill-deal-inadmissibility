import GraybillDeal.Risk
import GraybillDeal.UnequalNormalSample

/-!
# Universal raw-sample risk transport

This file is the sample-size-generic raw layer for the universal
Graybill--Deal argument.  The natural-number parameters `ν₁, ν₂` are the
residual degrees of freedom, so the corresponding sample sizes are
`n₁ = ν₁ + 1` and `n₂ = ν₂ + 1`.  Thus the assumptions `0 < ν₁` and
`0 < ν₂` are exactly `n₁, n₂ ≥ 2`.

For the two unbiased sample variances `S₁²,S₂²`, set

* `A₁ = S₁² / n₁`,
* `A₂ = S₂² / n₂`,
* `r = A₁ / (A₁ + A₂)`,
* `q = (Ȳ-X̄)² / (A₁ + A₂)`.

The ordinary Graybill--Deal estimator is `X̄ + r (Ȳ-X̄)`.  An arbitrary
reduced rule `δ : ℝ × ℝ → ℝ` gives the raw estimator
`X̄ + δ(r,q) (Ȳ-X̄)`.

The main theorem in this file says that a strict comparison of the reduced
weighted squared risks

`E[D² (δ(r,q)-θ)²] < E[D² (r-θ)²]`

implies the corresponding strict comparison of the raw common-mean risks.
Here `D = Ȳ-X̄` and `θ` is the known-variance oracle weight.  All
integrability assumptions are explicit.  The cross terms are not assumed:
they are proved to vanish from the arbitrary-size normal-sample oracle
independence theorem in `UnequalNormalSample.lean`.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Literal arbitrary-size raw coordinates -/

/-- Estimated variance `S₁² / n₁` of the first sample mean. -/
def universalRawMeanVariance1
    (ν₁ : ℕ) (X : Fin (ν₁ + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleVarianceN ν₁ X ω / (ν₁ + 1)

/-- Estimated variance `S₂² / n₂` of the second sample mean. -/
def universalRawMeanVariance2
    (ν₂ : ℕ) (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleVarianceN ν₂ Y ω / (ν₂ + 1)

/-- Sum `S₁²/n₁ + S₂²/n₂` of the estimated mean variances. -/
def universalRawMeanVarianceSum
    (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  universalRawMeanVariance1 ν₁ X ω
    + universalRawMeanVariance2 ν₂ Y ω

/-- The literal arbitrary-size Graybill--Deal weight. -/
def universalRawGraybillDealWeight
    (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  universalRawMeanVariance1 ν₁ X ω
    / universalRawMeanVarianceSum ν₁ ν₂ X Y ω

/-- The scale-free quadratic coordinate `q = D²/(A₁+A₂)`. -/
def universalRawQ
    (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  meanDifferenceU ν₁ ν₂ X Y ω ^ 2
    / universalRawMeanVarianceSum ν₁ ν₂ X Y ω

/-- The pair `(r,q)` of reduced raw coordinates. -/
def universalRawReducedCoordinates
    (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) : ℝ × ℝ :=
  (universalRawGraybillDealWeight ν₁ ν₂ X Y ω,
    universalRawQ ν₁ ν₂ X Y ω)

/-- Apply an arbitrary reduced rule to the literal raw coordinates. -/
def universalRawReducedWeight
    (δ : ℝ × ℝ → ℝ) (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  δ (universalRawReducedCoordinates ν₁ ν₂ X Y ω)

/-- The raw common-mean estimator induced by a reduced weight rule. -/
def universalRawReducedEstimator
    (δ : ℝ × ℝ → ℝ) (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleMeanN ν₁ X ω
    + universalRawReducedWeight δ ν₁ ν₂ X Y ω
      * meanDifferenceU ν₁ ν₂ X Y ω

/-- The ordinary arbitrary-size Graybill--Deal estimator. -/
def universalRawGraybillDealEstimator
    (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleMeanN ν₁ X ω
    + universalRawGraybillDealWeight ν₁ ν₂ X Y ω
      * meanDifferenceU ν₁ ν₂ X Y ω

/-- The parameter-space oracle coordinate
`θ = (v₁/n₁)/(v₁/n₁+v₂/n₂)`. -/
def universalRawOracleTheta
    (ν₁ ν₂ : ℕ) (v₁ v₂ : NNReal) : ℝ :=
  oracleVarianceWeightU ν₁ ν₂ v₁ v₂

/-- The oracle-centered regression error. -/
def universalRawOracleError
    (ν₁ ν₂ : ℕ) (μ : ℝ) (v₁ v₂ : NNReal)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  oracleCenteredErrorU ν₁ ν₂ μ
    (universalRawOracleTheta ν₁ ν₂ v₁ v₂) X Y ω

/-! ## Pure sufficient-summary coordinates -/

/--
Turn an unnormalised residual sum of squares into the estimated variance of
the corresponding sample mean.
-/
def universalMeanVarianceOfRSS (ν : ℕ) (rss : ℝ) : ℝ :=
  (rss / ν) / (ν + 1)

/--
The ordering used by `UnequalNormalSample` is `(D,RSS₁,RSS₂)`.  The
right-associated product type `ℝ × ℝ × ℝ` therefore has the corresponding
fields `z.1, z.2.1, z.2.2`.
-/
def universalSummaryTriple
    (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) : ℝ × ℝ × ℝ :=
  (meanDifferenceU ν₁ ν₂ X Y ω,
    residualSumSquaresN ν₁ X ω,
    residualSumSquaresN ν₂ Y ω)

/-- The reduced coordinates as a pure function of `(D,RSS₁,RSS₂)`. -/
def universalReducedCoordinatesOfSummary
    (ν₁ ν₂ : ℕ) (z : ℝ × ℝ × ℝ) : ℝ × ℝ :=
  let D := z.1
  let A₁ := universalMeanVarianceOfRSS ν₁ z.2.1
  let A₂ := universalMeanVarianceOfRSS ν₂ z.2.2
  (A₁ / (A₁ + A₂), D ^ 2 / (A₁ + A₂))

/-- The regression factor associated with a reduced rule. -/
def universalReducedRuleFactorOfSummary
    (δ : ℝ × ℝ → ℝ) (ν₁ ν₂ : ℕ) (θ : ℝ)
    (z : ℝ × ℝ × ℝ) : ℝ :=
  z.1 * (δ (universalReducedCoordinatesOfSummary ν₁ ν₂ z) - θ)

/-! ## Elementary coordinate and regression identities -/

theorem universalRawReducedCoordinates_eq_summary
    {ν₁ ν₂ : ℕ}
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) :
    universalRawReducedCoordinates ν₁ ν₂ X Y ω =
      universalReducedCoordinatesOfSummary ν₁ ν₂
        (universalSummaryTriple ν₁ ν₂ X Y ω) := by
  rfl

theorem universalRawReducedWeight_eq_summary
    (δ : ℝ × ℝ → ℝ) {ν₁ ν₂ : ℕ}
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) :
    universalRawReducedWeight δ ν₁ ν₂ X Y ω =
      δ (universalReducedCoordinatesOfSummary ν₁ ν₂
        (universalSummaryTriple ν₁ ν₂ X Y ω)) := by
  rfl

theorem universalReducedRuleFactorOfSummary_apply
    (δ : ℝ × ℝ → ℝ) {ν₁ ν₂ : ℕ} (θ : ℝ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) :
    universalReducedRuleFactorOfSummary δ ν₁ ν₂ θ
        (universalSummaryTriple ν₁ ν₂ X Y ω)
      =
    meanDifferenceU ν₁ ν₂ X Y ω
      * (universalRawReducedWeight δ ν₁ ν₂ X Y ω - θ) := by
  rfl

/--
Every weighted sample-mean estimator has the exact oracle regression
decomposition

`X̄ + wD = μ + T + D(w-θ)`.
-/
theorem rawWeightedEstimator_eq_oracle_decomposition
    (μ θ : ℝ) {ν₁ ν₂ : ℕ}
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ)
    (w : Ω → ℝ) (ω : Ω) :
    sampleMeanN ν₁ X ω + w ω * meanDifferenceU ν₁ ν₂ X Y ω
      =
    μ + oracleCenteredErrorU ν₁ ν₂ μ θ X Y ω
      + meanDifferenceU ν₁ ν₂ X Y ω * (w ω - θ) := by
  unfold oracleCenteredErrorU
  ring

theorem universalRawReducedEstimator_eq_oracle_decomposition
    (δ : ℝ × ℝ → ℝ) {ν₁ ν₂ : ℕ}
    (μ : ℝ) (v₁ v₂ : NNReal)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) :
    universalRawReducedEstimator δ ν₁ ν₂ X Y ω
      =
    μ + universalRawOracleError ν₁ ν₂ μ v₁ v₂ X Y ω
      + meanDifferenceU ν₁ ν₂ X Y ω
        * (universalRawReducedWeight δ ν₁ ν₂ X Y ω
          - universalRawOracleTheta ν₁ ν₂ v₁ v₂) := by
  exact rawWeightedEstimator_eq_oracle_decomposition
    μ (universalRawOracleTheta ν₁ ν₂ v₁ v₂) X Y
    (universalRawReducedWeight δ ν₁ ν₂ X Y) ω

theorem universalRawGraybillDealEstimator_eq_oracle_decomposition
    {ν₁ ν₂ : ℕ}
    (μ : ℝ) (v₁ v₂ : NNReal)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) :
    universalRawGraybillDealEstimator ν₁ ν₂ X Y ω
      =
    μ + universalRawOracleError ν₁ ν₂ μ v₁ v₂ X Y ω
      + meanDifferenceU ν₁ ν₂ X Y ω
        * (universalRawGraybillDealWeight ν₁ ν₂ X Y ω
          - universalRawOracleTheta ν₁ ν₂ v₁ v₂) := by
  exact rawWeightedEstimator_eq_oracle_decomposition
    μ (universalRawOracleTheta ν₁ ν₂ v₁ v₂) X Y
    (universalRawGraybillDealWeight ν₁ ν₂ X Y) ω

/-- Familiar inverse-estimated-variance form of the ordinary estimator. -/
theorem universalRawGraybillDealEstimator_eq_ratio
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ} {ω : Ω}
    (hsum : universalRawMeanVarianceSum ν₁ ν₂ X Y ω ≠ 0) :
    universalRawGraybillDealEstimator ν₁ ν₂ X Y ω
      =
    (universalRawMeanVariance2 ν₂ Y ω * sampleMeanN ν₁ X ω
        + universalRawMeanVariance1 ν₁ X ω * sampleMeanN ν₂ Y ω)
      / universalRawMeanVarianceSum ν₁ ν₂ X Y ω := by
  unfold universalRawGraybillDealEstimator
    universalRawGraybillDealWeight meanDifferenceU
  have hsum' :
      universalRawMeanVariance1 ν₁ X ω
          + universalRawMeanVariance2 ν₂ Y ω ≠ 0 := by
    simpa only [universalRawMeanVarianceSum] using hsum
  unfold universalRawMeanVarianceSum
  field_simp [hsum']
  ring

/-! ## Measurability -/

@[measurability, fun_prop]
theorem measurable_universalRawReducedCoordinates
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j)) :
    Measurable (universalRawReducedCoordinates ν₁ ν₂ X Y) := by
  unfold universalRawReducedCoordinates
    universalRawGraybillDealWeight universalRawQ
    universalRawMeanVarianceSum universalRawMeanVariance1
    universalRawMeanVariance2
  have hSX := measurable_sampleVarianceN hX
  have hSY := measurable_sampleVarianceN hY
  have hD := measurable_meanDifferenceU hX hY
  fun_prop

@[measurability, fun_prop]
theorem measurable_universalRawReducedWeight
    {δ : ℝ × ℝ → ℝ} (hδ : Measurable δ)
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j)) :
    Measurable (universalRawReducedWeight δ ν₁ ν₂ X Y) := by
  exact hδ.comp (measurable_universalRawReducedCoordinates hX hY)

theorem measurable_universalReducedRuleFactorOfSummary
    {δ : ℝ × ℝ → ℝ} (hδ : Measurable δ)
    (ν₁ ν₂ : ℕ) (θ : ℝ) :
    Measurable (universalReducedRuleFactorOfSummary δ ν₁ ν₂ θ) := by
  unfold universalReducedRuleFactorOfSummary
    universalReducedCoordinatesOfSummary
    universalMeanVarianceOfRSS
  fun_prop

/-! ## Reduced weighted risk -/

/--
The part of squared risk that depends on the weight rule after oracle
regression.
-/
def universalRawReducedSquaredRisk
    (θ : ℝ) (δ : ℝ × ℝ → ℝ) (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (P : Measure Ω) : ℝ :=
  ∫ ω,
    meanDifferenceU ν₁ ν₂ X Y ω ^ 2
      * (universalRawReducedWeight δ ν₁ ν₂ X Y ω - θ) ^ 2 ∂P

/-- Reduced weighted risk of the ordinary Graybill--Deal rule `δ(r,q)=r`. -/
def universalRawGraybillDealReducedSquaredRisk
    (θ : ℝ) (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (P : Measure Ω) : ℝ :=
  ∫ ω,
    meanDifferenceU ν₁ ν₂ X Y ω ^ 2
      * (universalRawGraybillDealWeight ν₁ ν₂ X Y ω - θ) ^ 2 ∂P

/-! ## Normal-model oracle moments -/

namespace TwoNormalSamplesU

variable {ν₁ ν₂ : ℕ}
  {X : Fin (ν₁ + 1) → Ω → ℝ}
  {Y : Fin (ν₂ + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}

/-- The arbitrary-size oracle error is square-integrable. -/
theorem integrable_sq_universalRawOracleError
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    Integrable
      (fun ω =>
        universalRawOracleError ν₁ ν₂ μ v₁ v₂ X Y ω ^ 2) P := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  let θ := universalRawOracleTheta ν₁ ν₂ v₁ v₂
  have hmeanX : MemLp (sampleMeanN ν₁ X) 2 P :=
    h.hasGaussianLaw_sampleMeanX.memLp_two
  have hmeanY : MemLp (sampleMeanN ν₂ Y) 2 P :=
    h.hasGaussianLaw_sampleMeanY.memLp_two
  have hD :
      MemLp (meanDifferenceU ν₁ ν₂ X Y) 2 P := by
    unfold meanDifferenceU
    exact hmeanY.sub hmeanX
  have hT :
      MemLp (universalRawOracleError ν₁ ν₂ μ v₁ v₂ X Y) 2 P := by
    have hraw :=
      (hmeanX.add (hD.const_mul θ)).sub (memLp_const (μ := P) μ)
    apply hraw.ae_eq
    filter_upwards [] with ω
    rfl
  exact (memLp_two_iff_integrable_sq hT.1).1 hT

/-- The arbitrary-size oracle error has mean zero. -/
theorem integral_universalRawOracleError
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    ∫ ω, universalRawOracleError ν₁ ν₂ μ v₁ v₂ X Y ω ∂P = 0 := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hXint : Integrable (sampleMeanN ν₁ X) P :=
    h.hasGaussianLaw_sampleMeanX.integrable
  have hYint : Integrable (sampleMeanN ν₂ Y) P :=
    h.hasGaussianLaw_sampleMeanY.integrable
  have hDint : Integrable (meanDifferenceU ν₁ ν₂ X Y) P := by
    unfold meanDifferenceU
    exact hYint.sub hXint
  unfold universalRawOracleError oracleCenteredErrorU
  change
    (∫ ω,
      (sampleMeanN ν₁ X
        + fun ω =>
          universalRawOracleTheta ν₁ ν₂ v₁ v₂
            * meanDifferenceU ν₁ ν₂ X Y ω) ω
        - (fun _ : Ω => μ) ω ∂P) = 0
  rw [integral_sub
      (hXint.add
        (hDint.const_mul (universalRawOracleTheta ν₁ ν₂ v₁ v₂)))
      (integrable_const μ)]
  change
    (∫ ω,
      sampleMeanN ν₁ X ω
        + universalRawOracleTheta ν₁ ν₂ v₁ v₂
          * meanDifferenceU ν₁ ν₂ X Y ω ∂P)
      - (∫ _ : Ω, μ ∂P) = 0
  rw [integral_add hXint
      (hDint.const_mul (universalRawOracleTheta ν₁ ν₂ v₁ v₂)),
    integral_const_mul, h.integral_meanDifference,
    h.integral_sampleMeanX]
  simp

end TwoNormalSamplesU

/-!
On a finite measure space, an a.e.-strongly measurable real function whose
square is integrable is itself integrable.
-/
private theorem universal_integrable_of_integrable_sq
    {f : Ω → ℝ} {P : Measure Ω} [IsFiniteMeasure P]
    (hf : AEStronglyMeasurable f P)
    (hfsq : Integrable (fun ω => f ω ^ 2) P) :
    Integrable f P := by
  apply (hfsq.add (integrable_const (1 : ℝ))).mono' hf
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  change |f ω| ≤ f ω ^ 2 + 1
  have hsquare : 0 ≤ (|f ω| - 1 / 2 : ℝ) ^ 2 := sq_nonneg _
  have habssq : |f ω| ^ 2 = f ω ^ 2 := sq_abs (f ω)
  norm_num at hsquare
  nlinarith

/-! ## Exact risk transport -/

/--
Exact raw/reduced risk-difference identity under the arbitrary-size normal
model.

The only analytic hypotheses are measurability of the reduced rule and
integrability of the two displayed reduced quadratic risks.  The oracle
cross terms vanish automatically from joint normality and Cochran
independence, for every `ν₁,ν₂` and every positive oracle variance sum.
-/
theorem universalRaw_sqRisk_sub_graybillDeal_eq_reduced
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hsum :
      0 < (v₁ : ℝ) / (ν₁ + 1) + (v₂ : ℝ) / (ν₂ + 1))
    (δ : ℝ × ℝ → ℝ) (hδ : Measurable δ)
    (hquadraticδ :
      Integrable
        (fun ω =>
          meanDifferenceU ν₁ ν₂ X Y ω ^ 2
            * (universalRawReducedWeight δ ν₁ ν₂ X Y ω
              - universalRawOracleTheta ν₁ ν₂ v₁ v₂) ^ 2) P)
    (hquadraticGD :
      Integrable
        (fun ω =>
          meanDifferenceU ν₁ ν₂ X Y ω ^ 2
            * (universalRawGraybillDealWeight ν₁ ν₂ X Y ω
              - universalRawOracleTheta ν₁ ν₂ v₁ v₂) ^ 2) P) :
    sqRisk μ (universalRawReducedEstimator δ ν₁ ν₂ X Y) P
        - sqRisk μ (universalRawGraybillDealEstimator ν₁ ν₂ X Y) P
      =
    universalRawReducedSquaredRisk
        (universalRawOracleTheta ν₁ ν₂ v₁ v₂)
        δ ν₁ ν₂ X Y P
      - universalRawGraybillDealReducedSquaredRisk
        (universalRawOracleTheta ν₁ ν₂ v₁ v₂)
        ν₁ ν₂ X Y P := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  let θ : ℝ := universalRawOracleTheta ν₁ ν₂ v₁ v₂
  let T : Ω → ℝ := universalRawOracleError ν₁ ν₂ μ v₁ v₂ X Y
  let D : Ω → ℝ := meanDifferenceU ν₁ ν₂ X Y
  let w : Ω → ℝ := universalRawReducedWeight δ ν₁ ν₂ X Y
  let r : Ω → ℝ := universalRawGraybillDealWeight ν₁ ν₂ X Y
  let factorδ : Ω → ℝ := fun ω => D ω * (w ω - θ)
  let factorGD : Ω → ℝ := fun ω => D ω * (r ω - θ)

  have hTmeas : Measurable T := by
    dsimp only [T, universalRawOracleError]
    exact measurable_oracleCenteredErrorU hX hY _ _
  have hDmeas : Measurable D := by
    exact measurable_meanDifferenceU hX hY
  have hwmeas : Measurable w := by
    exact measurable_universalRawReducedWeight hδ hX hY
  have hrmeas : Measurable r := by
    have hcoords := measurable_universalRawReducedCoordinates hX hY
    exact measurable_fst.comp hcoords
  have hfactorδmeas : Measurable factorδ := by
    dsimp only [factorδ]
    fun_prop
  have hfactorGDmeas : Measurable factorGD := by
    dsimp only [factorGD]
    fun_prop

  have hfactorδ_sq :
      Integrable (fun ω => factorδ ω ^ 2) P := by
    apply hquadraticδ.congr
    filter_upwards [] with ω
    dsimp only [factorδ, D, w, θ]
    ring
  have hfactorGD_sq :
      Integrable (fun ω => factorGD ω ^ 2) P := by
    apply hquadraticGD.congr
    filter_upwards [] with ω
    dsimp only [factorGD, D, r, θ]
    ring
  have hfactorδ_int : Integrable factorδ P :=
    universal_integrable_of_integrable_sq
      hfactorδmeas.aestronglyMeasurable hfactorδ_sq
  have hfactorGD_int : Integrable factorGD P :=
    universal_integrable_of_integrable_sq
      hfactorGDmeas.aestronglyMeasurable hfactorGD_sq
  have hT_sq : Integrable (fun ω => T ω ^ 2) P := by
    simpa only [T] using h.integrable_sq_universalRawOracleError
  have hT_int : Integrable T P :=
    universal_integrable_of_integrable_sq
      hTmeas.aestronglyMeasurable hT_sq

  have hindSummary :
      IndepFun T (universalSummaryTriple ν₁ ν₂ X Y) P := by
    change
      IndepFun
        (oracleCenteredErrorU ν₁ ν₂ μ
          (oracleVarianceWeightU ν₁ ν₂ v₁ v₂) X Y)
        (fun ω =>
          (meanDifferenceU ν₁ ν₂ X Y ω,
            residualSumSquaresN ν₁ X ω,
            residualSumSquaresN ν₂ Y ω)) P
    exact
      h.indepFun_oracleCenteredError_meanDifference_residualSumSquares hsum
  have hindδ : IndepFun T factorδ P := by
    have hcomp :=
      hindSummary.comp measurable_id
        (measurable_universalReducedRuleFactorOfSummary hδ ν₁ ν₂ θ)
    apply hcomp.congr
    · filter_upwards [] with ω
      rfl
    · filter_upwards [] with ω
      dsimp only [Function.comp_apply, factorδ, D, w]
      exact
        (universalReducedRuleFactorOfSummary_apply
          δ θ X Y ω)
  have hindGD : IndepFun T factorGD P := by
    let firstRule : ℝ × ℝ → ℝ := fun z => z.1
    have hfirst : Measurable firstRule := by
      exact measurable_fst
    have hcomp :=
      hindSummary.comp measurable_id
        (measurable_universalReducedRuleFactorOfSummary
          hfirst ν₁ ν₂ θ)
    apply hcomp.congr
    · filter_upwards [] with ω
      rfl
    · filter_upwards [] with ω
      dsimp only [Function.comp_apply, factorGD, D, r, firstRule]
      rfl

  have hcrossδ :
      Integrable
        (fun ω => T ω * D ω * (w ω - θ)) P := by
    have hmul := hindδ.integrable_mul hT_int hfactorδ_int
    apply hmul.congr
    filter_upwards [] with ω
    dsimp only [factorδ]
    simp only [Pi.mul_apply]
    ring
  have hcrossGD :
      Integrable
        (fun ω => T ω * D ω * (r ω - θ)) P := by
    have hmul := hindGD.integrable_mul hT_int hfactorGD_int
    apply hmul.congr
    filter_upwards [] with ω
    dsimp only [factorGD]
    simp only [Pi.mul_apply]
    ring
  have hTzero : ∫ ω, T ω ∂P = 0 := by
    simpa only [T] using h.integral_universalRawOracleError
  have hcrossδzero :
      ∫ ω, T ω * D ω * (w ω - θ) ∂P = 0 := by
    calc
      (∫ ω, T ω * D ω * (w ω - θ) ∂P)
          = ∫ ω, T ω * factorδ ω ∂P := by
              apply integral_congr_ae
              filter_upwards [] with ω
              dsimp only [factorδ]
              ring
      _ = (∫ ω, T ω ∂P) * ∫ ω, factorδ ω ∂P := by
            exact hindδ.integral_fun_mul_eq_mul_integral
              hTmeas.aestronglyMeasurable
              hfactorδmeas.aestronglyMeasurable
      _ = 0 := by rw [hTzero, zero_mul]
  have hcrossGDzero :
      ∫ ω, T ω * D ω * (r ω - θ) ∂P = 0 := by
    calc
      (∫ ω, T ω * D ω * (r ω - θ) ∂P)
          = ∫ ω, T ω * factorGD ω ∂P := by
              apply integral_congr_ae
              filter_upwards [] with ω
              dsimp only [factorGD]
              ring
      _ = (∫ ω, T ω ∂P) * ∫ ω, factorGD ω ∂P := by
            exact hindGD.integral_fun_mul_eq_mul_integral
              hTmeas.aestronglyMeasurable
              hfactorGDmeas.aestronglyMeasurable
      _ = 0 := by rw [hTzero, zero_mul]

  have hrisk :=
    sqRisk_weight_difference μ θ T D w r P
      hT_sq hcrossδ hcrossGD
      (by simpa only [D, w, θ] using hquadraticδ)
      (by simpa only [D, r, θ] using hquadraticGD)
      hcrossδzero hcrossGDzero
  rw [show
      (fun ω => μ + T ω + D ω * (w ω - θ)) =
        universalRawReducedEstimator δ ν₁ ν₂ X Y by
        funext ω
        symm
        exact universalRawReducedEstimator_eq_oracle_decomposition
          δ μ v₁ v₂ X Y ω,
    show
      (fun ω => μ + T ω + D ω * (r ω - θ)) =
        universalRawGraybillDealEstimator ν₁ ν₂ X Y by
        funext ω
        symm
        exact universalRawGraybillDealEstimator_eq_oracle_decomposition
          μ v₁ v₂ X Y ω] at hrisk
  calc
    sqRisk μ (universalRawReducedEstimator δ ν₁ ν₂ X Y) P
          - sqRisk μ (universalRawGraybillDealEstimator ν₁ ν₂ X Y) P
        =
      ∫ ω,
        D ω ^ 2 * ((w ω - θ) ^ 2 - (r ω - θ) ^ 2) ∂P := hrisk
    _ =
      (∫ ω, D ω ^ 2 * (w ω - θ) ^ 2 ∂P)
        - ∫ ω, D ω ^ 2 * (r ω - θ) ^ 2 ∂P := by
          rw [← integral_sub
            (by simpa only [D, w, θ] using hquadraticδ)
            (by simpa only [D, r, θ] using hquadraticGD)]
          apply integral_congr_ae
          filter_upwards [] with ω
          ring
    _ =
      universalRawReducedSquaredRisk θ δ ν₁ ν₂ X Y P
        - universalRawGraybillDealReducedSquaredRisk
            θ ν₁ ν₂ X Y P := by
          rfl

/--
A strict reduced weighted-risk improvement transports verbatim to a strict
raw common-mean risk improvement.
-/
theorem universalRaw_sqRisk_lt_graybillDeal_of_reduced
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hsum :
      0 < (v₁ : ℝ) / (ν₁ + 1) + (v₂ : ℝ) / (ν₂ + 1))
    (δ : ℝ × ℝ → ℝ) (hδ : Measurable δ)
    (hquadraticδ :
      Integrable
        (fun ω =>
          meanDifferenceU ν₁ ν₂ X Y ω ^ 2
            * (universalRawReducedWeight δ ν₁ ν₂ X Y ω
              - universalRawOracleTheta ν₁ ν₂ v₁ v₂) ^ 2) P)
    (hquadraticGD :
      Integrable
        (fun ω =>
          meanDifferenceU ν₁ ν₂ X Y ω ^ 2
            * (universalRawGraybillDealWeight ν₁ ν₂ X Y ω
              - universalRawOracleTheta ν₁ ν₂ v₁ v₂) ^ 2) P)
    (hreduced :
      universalRawReducedSquaredRisk
          (universalRawOracleTheta ν₁ ν₂ v₁ v₂)
          δ ν₁ ν₂ X Y P
        <
      universalRawGraybillDealReducedSquaredRisk
          (universalRawOracleTheta ν₁ ν₂ v₁ v₂)
          ν₁ ν₂ X Y P) :
    sqRisk μ (universalRawReducedEstimator δ ν₁ ν₂ X Y) P
      <
    sqRisk μ (universalRawGraybillDealEstimator ν₁ ν₂ X Y) P := by
  have hid :=
    universalRaw_sqRisk_sub_graybillDeal_eq_reduced
      h hX hY hsum δ hδ hquadraticδ hquadraticGD
  linarith

/--
A non-strict reduced weighted-risk comparison likewise transports to the
raw common-mean problem.  Together with
`universalRaw_sqRisk_lt_graybillDeal_of_reduced` at one parameter value,
this is the pointwise API needed to transport decision-theoretic
dominance.
-/
theorem universalRaw_sqRisk_le_graybillDeal_of_reduced
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hsum :
      0 < (v₁ : ℝ) / (ν₁ + 1) + (v₂ : ℝ) / (ν₂ + 1))
    (δ : ℝ × ℝ → ℝ) (hδ : Measurable δ)
    (hquadraticδ :
      Integrable
        (fun ω =>
          meanDifferenceU ν₁ ν₂ X Y ω ^ 2
            * (universalRawReducedWeight δ ν₁ ν₂ X Y ω
              - universalRawOracleTheta ν₁ ν₂ v₁ v₂) ^ 2) P)
    (hquadraticGD :
      Integrable
        (fun ω =>
          meanDifferenceU ν₁ ν₂ X Y ω ^ 2
            * (universalRawGraybillDealWeight ν₁ ν₂ X Y ω
              - universalRawOracleTheta ν₁ ν₂ v₁ v₂) ^ 2) P)
    (hreduced :
      universalRawReducedSquaredRisk
          (universalRawOracleTheta ν₁ ν₂ v₁ v₂)
          δ ν₁ ν₂ X Y P
        ≤
      universalRawGraybillDealReducedSquaredRisk
          (universalRawOracleTheta ν₁ ν₂ v₁ v₂)
          ν₁ ν₂ X Y P) :
    sqRisk μ (universalRawReducedEstimator δ ν₁ ν₂ X Y) P
      ≤
    sqRisk μ (universalRawGraybillDealEstimator ν₁ ν₂ X Y) P := by
  have hid :=
    universalRaw_sqRisk_sub_graybillDeal_eq_reduced
      h hX hY hsum δ hδ hquadraticδ hquadraticGD
  linarith

end

end GraybillDeal
