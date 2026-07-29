import GraybillDeal.UnequalDampedCanonical
import GraybillDeal.UnequalDampedRawEstimator

/-!
# Raw/canonical coordinate identities for samples of sizes 13 and 17

This file identifies the direct canonical coordinates with the literal
Graybill--Deal quantities.  The key normalization is

`A₁+A₂ = λ L Dnorm / 28`,

where `A₁=S₁²/13`, `A₂=S₂²/17`,
`λ=v₁/13+v₂/17`, `P=U₁/(U₁+U₂)`, and `L=U₁+U₂`.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem unequalDamped_denom_ratio_sum
    {τ₁ τ₂ u₁ u₂ : ℝ}
    (hτ : τ₁ + τ₂ ≠ 0) (hu : u₁ + u₂ ≠ 0) :
    (τ₁ + τ₂) * (u₁ + u₂)
          * unequalDampedCanonicalDenom13_17
              (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂))
        / 28
      =
    τ₁ * u₁ / 12 + τ₂ * u₂ / 16 := by
  unfold unequalDampedCanonicalDenom13_17
  field_simp [hτ, hu]
  ring

private theorem unequalDamped_R_ratio_sum
    {τ₁ τ₂ u₁ u₂ : ℝ}
    (hτ : τ₁ + τ₂ ≠ 0) (hu : u₁ + u₂ ≠ 0)
    (hA : τ₁ * u₁ / 12 + τ₂ * u₂ / 16 ≠ 0) :
    unequalDampedCanonicalR13_17
        (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂))
      =
    (τ₁ * u₁ / 12)
      / (τ₁ * u₁ / 12 + τ₂ * u₂ / 16) := by
  have hden :
      unequalDampedCanonicalDenom13_17
          (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂)) ≠ 0 := by
    intro hzero
    have hid := unequalDamped_denom_ratio_sum hτ hu
    rw [hzero] at hid
    simp only [mul_zero, zero_div] at hid
    exact hA hid.symm
  unfold unequalDampedCanonicalR13_17
  apply (div_eq_div_iff hden hA).2
  rw [← unequalDamped_denom_ratio_sum hτ hu]
  field_simp [hτ, hu] <;> ring

private theorem unequalDamped_Q_ratio_sum
    {τ₁ τ₂ u₁ u₂ d : ℝ}
    (hτ : τ₁ + τ₂ ≠ 0) (hu : u₁ + u₂ ≠ 0)
    (hA : τ₁ * u₁ / 12 + τ₂ * u₂ / 16 ≠ 0) :
    unequalDampedCanonicalQ13_17
        (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂))
        (u₁ + u₂) (d ^ 2 / (τ₁ + τ₂))
      =
    d ^ 2 / (τ₁ * u₁ / 12 + τ₂ * u₂ / 16) := by
  have hden :
      unequalDampedCanonicalDenom13_17
          (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂)) ≠ 0 := by
    intro hzero
    have hid := unequalDamped_denom_ratio_sum hτ hu
    rw [hzero] at hid
    simp only [mul_zero, zero_div] at hid
    exact hA hid.symm
  unfold unequalDampedCanonicalQ13_17
  have hUden :
      (u₁ + u₂)
          * unequalDampedCanonicalDenom13_17
              (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂)) ≠ 0 :=
    mul_ne_zero hu hden
  apply (div_eq_div_iff hUden hA).2
  rw [← unequalDamped_denom_ratio_sum hτ hu]
  field_simp [hτ, hu] <;> ring

/-- The raw oracle weight is the ratio of the two mean variances. -/
theorem oracleVarianceWeightU_twelve_sixteen
    (v₁ v₂ : NNReal) :
    oracleVarianceWeightU 12 16 v₁ v₂
      =
    ((v₁ : ℝ) / 13) / normalMeanVarianceSum13_17 v₁ v₂ := by
  norm_num [oracleVarianceWeightU, normalMeanVarianceSum13_17]

/-- The first probabilistic residual coordinate is `12 S₁²/v₁`. -/
theorem normalRawU1_13_17_eq_sampleVariance
    (v₁ : NNReal) (X : Fin 13 → Ω → ℝ) (ω : Ω) :
    normalRawU1_13_17 v₁ X ω
      =
    12 * sampleVarianceN 12 X ω / (v₁ : ℝ) := by
  unfold normalRawU1_13_17 scaledResidualSumSquaresN
  rw [← residualDF_mul_sampleVarianceN (by norm_num) X ω]
  norm_num

/-- The second probabilistic residual coordinate is `16 S₂²/v₂`. -/
theorem normalRawU2_13_17_eq_sampleVariance
    (v₂ : NNReal) (Y : Fin 17 → Ω → ℝ) (ω : Ω) :
    normalRawU2_13_17 v₂ Y ω
      =
    16 * sampleVarianceN 16 Y ω / (v₂ : ℝ) := by
  unfold normalRawU2_13_17 scaledResidualSumSquaresN
  rw [← residualDF_mul_sampleVarianceN (by norm_num) Y ω]
  norm_num

/-- The two definitions of the standardized squared difference coincide. -/
theorem normalRawV13_17_eq_unequalStandardizedDifference
    (v₁ v₂ : NNReal)
    (X : Fin 13 → Ω → ℝ) (Y : Fin 17 → Ω → ℝ) (ω : Ω) :
    normalRawV13_17 v₁ v₂ X Y ω
      =
    unequalStandardizedDifference13_17
      (normalMeanVarianceSum13_17 v₁ v₂)
      (meanDifferenceU 12 16 X Y ω) := by
  norm_num [normalRawV13_17, generalStandardizedDifference,
    unequalStandardizedDifference13_17]

/--
The fixed canonical denominator reconstructs the sum of the two estimated
sample-mean variances.
-/
theorem rawMeanVarianceSum13_17_eq_canonical
    {v₁ v₂ : NNReal}
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ} {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : normalRawL13_17 v₁ v₂ X Y ω ≠ 0) :
    rawMeanVarianceSum13_17 X Y ω
      =
    normalMeanVarianceSum13_17 v₁ v₂
      * normalRawL13_17 v₁ v₂ X Y ω
      * unequalDampedCanonicalDenom13_17
          (oracleVarianceWeightU 12 16 v₁ v₂)
          (normalRawP13_17 v₁ v₂ X Y ω)
      / 28 := by
  let τ₁ : ℝ := (v₁ : ℝ) / 13
  let τ₂ : ℝ := (v₂ : ℝ) / 17
  let u₁ : ℝ := normalRawU1_13_17 v₁ X ω
  let u₂ : ℝ := normalRawU2_13_17 v₂ Y ω
  have hτ : τ₁ + τ₂ ≠ 0 := by
    apply ne_of_gt
    dsimp only [τ₁, τ₂]
    positivity
  have hu : u₁ + u₂ ≠ 0 := by
    simpa [u₁, u₂, normalRawL13_17] using hL
  have hid := unequalDamped_denom_ratio_sum hτ hu
  have hright :
      τ₁ * u₁ / 12 + τ₂ * u₂ / 16
        = rawMeanVarianceSum13_17 X Y ω := by
    dsimp only [τ₁, τ₂, u₁, u₂]
    rw [normalRawU1_13_17_eq_sampleVariance,
      normalRawU2_13_17_eq_sampleVariance]
    unfold rawMeanVarianceSum13_17 rawMeanVariance1_13
      rawMeanVariance2_17
    field_simp [hv₁.ne', hv₂.ne']
  rw [hright] at hid
  symm
  simpa [τ₁, τ₂, u₁, u₂, normalMeanVarianceSum13_17,
    normalRawP13_17, normalRawL13_17,
    oracleVarianceWeightU_twelve_sixteen] using hid

/-- The canonical base weight is the literal unequal Graybill--Deal weight. -/
theorem unequalDampedCanonicalR_eq_rawGraybillDealWeight13_17
    {v₁ v₂ : NNReal}
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ} {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : normalRawL13_17 v₁ v₂ X Y ω ≠ 0)
    (hA : rawMeanVarianceSum13_17 X Y ω ≠ 0) :
    unequalDampedCanonicalR13_17
        (oracleVarianceWeightU 12 16 v₁ v₂)
        (normalRawP13_17 v₁ v₂ X Y ω)
      =
    rawGraybillDealWeight13_17 X Y ω := by
  let τ₁ : ℝ := (v₁ : ℝ) / 13
  let τ₂ : ℝ := (v₂ : ℝ) / 17
  let u₁ : ℝ := normalRawU1_13_17 v₁ X ω
  let u₂ : ℝ := normalRawU2_13_17 v₂ Y ω
  have hτ : τ₁ + τ₂ ≠ 0 := by
    apply ne_of_gt
    dsimp only [τ₁, τ₂]
    positivity
  have hu : u₁ + u₂ ≠ 0 := by
    simpa [u₁, u₂, normalRawL13_17] using hL
  have hcomponent :
      τ₁ * u₁ / 12 + τ₂ * u₂ / 16
        = rawMeanVarianceSum13_17 X Y ω := by
    dsimp only [τ₁, τ₂, u₁, u₂]
    rw [normalRawU1_13_17_eq_sampleVariance,
      normalRawU2_13_17_eq_sampleVariance]
    unfold rawMeanVarianceSum13_17 rawMeanVariance1_13
      rawMeanVariance2_17
    field_simp [hv₁.ne', hv₂.ne']
  have hcomponent_ne :
      τ₁ * u₁ / 12 + τ₂ * u₂ / 16 ≠ 0 := by
    rwa [hcomponent]
  have hr := unequalDamped_R_ratio_sum hτ hu hcomponent_ne
  rw [hcomponent] at hr
  have hfirst :
      τ₁ * u₁ / 12 = rawMeanVariance1_13 X ω := by
    dsimp only [τ₁, u₁]
    rw [normalRawU1_13_17_eq_sampleVariance]
    unfold rawMeanVariance1_13
    field_simp [hv₁.ne']
  rw [hfirst] at hr
  simpa [τ₁, τ₂, u₁, u₂, normalRawP13_17,
    oracleVarianceWeightU_twelve_sixteen,
    normalMeanVarianceSum13_17,
    rawGraybillDealWeight13_17] using hr

/-- The canonical `Q` is exactly `D²/(S₁²/13+S₂²/17)`. -/
theorem unequalDampedCanonicalQ_eq_rawQuadraticStatistic13_17
    {v₁ v₂ : NNReal}
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ} {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : normalRawL13_17 v₁ v₂ X Y ω ≠ 0)
    (hA : rawMeanVarianceSum13_17 X Y ω ≠ 0) :
    unequalDampedCanonicalQ13_17
        (oracleVarianceWeightU 12 16 v₁ v₂)
        (normalRawP13_17 v₁ v₂ X Y ω)
        (normalRawL13_17 v₁ v₂ X Y ω)
        (normalRawV13_17 v₁ v₂ X Y ω)
      =
    rawQuadraticStatistic13_17 X Y ω := by
  let τ₁ : ℝ := (v₁ : ℝ) / 13
  let τ₂ : ℝ := (v₂ : ℝ) / 17
  let u₁ : ℝ := normalRawU1_13_17 v₁ X ω
  let u₂ : ℝ := normalRawU2_13_17 v₂ Y ω
  let d : ℝ := meanDifferenceU 12 16 X Y ω
  have hτ : τ₁ + τ₂ ≠ 0 := by
    apply ne_of_gt
    dsimp only [τ₁, τ₂]
    positivity
  have hu : u₁ + u₂ ≠ 0 := by
    simpa [u₁, u₂, normalRawL13_17] using hL
  have hcomponent :
      τ₁ * u₁ / 12 + τ₂ * u₂ / 16
        = rawMeanVarianceSum13_17 X Y ω := by
    dsimp only [τ₁, τ₂, u₁, u₂]
    rw [normalRawU1_13_17_eq_sampleVariance,
      normalRawU2_13_17_eq_sampleVariance]
    unfold rawMeanVarianceSum13_17 rawMeanVariance1_13
      rawMeanVariance2_17
    field_simp [hv₁.ne', hv₂.ne']
  have hcomponent_ne :
      τ₁ * u₁ / 12 + τ₂ * u₂ / 16 ≠ 0 := by
    rwa [hcomponent]
  have hq := unequalDamped_Q_ratio_sum
    (d := d) hτ hu hcomponent_ne
  rw [hcomponent] at hq
  simpa [τ₁, τ₂, u₁, u₂, d, normalRawP13_17,
    normalRawL13_17, normalRawV13_17,
    generalStandardizedDifference,
    normalMeanVarianceSum13_17,
    oracleVarianceWeightU_twelve_sixteen,
    rawQuadraticStatistic13_17] using hq

/-- The canonical perturbation direction is the literal raw direction. -/
theorem unequalDampedCanonicalH_eq_rawDirection13_17
    {v₁ v₂ : NNReal}
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ} {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : normalRawL13_17 v₁ v₂ X Y ω ≠ 0)
    (hA : rawMeanVarianceSum13_17 X Y ω ≠ 0) :
    unequalDampedCanonicalH13_17
        (oracleVarianceWeightU 12 16 v₁ v₂)
        (normalRawP13_17 v₁ v₂ X Y ω)
        (normalRawL13_17 v₁ v₂ X Y ω)
        (normalRawV13_17 v₁ v₂ X Y ω)
      =
    unequalDampedPhi13_17 (rawGraybillDealWeight13_17 X Y ω)
      * (unequalDampedC13_17
        - rawQuadraticStatistic13_17 X Y ω) := by
  unfold unequalDampedCanonicalH13_17
  rw [unequalDampedCanonicalR_eq_rawGraybillDealWeight13_17
      hv₁ hv₂ hL hA,
    unequalDampedCanonicalQ_eq_rawQuadraticStatistic13_17
      hv₁ hv₂ hL hA]

/-- The un-clipped canonical weight is the literal raw perturbation. -/
theorem unequalDampedCanonicalWeight_eq_rawPerturbedWeight13_17
    {ε : ℝ} {v₁ v₂ : NNReal}
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ} {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : normalRawL13_17 v₁ v₂ X Y ω ≠ 0)
    (hA : rawMeanVarianceSum13_17 X Y ω ≠ 0) :
    unequalDampedCanonicalWeight13_17 ε
        (oracleVarianceWeightU 12 16 v₁ v₂)
        (normalRawP13_17 v₁ v₂ X Y ω)
        (normalRawL13_17 v₁ v₂ X Y ω)
        (normalRawV13_17 v₁ v₂ X Y ω)
      =
    rawPerturbedWeight13_17 ε X Y ω := by
  unfold unequalDampedCanonicalWeight13_17 perturbation
    rawPerturbedWeight13_17
  rw [unequalDampedCanonicalR_eq_rawGraybillDealWeight13_17
      hv₁ hv₂ hL hA,
    unequalDampedCanonicalH_eq_rawDirection13_17
      hv₁ hv₂ hL hA]
  ring

/-- The clipped canonical weight is the literal clipped perturbation. -/
theorem unequalDampedCanonicalClippedWeight_eq_rawClippedPerturbedWeight13_17
    {ε : ℝ} {v₁ v₂ : NNReal}
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ} {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : normalRawL13_17 v₁ v₂ X Y ω ≠ 0)
    (hA : rawMeanVarianceSum13_17 X Y ω ≠ 0) :
    unequalDampedCanonicalClippedWeight13_17 ε
        (oracleVarianceWeightU 12 16 v₁ v₂)
        (normalRawP13_17 v₁ v₂ X Y ω)
        (normalRawL13_17 v₁ v₂ X Y ω)
        (normalRawV13_17 v₁ v₂ X Y ω)
      =
    rawClippedPerturbedWeight13_17 ε X Y ω := by
  unfold unequalDampedCanonicalClippedWeight13_17
    rawClippedPerturbedWeight13_17
  rw [unequalDampedCanonicalWeight_eq_rawPerturbedWeight13_17
    hv₁ hv₂ hL hA]

/-- The full canonical baseline is the literal Graybill--Deal estimator. -/
theorem unequalDampedCanonicalBaseEstimator_eq_rawGraybillDealEstimator13_17
    {μ : ℝ} {v₁ v₂ : NNReal}
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ} {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : normalRawL13_17 v₁ v₂ X Y ω ≠ 0)
    (hA : rawMeanVarianceSum13_17 X Y ω ≠ 0) :
    μ
        + oracleCenteredError13_17 μ v₁ v₂ X Y ω
        + meanDifferenceU 12 16 X Y ω
          * (unequalDampedCanonicalR13_17
                (oracleVarianceWeightU 12 16 v₁ v₂)
                (normalRawP13_17 v₁ v₂ X Y ω)
              - oracleVarianceWeightU 12 16 v₁ v₂)
      =
    rawGraybillDealEstimator13_17 X Y ω := by
  rw [unequalDampedCanonicalR_eq_rawGraybillDealWeight13_17
      hv₁ hv₂ hL hA]
  unfold oracleCenteredError13_17 oracleCenteredErrorU
    rawGraybillDealEstimator13_17
  ring

/-- The full canonical competitor is the literal raw clipped competitor. -/
theorem unequalDampedCanonicalClippedEstimator_eq_rawClippedPerturbedEstimator13_17
    {ε μ : ℝ} {v₁ v₂ : NNReal}
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ} {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : normalRawL13_17 v₁ v₂ X Y ω ≠ 0)
    (hA : rawMeanVarianceSum13_17 X Y ω ≠ 0) :
    μ
        + oracleCenteredError13_17 μ v₁ v₂ X Y ω
        + meanDifferenceU 12 16 X Y ω
          * (unequalDampedCanonicalClippedWeight13_17 ε
                (oracleVarianceWeightU 12 16 v₁ v₂)
                (normalRawP13_17 v₁ v₂ X Y ω)
                (normalRawL13_17 v₁ v₂ X Y ω)
                (normalRawV13_17 v₁ v₂ X Y ω)
              - oracleVarianceWeightU 12 16 v₁ v₂)
      =
    rawClippedPerturbedEstimator13_17 ε X Y ω := by
  rw [unequalDampedCanonicalClippedWeight_eq_rawClippedPerturbedWeight13_17
      hv₁ hv₂ hL hA]
  unfold oracleCenteredError13_17 oracleCenteredErrorU
    rawClippedPerturbedEstimator13_17
  ring

namespace TwoNormalSamplesU

variable
  {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}

theorem ae_eq_unequalDampedCanonicalR_rawGraybillDealWeight13_17
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    (fun ω =>
      unequalDampedCanonicalR13_17
        (oracleVarianceWeightU 12 16 v₁ v₂)
        (normalRawP13_17 v₁ v₂ X Y ω))
      =ᵐ[P]
    rawGraybillDealWeight13_17 X Y := by
  filter_upwards
    [h.ae_ne_normalRawL13_17 hv₁ hv₂,
      h.ae_ne_sampleMeanVarianceSum13_17 hv₁ hv₂] with ω hL hA
  exact unequalDampedCanonicalR_eq_rawGraybillDealWeight13_17
    hv₁ hv₂ hL hA

theorem ae_eq_unequalDampedCanonicalQ_rawQuadraticStatistic13_17
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    (fun ω =>
      unequalDampedCanonicalQ13_17
        (oracleVarianceWeightU 12 16 v₁ v₂)
        (normalRawP13_17 v₁ v₂ X Y ω)
        (normalRawL13_17 v₁ v₂ X Y ω)
        (normalRawV13_17 v₁ v₂ X Y ω))
      =ᵐ[P]
    rawQuadraticStatistic13_17 X Y := by
  filter_upwards
    [h.ae_ne_normalRawL13_17 hv₁ hv₂,
      h.ae_ne_sampleMeanVarianceSum13_17 hv₁ hv₂] with ω hL hA
  exact unequalDampedCanonicalQ_eq_rawQuadraticStatistic13_17
    hv₁ hv₂ hL hA

theorem ae_eq_unequalDampedCanonicalClippedWeight_raw13_17
    (ε : ℝ)
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    (fun ω =>
      unequalDampedCanonicalClippedWeight13_17 ε
        (oracleVarianceWeightU 12 16 v₁ v₂)
        (normalRawP13_17 v₁ v₂ X Y ω)
        (normalRawL13_17 v₁ v₂ X Y ω)
        (normalRawV13_17 v₁ v₂ X Y ω))
      =ᵐ[P]
    rawClippedPerturbedWeight13_17 ε X Y := by
  filter_upwards
    [h.ae_ne_normalRawL13_17 hv₁ hv₂,
      h.ae_ne_sampleMeanVarianceSum13_17 hv₁ hv₂] with ω hL hA
  exact
    unequalDampedCanonicalClippedWeight_eq_rawClippedPerturbedWeight13_17
      hv₁ hv₂ hL hA

theorem ae_eq_unequalDampedCanonicalBaseEstimator_raw13_17
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    (fun ω =>
      μ
        + oracleCenteredError13_17 μ v₁ v₂ X Y ω
        + meanDifferenceU 12 16 X Y ω
          * (unequalDampedCanonicalR13_17
                (oracleVarianceWeightU 12 16 v₁ v₂)
                (normalRawP13_17 v₁ v₂ X Y ω)
              - oracleVarianceWeightU 12 16 v₁ v₂))
      =ᵐ[P]
    rawGraybillDealEstimator13_17 X Y := by
  filter_upwards
    [h.ae_ne_normalRawL13_17 hv₁ hv₂,
      h.ae_ne_sampleMeanVarianceSum13_17 hv₁ hv₂] with ω hL hA
  exact
    unequalDampedCanonicalBaseEstimator_eq_rawGraybillDealEstimator13_17
      hv₁ hv₂ hL hA

theorem ae_eq_unequalDampedCanonicalClippedEstimator_raw13_17
    (ε : ℝ)
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    (fun ω =>
      μ
        + oracleCenteredError13_17 μ v₁ v₂ X Y ω
        + meanDifferenceU 12 16 X Y ω
          * (unequalDampedCanonicalClippedWeight13_17 ε
                (oracleVarianceWeightU 12 16 v₁ v₂)
                (normalRawP13_17 v₁ v₂ X Y ω)
                (normalRawL13_17 v₁ v₂ X Y ω)
                (normalRawV13_17 v₁ v₂ X Y ω)
              - oracleVarianceWeightU 12 16 v₁ v₂))
      =ᵐ[P]
    rawClippedPerturbedEstimator13_17 ε X Y := by
  filter_upwards
    [h.ae_ne_normalRawL13_17 hv₁ hv₂,
      h.ae_ne_sampleMeanVarianceSum13_17 hv₁ hv₂] with ω hL hA
  exact
    unequalDampedCanonicalClippedEstimator_eq_rawClippedPerturbedEstimator13_17
      hv₁ hv₂ hL hA

end TwoNormalSamplesU

end

end GraybillDeal
