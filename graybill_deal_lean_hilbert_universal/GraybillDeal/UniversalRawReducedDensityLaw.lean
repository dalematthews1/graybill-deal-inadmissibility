import GraybillDeal.UniversalRawComponentLaws
import GraybillDeal.UniversalReducedChangeOfVariables
import GraybillDeal.UniversalRadialGammaIntegral
import GraybillDeal.UniversalRawCoordinateLift
import GraybillDeal.UniversalReducedRiskRebase
import GraybillDeal.UniversalRawParameters

/-!
# The raw risk-weighted reduced law

This file assembles the probabilistic part of the universal reduction.
For residual degrees of freedom `ν₁,ν₂ > 0`, write

```
τ = v₁/(ν₁+1) + v₂/(ν₂+1),
θ = (v₁/(ν₁+1))/τ,
V = D²/τ,  U₁ = RSS₁/v₁,  U₂ = RSS₂/v₂.
```

The canonical positive coordinates are

```
g₁ = θ U₁/ν₁,   g₂ = (1-θ) U₂/ν₂,   w = V.
```

Thus `gᵢ` is the estimated variance of the corresponding sample mean,
divided by `τ`, and

```
r = g₁/(g₁+g₂),   q = w/(g₁+g₂).
```

The exact risk tilt has already been proved in
`UniversalRawComponentLaws`: weighting by `D²` contributes the scalar `τ`
and raises the `V`-shape from `1/2` to `3/2`.  Here we prove the remaining
raw algebra, define the actual weighted reduced pushforward, and reduce its
density theorem to one purely deterministic pushforward identity for the
tilted product-gamma measure.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Turn `(V,U₁,U₂)` into the canonical positive triple
`(g₁,g₂,w)`.  The use of `νᵢ`, rather than `2*(νᵢ/2)`, keeps all raw
coordinate identities algebraically transparent. -/
def universalRawComponentsToCanonical
    (ν₁ ν₂ : ℕ) (v₁ v₂ : NNReal)
    (z : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let θ := universalRawOracleTheta ν₁ ν₂ v₁ v₂
  (θ * z.2.1 / ν₁,
    ((1 - θ) * z.2.2 / ν₂, z.1))

@[measurability, fun_prop]
theorem measurable_universalRawComponentsToCanonical
    (ν₁ ν₂ : ℕ) (v₁ v₂ : NNReal) :
    Measurable (universalRawComponentsToCanonical ν₁ ν₂ v₁ v₂) := by
  unfold universalRawComponentsToCanonical
  fun_prop

/-- The ambient reduced pair obtained from the canonical triple. -/
def universalCanonicalReducedPair (z : ℝ × ℝ × ℝ) : ℝ × ℝ :=
  let y := universalCanonicalToReducedRadial z
  (y.1, y.2.1)

@[measurability, fun_prop]
theorem measurable_universalCanonicalReducedPair :
    Measurable universalCanonicalReducedPair := by
  unfold universalCanonicalReducedPair
  fun_prop

/-- An everywhere-defined reduced observation obtained from a component
triple.  On the positive support this is the literal `(r,q)` pair. -/
def universalRawComponentsReducedObservation
    (ν₁ ν₂ : ℕ) (v₁ v₂ : NNReal)
    (z : ℝ × ℝ × ℝ) : UniversalReducedObservation :=
  ⟨universalSafeReducedCoordinates
      (universalCanonicalReducedPair
        (universalRawComponentsToCanonical ν₁ ν₂ v₁ v₂ z)),
    universalSafeReducedCoordinates_property _⟩

@[measurability, fun_prop]
theorem measurable_universalRawComponentsReducedObservation
    (ν₁ ν₂ : ℕ) (v₁ v₂ : NNReal) :
    Measurable
      (universalRawComponentsReducedObservation ν₁ ν₂ v₁ v₂) := by
  apply Measurable.subtype_mk
  exact measurable_universalSafeReducedCoordinates.comp
    (measurable_universalCanonicalReducedPair.comp
      (measurable_universalRawComponentsToCanonical ν₁ ν₂ v₁ v₂))

/-- The concrete unnormalised risk-weighted reduced law. -/
def universalRawRiskWeightedReducedMeasure
    (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ)
    (P : Measure Ω) : Measure UniversalReducedObservation :=
  Measure.map (universalRawReducedObservation ν₁ ν₂ X Y)
    (P.withDensity
      (fun ω => ENNReal.ofReal
        (meanDifferenceU ν₁ ν₂ X Y ω ^ 2)))

/-- The `HasWeightedReducedLaw` interface is definitionally discharged by
the concrete pushforward above. -/
theorem hasWeightedReducedLaw_universalRawRiskWeightedReducedMeasure
    (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ)
    (P : Measure Ω) :
    HasWeightedReducedLaw P
      (meanDifferenceU ν₁ ν₂ X Y)
      (universalRawReducedObservation ν₁ ν₂ X Y)
      (universalRawRiskWeightedReducedMeasure ν₁ ν₂ X Y P) := by
  rfl

/-! ## Exact raw-to-component coordinate algebra -/

theorem universalRawMeanVariance1_eq_tau_mul_canonical1
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁)
    {v₁ v₂ : NNReal}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ)
    (ω : Ω) :
    universalRawMeanVariance1 ν₁ X ω
      =
    universalRawDifferenceVariance ν₁ ν₂ v₁ v₂
      * (universalRawComponentsToCanonical ν₁ ν₂ v₁ v₂
          (universalRawIndependentComponents
            ν₁ ν₂ v₁ v₂ X Y ω)).1 := by
  have hτ :
      0 < universalRawDifferenceVariance ν₁ ν₂ v₁ v₂ :=
    universalRawDifferenceVariance_pos ν₁ ν₂ hv₁ hv₂
  have hν₁r : (ν₁ : ℝ) ≠ 0 := by exact_mod_cast hν₁.ne'
  unfold universalRawMeanVariance1 sampleVarianceN
    universalRawComponentsToCanonical
    universalRawIndependentComponents universalRawScaledResidual1
    scaledResidualSumSquaresN universalRawOracleTheta
    oracleVarianceWeightU universalRawDifferenceVariance
  field_simp

theorem universalRawMeanVariance2_eq_tau_mul_canonical2
    {ν₁ ν₂ : ℕ} (hν₂ : 0 < ν₂)
    {v₁ v₂ : NNReal}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ)
    (ω : Ω) :
    universalRawMeanVariance2 ν₂ Y ω
      =
    universalRawDifferenceVariance ν₁ ν₂ v₁ v₂
      * (universalRawComponentsToCanonical ν₁ ν₂ v₁ v₂
          (universalRawIndependentComponents
            ν₁ ν₂ v₁ v₂ X Y ω)).2.1 := by
  have hτ :
      0 < universalRawDifferenceVariance ν₁ ν₂ v₁ v₂ :=
    universalRawDifferenceVariance_pos ν₁ ν₂ hv₁ hv₂
  have hν₂r : (ν₂ : ℝ) ≠ 0 := by exact_mod_cast hν₂.ne'
  unfold universalRawMeanVariance2 sampleVarianceN
    universalRawComponentsToCanonical
    universalRawIndependentComponents universalRawScaledResidual2
    scaledResidualSumSquaresN universalRawOracleTheta
    oracleVarianceWeightU universalRawDifferenceVariance
  field_simp
  ring

theorem meanDifference_sq_eq_tau_mul_canonical3
    {ν₁ ν₂ : ℕ} {v₁ v₂ : NNReal}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ)
    (ω : Ω) :
    meanDifferenceU ν₁ ν₂ X Y ω ^ 2
      =
    universalRawDifferenceVariance ν₁ ν₂ v₁ v₂
      * (universalRawComponentsToCanonical ν₁ ν₂ v₁ v₂
          (universalRawIndependentComponents
            ν₁ ν₂ v₁ v₂ X Y ω)).2.2 := by
  exact meanDifference_sq_eq_variance_mul_standardized X Y
    (universalRawDifferenceVariance_pos ν₁ ν₂ hv₁ hv₂) ω

/-- Pointwise equality of the literal raw pair and the canonical reduced
pair.  It is stated under positivity of both estimated mean variances,
which is the almost-sure event supplied by `UniversalRawCoordinateLift`. -/
theorem universalCanonicalReducedPair_components_eq_raw
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    {v₁ v₂ : NNReal}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ)
    (ω : Ω)
    (hA₁ : 0 < universalRawMeanVariance1 ν₁ X ω)
    (hA₂ : 0 < universalRawMeanVariance2 ν₂ Y ω) :
    universalCanonicalReducedPair
        (universalRawComponentsToCanonical ν₁ ν₂ v₁ v₂
          (universalRawIndependentComponents
            ν₁ ν₂ v₁ v₂ X Y ω))
      =
    universalRawReducedCoordinates ν₁ ν₂ X Y ω := by
  let τ := universalRawDifferenceVariance ν₁ ν₂ v₁ v₂
  let z :=
    universalRawComponentsToCanonical ν₁ ν₂ v₁ v₂
      (universalRawIndependentComponents ν₁ ν₂ v₁ v₂ X Y ω)
  have hτ : 0 < τ :=
    universalRawDifferenceVariance_pos ν₁ ν₂ hv₁ hv₂
  have h₁ :
      universalRawMeanVariance1 ν₁ X ω = τ * z.1 := by
    exact universalRawMeanVariance1_eq_tau_mul_canonical1
      hν₁ hv₁ hv₂ X Y ω
  have h₂ :
      universalRawMeanVariance2 ν₂ Y ω = τ * z.2.1 := by
    exact universalRawMeanVariance2_eq_tau_mul_canonical2
      hν₂ hv₁ hv₂ X Y ω
  have h₃ :
      meanDifferenceU ν₁ ν₂ X Y ω ^ 2 = τ * z.2.2 := by
    exact meanDifference_sq_eq_tau_mul_canonical3
      hv₁ hv₂ X Y ω
  have hsum :
      universalRawMeanVarianceSum ν₁ ν₂ X Y ω
        = τ * (z.1 + z.2.1) := by
    unfold universalRawMeanVarianceSum
    rw [h₁, h₂]
    ring
  have hzsum : z.1 + z.2.1 ≠ 0 := by
    intro hz
    have : universalRawMeanVarianceSum ν₁ ν₂ X Y ω = 0 := by
      rw [hsum, hz, mul_zero]
    unfold universalRawMeanVarianceSum at this
    linarith
  unfold universalCanonicalReducedPair
    universalCanonicalToReducedRadial
    universalRawReducedCoordinates universalRawGraybillDealWeight
    universalRawQ
  dsimp only
  rw [h₁, h₃, hsum]
  change
    (z.1 / (z.1 + z.2.1), z.2.2 / (z.1 + z.2.1))
      =
    (τ * z.1 / (τ * (z.1 + z.2.1)),
      τ * z.2.2 / (τ * (z.1 + z.2.1)))
  apply Prod.ext
  · dsimp only
    field_simp [hτ.ne', hzsum]
  · dsimp only
    field_simp [hτ.ne', hzsum]

namespace TwoNormalSamplesU

variable {ν₁ ν₂ : ℕ}
  {X : Fin (ν₁ + 1) → Ω → ℝ}
  {Y : Fin (ν₂ + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}

/-- The safe raw observation is almost surely the deterministic image of
the independent component triple. -/
theorem ae_universalRawReducedObservation_eq_components
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    universalRawReducedObservation ν₁ ν₂ X Y
      =ᵐ[P]
    (universalRawComponentsReducedObservation ν₁ ν₂ v₁ v₂)
      ∘ universalRawIndependentComponents ν₁ ν₂ v₁ v₂ X Y := by
  filter_upwards
    [h.ae_pos_universalRawMeanVariance1 hν₁ hv₁,
      h.ae_pos_universalRawMeanVariance2 hν₂ hv₂,
      h.ae_mem_universalRawReducedCoordinates
        hν₁ hν₂ hv₁ hv₂] with ω hA₁ hA₂ hmem
  apply Subtype.ext
  simp only [Function.comp_apply, universalRawReducedObservation,
    universalRawComponentsReducedObservation]
  rw [universalSafeReducedCoordinates,
    if_pos hmem]
  have hpair :=
    universalCanonicalReducedPair_components_eq_raw
      hν₁ hν₂ hv₁ hv₂ X Y ω hA₁ hA₂
  rw [hpair, universalSafeReducedCoordinates, if_pos hmem]

/-- The full raw weighted pushforward is exactly `τ` times the deterministic
reduced image of the risk-tilted independent component measure. -/
theorem universalRawRiskWeightedReducedMeasure_eq_componentImage
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    universalRawRiskWeightedReducedMeasure ν₁ ν₂ X Y P
      =
    ENNReal.ofReal
        (universalRawDifferenceVariance ν₁ ν₂ v₁ v₂)
      • Measure.map
          (universalRawComponentsReducedObservation ν₁ ν₂ v₁ v₂)
          (universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂) := by
  let W :=
    P.withDensity
      (fun ω =>
        ENNReal.ofReal (meanDifferenceU ν₁ ν₂ X Y ω ^ 2))
  let C :=
    universalRawIndependentComponents ν₁ ν₂ v₁ v₂ X Y
  let F :=
    universalRawComponentsReducedObservation ν₁ ν₂ v₁ v₂
  have hWC :
      Measure.map C W
        =
      ENNReal.ofReal
          (universalRawDifferenceVariance ν₁ ν₂ v₁ v₂)
        • universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂ := by
    exact
      h.map_universalRawIndependentComponents_withDensity_sq_meanDifference
        hν₁ hν₂ hv₁ hv₂
  have hC : Measurable C :=
    measurable_universalRawIndependentComponents hX hY
  have hF : Measurable F :=
    measurable_universalRawComponentsReducedObservation ν₁ ν₂ v₁ v₂
  have hZW :
      universalRawReducedObservation ν₁ ν₂ X Y =ᵐ[W] F ∘ C := by
    exact
      (withDensity_absolutelyContinuous P _).ae_eq
        (h.ae_universalRawReducedObservation_eq_components
          hν₁ hν₂ hv₁ hv₂)
  unfold universalRawRiskWeightedReducedMeasure
  change Measure.map
      (universalRawReducedObservation ν₁ ν₂ X Y) W = _
  rw [Measure.map_congr hZW]
  rw [← Measure.map_map hF hC]
  rw [hWC, Measure.map_smul]

end TwoNormalSamplesU

/-! ## The exact remaining deterministic density statement

The theorem below is the final assembly point.  Its hypothesis is now a
statement solely about an explicit product of three Gamma measures and an
explicit deterministic map.  `UniversalReducedChangeOfVariables` and
`UniversalRadialGammaIntegral` provide its Jacobian and radial integral.
-/

def UniversalRiskTiltedComponentReducedDensityIdentity
    (ν₁ ν₂ : ℕ) (v₁ v₂ : NNReal)
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) : Prop :=
  Measure.map
      (universalRawComponentsReducedObservation ν₁ ν₂ v₁ v₂)
      (universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂)
    =
  universalReducedLebesgueMeasure.withDensity
    (fun x =>
      ENNReal.ofReal
        (universalFullReducedDensity
          ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2)
          (universalRawOracleInteriorTheta
            ν₁ ν₂ v₁ v₂ hv₁ hv₂) x))

theorem hasUniversalReducedDensity_universalRawRiskWeightedReducedMeasure
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (hdet :
      UniversalRiskTiltedComponentReducedDensityIdentity
        ν₁ ν₂ v₁ v₂ hv₁ hv₂) :
    HasUniversalReducedDensity
      (ENNReal.ofReal
          (universalRawDifferenceVariance ν₁ ν₂ v₁ v₂)
        • universalReducedLebesgueMeasure)
      (universalRawRiskWeightedReducedMeasure ν₁ ν₂ X Y P)
      ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2)
      (universalRawOracleInteriorTheta
        ν₁ ν₂ v₁ v₂ hv₁ hv₂) := by
  have hv₁r : 0 < (v₁ : ℝ) := by exact_mod_cast hv₁
  have hv₂r : 0 < (v₂ : ℝ) := by exact_mod_cast hv₂
  rw [h.universalRawRiskWeightedReducedMeasure_eq_componentImage
    hX hY hν₁ hν₂ hv₁r hv₂r]
  rw [hdet]
  unfold HasUniversalReducedDensity
  rw [withDensity_smul_measure]

end

end GraybillDeal
