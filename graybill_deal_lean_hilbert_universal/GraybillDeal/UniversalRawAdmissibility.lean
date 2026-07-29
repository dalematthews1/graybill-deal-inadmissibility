import GraybillDeal.UniversalConditionalRawTheorem
import GraybillDeal.UniversalRawComponentLaws

/-!
# An all-parameter raw admissibility wrapper

The lower-level raw transport theorems compare risks at one normal-model
parameter point.  This module packages those comparisons for a fixed
two-sample experiment whose probability law is indexed by
`(μ,v₁,v₂)`.

No probability law is asserted here.  The exact raw reduced-density
family remains an ordinary hypothesis, and is separated from the
Brown--Lehmann--Casella complete-class hypothesis.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A family of raw laws really is the two-independent-normal-sample
model at every parameter point. -/
def IsUniversalTwoNormalSampleFamily
    (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ)
    (P : ℝ → NNReal → NNReal → Measure Ω) : Prop :=
  ∀ μ v₁ v₂,
    TwoNormalSamplesU ν₁ ν₂ X Y (P μ v₁ v₂) μ v₁ v₂

/-- The exact `D²`-weighted reduced law is available at every positive
variance parameter point.

The dominating reference is scaled by

`τ = v₁/(ν₁+1) + v₂/(ν₂+1)`,

the variance of the sample-mean difference. -/
def HasUniversalRawReducedLawFamily
    (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ)
    (P : ℝ → NNReal → NNReal → Measure Ω) : Prop :=
  ∀ (μ : ℝ) (v₁ v₂ : NNReal)
      (hv₁ : 0 < v₁) (hv₂ : 0 < v₂),
      ∃ Q : Measure UniversalReducedObservation,
        HasUniversalReducedDensity
          ((ENNReal.ofReal
              (universalRawDifferenceVariance ν₁ ν₂ v₁ v₂))
            • universalReducedLebesgueMeasure)
          Q
          (universalShape (ν₁ + 1))
          (universalShape (ν₂ + 1))
          (universalRawOracleInteriorTheta
            ν₁ ν₂ v₁ v₂ hv₁ hv₂) ∧
        HasWeightedReducedLaw
          (P μ v₁ v₂)
          (meanDifferenceU ν₁ ν₂ X Y)
          (universalRawReducedObservation ν₁ ν₂ X Y)
          Q

/-- A total reduced rule weakly improves the literal Graybill--Deal
estimator at every positive-variance parameter point and improves it
strictly somewhere. -/
def UniversalRawRiskDominatesGraybillDeal
    (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ)
    (P : ℝ → NNReal → NNReal → Measure Ω)
    (δ : ℝ × ℝ → ℝ) : Prop :=
  (∀ (μ : ℝ) (v₁ v₂ : NNReal),
      0 < v₁ → 0 < v₂ →
        sqRisk μ
            (universalRawReducedEstimator δ ν₁ ν₂ X Y)
            (P μ v₁ v₂)
          ≤
        sqRisk μ
            (universalRawGraybillDealEstimator ν₁ ν₂ X Y)
            (P μ v₁ v₂)) ∧
  ∃ (μ : ℝ) (v₁ v₂ : NNReal),
    0 < v₁ ∧ 0 < v₂ ∧
      sqRisk μ
          (universalRawReducedEstimator δ ν₁ ν₂ X Y)
          (P μ v₁ v₂)
        <
      sqRisk μ
          (universalRawGraybillDealEstimator ν₁ ν₂ X Y)
          (P μ v₁ v₂)

/-- Raw measurable admissibility of the literal Graybill--Deal rule
within the class of estimators induced by measurable total reduced
rules. -/
def IsUniversallyMeasurablyAdmissibleRawGraybillDeal
    (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ)
    (P : ℝ → NNReal → NNReal → Measure Ω) : Prop :=
  ¬ ∃ δ : ℝ × ℝ → ℝ,
    Measurable δ ∧
      UniversalRawRiskDominatesGraybillDeal ν₁ ν₂ X Y P δ

/-- The explicit realizing variances have mean-difference variance one. -/
theorem universalRawDifferenceVariance_realizing
    (ν₁ ν₂ : ℕ) (θ : UniversalInteriorTheta) :
    universalRawDifferenceVariance ν₁ ν₂
        (universalRawVariance1Realizing ν₁ θ)
        (universalRawVariance2Realizing ν₂ θ)
      =
    1 := by
  unfold universalRawDifferenceVariance
  simp only [universalRawVariance1Realizing_coe,
    universalRawVariance2Realizing_coe]
  have hν₁ : (ν₁ : ℝ) + 1 ≠ 0 := by positivity
  have hν₂ : (ν₂ : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Conditional all-parameter raw domination.

Once the complete-class input and the exact reduced law family are
supplied, one measurable rule weakly improves Graybill--Deal at every
positive variance pair and strictly improves it at one pair. -/
theorem
    exists_universalRaw_dominator_of_completeClass_and_lawFamily
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : ℝ → NNReal → NNReal → Measure Ω}
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hfamily : IsUniversalTwoNormalSampleFamily ν₁ ν₂ X Y P)
    (hlaws : HasUniversalRawReducedLawFamily ν₁ ν₂ X Y P)
    (hcomplete :
      UniversalMeasurableFiniteBayesCompleteClassProperty
        (universalReducedObservationReference
          universalReducedLebesgueMeasure
          (universalShape (ν₁ + 1))
          (universalShape (ν₂ + 1)))
        (universalShape (ν₁ + 1))
        (universalShape (ν₂ + 1))) :
    ∃ δ : ℝ × ℝ → ℝ,
      Measurable δ ∧
        UniversalRawRiskDominatesGraybillDeal ν₁ ν₂ X Y P δ := by
  have ha : 0 < universalShape (ν₁ + 1) :=
    universalShape_residualDegrees_pos hν₁
  have hb : 0 < universalShape (ν₂ + 1) :=
    universalShape_residualDegrees_pos hν₂
  obtain ⟨δ, hδ, hall⟩ :=
    exists_total_canonicalUniversalReduced_dominator_all_scalings_of_completeClass
      ha hb hcomplete
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro μ v₁ v₂ hv₁ hv₂
    obtain ⟨Q, hDensity, hWeighted⟩ :=
      hlaws μ v₁ v₂ hv₁ hv₂
    let τ : ℝ :=
      universalRawDifferenceVariance ν₁ ν₂ v₁ v₂
    have hτ : 0 < τ := by
      exact universalRawDifferenceVariance_pos ν₁ ν₂
        (by exact_mod_cast hv₁) (by exact_mod_cast hv₂)
    have hc0 : ENNReal.ofReal τ ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr hτ
    have hctop : ENNReal.ofReal τ ≠ ∞ :=
      ENNReal.ofReal_ne_top
    let θ :=
      universalRawOracleInteriorTheta ν₁ ν₂ v₁ v₂ hv₁ hv₂
    apply universalRaw_sqRisk_le_of_density_domination_lifted
      (hfamily μ v₁ v₂) hX hY hν₁ hν₂ hv₁ hv₂
      ha hb θ
      (universalRawOracleInteriorTheta_coe
        ν₁ ν₂ v₁ v₂ hv₁ hv₂)
      hDensity hWeighted δ hδ
    exact (hall (ENNReal.ofReal τ) hc0 hctop).2.1 θ
  · obtain ⟨θ, hstrict⟩ :=
      (hall 1 one_ne_zero ENNReal.one_ne_top).2.2
    let v₁ := universalRawVariance1Realizing ν₁ θ
    let v₂ := universalRawVariance2Realizing ν₂ θ
    have hv₁ : 0 < v₁ :=
      universalRawVariance1Realizing_pos ν₁ θ
    have hv₂ : 0 < v₂ :=
      universalRawVariance2Realizing_pos ν₂ θ
    obtain ⟨Q, hDensity, hWeighted⟩ :=
      hlaws 0 v₁ v₂ hv₁ hv₂
    have hτ :
        universalRawDifferenceVariance ν₁ ν₂ v₁ v₂ = 1 :=
      universalRawDifferenceVariance_realizing ν₁ ν₂ θ
    have hθ :
        universalRawOracleInteriorTheta
            ν₁ ν₂ v₁ v₂ hv₁ hv₂
          =
        θ := by
      apply Subtype.ext
      exact universalRawOracleTheta_realizing ν₁ ν₂ θ
    have hDensityOne :
        HasUniversalReducedDensity
          ((1 : ℝ≥0∞) • universalReducedLebesgueMeasure)
          Q
          (universalShape (ν₁ + 1))
          (universalShape (ν₂ + 1))
          θ := by
      simpa [hτ, hθ] using hDensity
    refine ⟨0, v₁, v₂, hv₁, hv₂, ?_⟩
    apply universalRaw_sqRisk_lt_of_density_domination_lifted
      (hfamily 0 v₁ v₂) hX hY hν₁ hν₂ hv₁ hv₂
      ha hb θ
      (universalRawOracleTheta_realizing ν₁ ν₂ θ).symm
      hDensityOne hWeighted δ hδ
    exact hstrict

/-- The same theorem stated directly as failure of the raw measurable
admissibility predicate. -/
theorem
    universalRawGraybillDeal_not_admissible_of_completeClass_and_lawFamily
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : ℝ → NNReal → NNReal → Measure Ω}
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hfamily : IsUniversalTwoNormalSampleFamily ν₁ ν₂ X Y P)
    (hlaws : HasUniversalRawReducedLawFamily ν₁ ν₂ X Y P)
    (hcomplete :
      UniversalMeasurableFiniteBayesCompleteClassProperty
        (universalReducedObservationReference
          universalReducedLebesgueMeasure
          (universalShape (ν₁ + 1))
          (universalShape (ν₂ + 1)))
        (universalShape (ν₁ + 1))
        (universalShape (ν₂ + 1))) :
    ¬ IsUniversallyMeasurablyAdmissibleRawGraybillDeal
      ν₁ ν₂ X Y P := by
  intro hadmissible
  exact hadmissible
    (exists_universalRaw_dominator_of_completeClass_and_lawFamily
      hν₁ hν₂ hX hY hfamily hlaws hcomplete)

end

end GraybillDeal
