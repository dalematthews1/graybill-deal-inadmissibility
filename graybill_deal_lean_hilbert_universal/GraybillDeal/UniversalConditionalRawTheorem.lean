import GraybillDeal.UniversalRiskScaling
import GraybillDeal.UniversalRawDecisionBridge
import GraybillDeal.UniversalRawCoordinateLift

/-!
# Conditional universal raw Graybill--Deal theorem

This module assembles the checked universal reduced theorem with the raw
normal-sample risk bridge.  It introduces no complete-class or
change-of-variables axiom.  The two facts that are not yet available in
the project remain ordinary theorem hypotheses:

* `UniversalMeasurableFiniteBayesCompleteClassProperty`;
* the concrete `HasUniversalReducedDensity` and `HasWeightedReducedLaw`
  identities for the raw experiment.

There are three useful conclusions.

1. A single total measurable rule dominates the reduced Graybill--Deal
   rule after *every* finite positive scaling of the canonical reference
   measure.
2. Every reduced parameter `θ ∈ (0,1)` is exactly the oracle parameter
   of positive raw variances at any fixed pair of sample sizes.
3. Once the two raw law identities are supplied, reduced weak or strict
   dominance transports directly to literal raw squared-risk dominance.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## One total dominator for every positive finite scaling -/

/-- The complete-class conclusion supplies one ambient measurable rule
which works simultaneously for every finite positive rescaling of the
canonical reference measure.  In particular, the rule does not depend on
the raw variance scale. -/
theorem
    exists_total_canonicalUniversalReduced_dominator_all_scalings_of_completeClass
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcomplete :
      UniversalMeasurableFiniteBayesCompleteClassProperty
        (universalReducedObservationReference
          universalReducedLebesgueMeasure a b)
        a b) :
    ∃ δ : ℝ × ℝ → ℝ,
      Measurable δ ∧
      ∀ c : ℝ≥0∞, c ≠ 0 → c ≠ ∞ →
        MeasurableDensitySquaredRiskDominates
          (universalReducedObservationReference
            (c • universalReducedLebesgueMeasure) a b)
          (universalReducedLikelihood a b)
          (fun θ => (θ : ℝ))
          (universalReducedRuleOnObservation δ)
          universalReducedBaseline := by
  obtain ⟨δ, hδ, hdom⟩ :=
    exists_total_canonicalUniversalReduced_dominator_of_completeClass
      ha hb hcomplete
  refine ⟨δ, hδ, ?_⟩
  intro c hc0 hctop
  rw [universalReducedObservationReference_smul]
  exact hdom.smul_measure c hc0 hctop

/-- Fixed-scaling corollary of the simultaneous result. -/
theorem
    exists_total_scaled_canonicalUniversalReduced_dominator_of_completeClass
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcomplete :
      UniversalMeasurableFiniteBayesCompleteClassProperty
        (universalReducedObservationReference
          universalReducedLebesgueMeasure a b)
        a b)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ∞) :
    ∃ δ : ℝ × ℝ → ℝ,
      Measurable δ ∧
      MeasurableDensitySquaredRiskDominates
        (universalReducedObservationReference
          (c • universalReducedLebesgueMeasure) a b)
        (universalReducedLikelihood a b)
        (fun θ => (θ : ℝ))
        (universalReducedRuleOnObservation δ)
        universalReducedBaseline := by
  obtain ⟨δ, hδ, hall⟩ :=
    exists_total_canonicalUniversalReduced_dominator_all_scalings_of_completeClass
      ha hb hcomplete
  exact ⟨δ, hδ, hall c hc0 hctop⟩

/-- Simultaneous scaling theorem stated with only the local
finite-measure Brown obligation. -/
theorem
    exists_total_canonicalUniversalReduced_dominator_all_scalings_of_compatibleLocal
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlocal :
      CompleteClass.MeasurableCompatibleLocalCompleteClassProperty
        (m :=
          universalReducedObservationReference
            universalReducedLebesgueMeasure a b)
        (universalReducedLikelihood a b)
        (fun θ : UniversalInteriorTheta => (θ : ℝ))) :
    ∃ δ : ℝ × ℝ → ℝ,
      Measurable δ ∧
      ∀ c : ℝ≥0∞, c ≠ 0 → c ≠ ∞ →
        MeasurableDensitySquaredRiskDominates
          (universalReducedObservationReference
            (c • universalReducedLebesgueMeasure) a b)
          (universalReducedLikelihood a b)
          (fun θ => (θ : ℝ))
          (universalReducedRuleOnObservation δ)
          universalReducedBaseline := by
  apply
    exists_total_canonicalUniversalReduced_dominator_all_scalings_of_completeClass
      ha hb
  exact
    CompleteClass.measurablePositiveFiniteBayesCompleteClassProperty_of_compatibleLocal
      hlocal

/-! ## Realizing every interior oracle parameter by raw variances -/

/-- A positive population variance for sample one whose sample-mean
variance is exactly `θ`. -/
def universalRawVariance1Realizing
    (ν₁ : ℕ) (θ : UniversalInteriorTheta) : NNReal :=
  ⟨((ν₁ : ℝ) + 1) * (θ : ℝ),
    mul_nonneg (by positivity) θ.property.1.le⟩

/-- A positive population variance for sample two whose sample-mean
variance is exactly `1-θ`. -/
def universalRawVariance2Realizing
    (ν₂ : ℕ) (θ : UniversalInteriorTheta) : NNReal :=
  ⟨((ν₂ : ℝ) + 1) * (1 - (θ : ℝ)),
    mul_nonneg (by positivity) (sub_nonneg.mpr θ.property.2.le)⟩

@[simp]
theorem universalRawVariance1Realizing_coe
    (ν₁ : ℕ) (θ : UniversalInteriorTheta) :
    (universalRawVariance1Realizing ν₁ θ : ℝ)
      =
    ((ν₁ : ℝ) + 1) * (θ : ℝ) :=
  rfl

@[simp]
theorem universalRawVariance2Realizing_coe
    (ν₂ : ℕ) (θ : UniversalInteriorTheta) :
    (universalRawVariance2Realizing ν₂ θ : ℝ)
      =
    ((ν₂ : ℝ) + 1) * (1 - (θ : ℝ)) :=
  rfl

theorem universalRawVariance1Realizing_pos
    (ν₁ : ℕ) (θ : UniversalInteriorTheta) :
    0 < universalRawVariance1Realizing ν₁ θ := by
  change 0 < ((ν₁ : ℝ) + 1) * (θ : ℝ)
  exact mul_pos (by positivity) θ.property.1

theorem universalRawVariance2Realizing_pos
    (ν₂ : ℕ) (θ : UniversalInteriorTheta) :
    0 < universalRawVariance2Realizing ν₂ θ := by
  change 0 < ((ν₂ : ℝ) + 1) * (1 - (θ : ℝ))
  exact mul_pos (by positivity) (sub_pos.mpr θ.property.2)

/-- Surjectivity of the raw oracle coordinate: every `θ ∈ (0,1)` is
realized exactly by positive population variances, at every fixed pair of
residual degrees of freedom. -/
theorem universalRawOracleTheta_realizing
    (ν₁ ν₂ : ℕ) (θ : UniversalInteriorTheta) :
    universalRawOracleTheta ν₁ ν₂
        (universalRawVariance1Realizing ν₁ θ)
        (universalRawVariance2Realizing ν₂ θ)
      =
    (θ : ℝ) := by
  unfold universalRawOracleTheta oracleVarianceWeightU
  simp only [universalRawVariance1Realizing_coe,
    universalRawVariance2Realizing_coe]
  have hν₁ : (ν₁ : ℝ) + 1 ≠ 0 := by positivity
  have hν₂ : (ν₂ : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-! ## Automatic use of the measurable raw-coordinate lift -/

/-- Weak raw transport with the measurable lift and its a.e. coordinate
identity discharged automatically. -/
theorem universalRaw_sqRisk_le_of_density_domination_lifted
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (hraw : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (hθ : (θ : ℝ) = universalRawOracleTheta ν₁ ν₂ v₁ v₂)
    {reference Q : Measure UniversalReducedObservation}
    (hDensity : HasUniversalReducedDensity reference Q a b θ)
    (hWeighted :
      HasWeightedReducedLaw P
        (meanDifferenceU ν₁ ν₂ X Y)
        (universalRawReducedObservation ν₁ ν₂ X Y) Q)
    (δ : ℝ × ℝ → ℝ) (hδ : Measurable δ)
    (hle :
      densitySquaredRisk
          (universalReducedObservationReference reference a b)
          (universalReducedLikelihood a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          (universalReducedRuleOnObservation δ) θ
        ≤
      densitySquaredRisk
          (universalReducedObservationReference reference a b)
          (universalReducedLikelihood a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          universalReducedBaseline θ) :
    sqRisk μ (universalRawReducedEstimator δ ν₁ ν₂ X Y) P
      ≤
    sqRisk μ (universalRawGraybillDealEstimator ν₁ ν₂ X Y) P := by
  apply universalRaw_sqRisk_le_of_density_domination
    hraw hX hY ha hb θ hθ hDensity hWeighted
    (measurable_universalRawReducedObservation hX hY)
    (hraw.ae_coe_universalRawReducedObservation_eq
      hν₁ hν₂ (by exact_mod_cast hv₁) (by exact_mod_cast hv₂))
    δ hδ hle

/-- Strict raw transport with the measurable lift and its a.e. coordinate
identity discharged automatically. -/
theorem universalRaw_sqRisk_lt_of_density_domination_lifted
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (hraw : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (hθ : (θ : ℝ) = universalRawOracleTheta ν₁ ν₂ v₁ v₂)
    {reference Q : Measure UniversalReducedObservation}
    (hDensity : HasUniversalReducedDensity reference Q a b θ)
    (hWeighted :
      HasWeightedReducedLaw P
        (meanDifferenceU ν₁ ν₂ X Y)
        (universalRawReducedObservation ν₁ ν₂ X Y) Q)
    (δ : ℝ × ℝ → ℝ) (hδ : Measurable δ)
    (hlt :
      densitySquaredRisk
          (universalReducedObservationReference reference a b)
          (universalReducedLikelihood a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          (universalReducedRuleOnObservation δ) θ
        <
      densitySquaredRisk
          (universalReducedObservationReference reference a b)
          (universalReducedLikelihood a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          universalReducedBaseline θ) :
    sqRisk μ (universalRawReducedEstimator δ ν₁ ν₂ X Y) P
      <
    sqRisk μ (universalRawGraybillDealEstimator ν₁ ν₂ X Y) P := by
  apply universalRaw_sqRisk_lt_of_density_domination
    hraw hX hY ha hb θ hθ hDensity hWeighted
    (measurable_universalRawReducedObservation hX hY)
    (hraw.ae_coe_universalRawReducedObservation_eq
      hν₁ hν₂ (by exact_mod_cast hv₁) (by exact_mod_cast hv₂))
    δ hδ hlt

/-! ## Conditional raw conclusion at one arbitrary parameter point -/

/-- The strongest pointwise raw conclusion available from the current
formalization without postulating a change-of-variables theorem.

The returned rule comes solely from the sample-size complete-class input.
It is independent of `μ`, `v₁`, `v₂`, and the positive scale `c`.
The two exact raw law identities are explicit hypotheses. -/
theorem
    exists_universalRaw_reducedEstimator_le_of_completeClass_and_laws
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (hraw : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (hcomplete :
      UniversalMeasurableFiniteBayesCompleteClassProperty
        (universalReducedObservationReference
          universalReducedLebesgueMeasure
          (universalShape (ν₁ + 1)) (universalShape (ν₂ + 1)))
        (universalShape (ν₁ + 1)) (universalShape (ν₂ + 1)))
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    {Q : Measure UniversalReducedObservation}
    (hDensity :
      HasUniversalReducedDensity
        (c • universalReducedLebesgueMeasure) Q
        (universalShape (ν₁ + 1)) (universalShape (ν₂ + 1))
        (universalRawOracleInteriorTheta ν₁ ν₂ v₁ v₂ hv₁ hv₂))
    (hWeighted :
      HasWeightedReducedLaw P
        (meanDifferenceU ν₁ ν₂ X Y)
        (universalRawReducedObservation ν₁ ν₂ X Y) Q) :
    ∃ δ : ℝ × ℝ → ℝ,
      Measurable δ ∧
      sqRisk μ (universalRawReducedEstimator δ ν₁ ν₂ X Y) P
        ≤
      sqRisk μ (universalRawGraybillDealEstimator ν₁ ν₂ X Y) P := by
  have ha : 0 < universalShape (ν₁ + 1) :=
    universalShape_residualDegrees_pos hν₁
  have hb : 0 < universalShape (ν₂ + 1) :=
    universalShape_residualDegrees_pos hν₂
  obtain ⟨δ, hδ, hall⟩ :=
    exists_total_canonicalUniversalReduced_dominator_all_scalings_of_completeClass
      ha hb hcomplete
  let θ :=
    universalRawOracleInteriorTheta ν₁ ν₂ v₁ v₂ hv₁ hv₂
  have hdom := hall c hc0 hctop
  refine ⟨δ, hδ, ?_⟩
  apply universalRaw_sqRisk_le_of_density_domination_lifted
    hraw hX hY hν₁ hν₂ hv₁ hv₂ ha hb θ
    (universalRawOracleInteriorTheta_coe
      ν₁ ν₂ v₁ v₂ hv₁ hv₂)
    hDensity hWeighted δ hδ
  exact hdom.2.1 θ

/-- The reduced dominator's strict parameter is always realized by
positive raw variances.  This is the final purely algebraic ingredient
needed before applying the strict lifted transport theorem at that
parameter. -/
theorem
    exists_strict_scaled_parameter_with_realizing_rawVariances_of_completeClass
    {ν₁ ν₂ : ℕ}
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hcomplete :
      UniversalMeasurableFiniteBayesCompleteClassProperty
        (universalReducedObservationReference
          universalReducedLebesgueMeasure
          (universalShape (ν₁ + 1)) (universalShape (ν₂ + 1)))
        (universalShape (ν₁ + 1)) (universalShape (ν₂ + 1)))
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ∞) :
    ∃ δ : ℝ × ℝ → ℝ,
      ∃ θ : UniversalInteriorTheta,
      ∃ v₁ v₂ : NNReal,
        Measurable δ ∧
        0 < v₁ ∧ 0 < v₂ ∧
        universalRawOracleTheta ν₁ ν₂ v₁ v₂ = (θ : ℝ) ∧
        densitySquaredRisk
            (universalReducedObservationReference
              (c • universalReducedLebesgueMeasure)
              (universalShape (ν₁ + 1)) (universalShape (ν₂ + 1)))
            (universalReducedLikelihood
              (universalShape (ν₁ + 1)) (universalShape (ν₂ + 1)))
            (fun η : UniversalInteriorTheta => (η : ℝ))
            (universalReducedRuleOnObservation δ) θ
          <
        densitySquaredRisk
            (universalReducedObservationReference
              (c • universalReducedLebesgueMeasure)
              (universalShape (ν₁ + 1)) (universalShape (ν₂ + 1)))
            (universalReducedLikelihood
              (universalShape (ν₁ + 1)) (universalShape (ν₂ + 1)))
            (fun η : UniversalInteriorTheta => (η : ℝ))
            universalReducedBaseline θ := by
  have ha : 0 < universalShape (ν₁ + 1) :=
    universalShape_residualDegrees_pos hν₁
  have hb : 0 < universalShape (ν₂ + 1) :=
    universalShape_residualDegrees_pos hν₂
  obtain ⟨δ, hδ, hdom⟩ :=
    exists_total_scaled_canonicalUniversalReduced_dominator_of_completeClass
      ha hb hcomplete c hc0 hctop
  obtain ⟨θ, hstrict⟩ := hdom.2.2
  let v₁ := universalRawVariance1Realizing ν₁ θ
  let v₂ := universalRawVariance2Realizing ν₂ θ
  refine ⟨δ, θ, v₁, v₂, hδ, ?_, ?_, ?_, hstrict⟩
  · exact universalRawVariance1Realizing_pos ν₁ θ
  · exact universalRawVariance2Realizing_pos ν₂ θ
  · exact universalRawOracleTheta_realizing ν₁ ν₂ θ

end

end GraybillDeal
