import GraybillDeal.UniversalRawAdmissibility
import GraybillDeal.UniversalRawReducedDensityLaw

/-!
# From the component-density identity to the full raw law family

`UniversalRawReducedDensityLaw` reduces the raw change-of-variables
calculation to a deterministic identity for an explicit product of three
Gamma measures.  This file packages that pointwise identity uniformly over
all positive variance pairs and feeds it into the all-parameter
admissibility wrapper.

No complete-class or density identity is asserted as an axiom: both remain
ordinary theorem hypotheses until their respective analytic proofs are
supplied.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Exact deterministic component-density identities at every positive
variance pair supply the full raw reduced-law family. -/
theorem hasUniversalRawReducedLawFamily_of_componentDensityIdentities
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : ℝ → NNReal → NNReal → Measure Ω}
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hfamily : IsUniversalTwoNormalSampleFamily ν₁ ν₂ X Y P)
    (hdet :
      ∀ (v₁ v₂ : NNReal) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂),
        UniversalRiskTiltedComponentReducedDensityIdentity
          ν₁ ν₂ v₁ v₂ hv₁ hv₂) :
    HasUniversalRawReducedLawFamily ν₁ ν₂ X Y P := by
  intro μ v₁ v₂ hv₁ hv₂
  let Q :=
    universalRawRiskWeightedReducedMeasure ν₁ ν₂ X Y (P μ v₁ v₂)
  refine ⟨Q, ?_, ?_⟩
  · have hDensity :=
      hasUniversalReducedDensity_universalRawRiskWeightedReducedMeasure
        (hfamily μ v₁ v₂) hX hY hν₁ hν₂ hv₁ hv₂
        (hdet v₁ v₂ hv₁ hv₂)
    simpa only [universalShape_residualDegrees] using hDensity
  · exact
      hasWeightedReducedLaw_universalRawRiskWeightedReducedMeasure
        ν₁ ν₂ X Y (P μ v₁ v₂)

/-- The universal raw dominator, conditional only on the two named
mathematical inputs: the local complete-class theorem and the explicit
deterministic Gamma pushforward. -/
theorem
    exists_universalRaw_dominator_of_completeClass_and_componentDensityIdentities
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : ℝ → NNReal → NNReal → Measure Ω}
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hfamily : IsUniversalTwoNormalSampleFamily ν₁ ν₂ X Y P)
    (hdet :
      ∀ (v₁ v₂ : NNReal) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂),
        UniversalRiskTiltedComponentReducedDensityIdentity
          ν₁ ν₂ v₁ v₂ hv₁ hv₂)
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
  apply
    exists_universalRaw_dominator_of_completeClass_and_lawFamily
      hν₁ hν₂ hX hY hfamily
  · exact
      hasUniversalRawReducedLawFamily_of_componentDensityIdentities
        hν₁ hν₂ hX hY hfamily hdet
  · exact hcomplete

/-- Conditional universal failure of raw measurable admissibility, with
the concrete density calculation exposed as the only raw-law input. -/
theorem
    universalRawGraybillDeal_not_admissible_of_completeClass_and_componentDensityIdentities
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : ℝ → NNReal → NNReal → Measure Ω}
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hfamily : IsUniversalTwoNormalSampleFamily ν₁ ν₂ X Y P)
    (hdet :
      ∀ (v₁ v₂ : NNReal) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂),
        UniversalRiskTiltedComponentReducedDensityIdentity
          ν₁ ν₂ v₁ v₂ hv₁ hv₂)
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
    (exists_universalRaw_dominator_of_completeClass_and_componentDensityIdentities
      hν₁ hν₂ hX hY hfamily hdet hcomplete)

end

end GraybillDeal
