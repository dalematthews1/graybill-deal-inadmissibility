import GraybillDeal.UniversalRawDensityIdentity
import GraybillDeal.UniversalRawLawFamily

/-!
# The unconditional universal raw-law theorem

The explicit Gamma pushforward identity has now been proved in
`UniversalRawDensityIdentity`.  This file substitutes that theorem into the
previously conditional raw-law assembly.  Consequently, a genuine
two-independent-normal-sample family has the required risk-weighted reduced
law at every positive variance pair, without any additional component-density
hypothesis.

The final two theorems expose the remaining decision-theoretic input cleanly:
apart from the hypotheses specifying the normal experiment and measurability
of its coordinates, only the finite-Bayes complete-class property remains.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A universal two-normal-sample family automatically has the exact
`D²`-weighted reduced law at every positive variance pair. -/
theorem hasUniversalRawReducedLawFamily_of_twoNormalSampleFamily
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : ℝ → NNReal → NNReal → Measure Ω}
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hfamily : IsUniversalTwoNormalSampleFamily ν₁ ν₂ X Y P) :
    HasUniversalRawReducedLawFamily ν₁ ν₂ X Y P := by
  apply
    hasUniversalRawReducedLawFamily_of_componentDensityIdentities
      hν₁ hν₂ hX hY hfamily
  intro v₁ v₂ hv₁ hv₂
  exact
    universalRiskTiltedComponentReducedDensityIdentity
      hν₁ hν₂ hv₁ hv₂

/-- Under the finite-Bayes complete-class property, the literal raw
Graybill--Deal estimator has a measurable universal dominator.

There is no remaining density or probability-law hypothesis: the raw law is
derived above from the two-normal-sample family. -/
theorem exists_universalRaw_dominator_of_completeClass
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : ℝ → NNReal → NNReal → Measure Ω}
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hfamily : IsUniversalTwoNormalSampleFamily ν₁ ν₂ X Y P)
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
      hasUniversalRawReducedLawFamily_of_twoNormalSampleFamily
        hν₁ hν₂ hX hY hfamily
  · exact hcomplete

/-- Universal failure of measurable admissibility for the literal raw
Graybill--Deal estimator, conditional only on the finite-Bayes complete-class
property beyond the hypotheses defining the normal experiment itself. -/
theorem universalRawGraybillDeal_not_admissible_of_completeClass
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : ℝ → NNReal → NNReal → Measure Ω}
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hfamily : IsUniversalTwoNormalSampleFamily ν₁ ν₂ X Y P)
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
    (exists_universalRaw_dominator_of_completeClass
      hν₁ hν₂ hX hY hfamily hcomplete)

end

end GraybillDeal
