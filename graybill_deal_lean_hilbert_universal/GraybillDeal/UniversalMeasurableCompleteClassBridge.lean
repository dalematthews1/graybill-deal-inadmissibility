import GraybillDeal.UniversalCompleteClassBridge
import GraybillDeal.UniversalMeasurableDecision

/-!
# Measurability-correct complete-class endgame

This file repeats the final conditional implication using the exact
measurable-procedure interface of the printed Lehmann--Casella theorem.
The conclusion remains inadmissibility in the project's older, stronger
sense (where competitors range over all real-valued functions): strong
admissibility implies measurable admissibility because the Graybill--Deal
baseline is continuous.

No complete-class theorem is assumed globally.  The finite-Bayes
approximation property remains an explicit hypothesis.
-/

namespace GraybillDeal

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- At arbitrary positive gamma shapes, the measurable finite-Bayes
complete-class conclusion contradicts measurable admissibility of the
reduced Graybill--Deal baseline.  In particular, this conclusion asserts
the existence of a *measurable* dominating procedure. -/
theorem
    universalReducedBaseline_not_measurablyAdmissible_of_measurableCompleteClass
    (ρ : Measure UniversalReducedObservation)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hopen :
      ∀ U : Set UniversalReducedObservation,
        IsOpen U → U.Nonempty → 0 < ρ U)
    (hcomplete :
      UniversalMeasurableFiniteBayesCompleteClassProperty ρ a b) :
    ¬ IsMeasurablyAdmissibleDensitySquared
      ρ
      (universalReducedLikelihood a b)
      (fun θ => (θ : ℝ))
      universalReducedBaseline := by
  intro hadmissible
  obtain ⟨πs, hπs⟩ :=
    hcomplete universalReducedBaseline hadmissible
  have hfull :
      ∀ᵐ x ∂ρ,
        Tendsto
          (fun n =>
            (πs n).toUniversalInteriorFinitePrior
              |>.fullReducedPosteriorAction a b x.r x.q)
          atTop (𝓝 x.r) := by
    filter_upwards [hπs] with x hx
    exact hx.congr'
      (Eventually.of_forall fun n =>
        (PositiveFinitePrior.bayesAction_reducedLikelihood_eq_fullReduced
          (πs n) a b x))
  have hexists :
      ∃ ν : ProbabilityMeasure UniversalTheta,
        UniversalPosteriorIdentity
          (ν : Measure UniversalTheta) a b :=
    exists_universalPosteriorIdentity_of_reduced_ae_finitePrior_tendsto
      (fun n => (πs n).toUniversalInteriorFinitePrior)
      ρ ha hb hopen hfull
  exact
    (not_exists_probabilityMeasure_universalPosteriorIdentity ha hb)
      hexists

/-- Corollary in the project's older, stronger admissibility sense. -/
theorem universalReducedBaseline_not_admissible_of_measurableCompleteClass
    (ρ : Measure UniversalReducedObservation)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hopen :
      ∀ U : Set UniversalReducedObservation,
        IsOpen U → U.Nonempty → 0 < ρ U)
    (hcomplete :
      UniversalMeasurableFiniteBayesCompleteClassProperty ρ a b) :
    ¬ IsAdmissibleDensitySquared
      ρ
      (universalReducedLikelihood a b)
      (fun θ => (θ : ℝ))
      universalReducedBaseline := by
  intro hadmissible
  exact
    (universalReducedBaseline_not_measurablyAdmissible_of_measurableCompleteClass
      ρ ha hb hopen hcomplete)
    (isMeasurablyAdmissible_of_isAdmissibleDensitySquared
      measurable_universalReducedBaseline hadmissible)

/-- Sample-size specialization with the statistically standard measurable
admissibility conclusion, valid for every `n₁,n₂ ≥ 2`. -/
theorem
    universalReducedBaseline_not_measurablyAdmissible_sampleSizes_of_measurableCompleteClass
    (ρ : Measure UniversalReducedObservation)
    {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (hopen :
      ∀ U : Set UniversalReducedObservation,
        IsOpen U → U.Nonempty → 0 < ρ U)
    (hcomplete :
      UniversalMeasurableFiniteBayesCompleteClassProperty
        ρ (universalShape n₁) (universalShape n₂)) :
    ¬ IsMeasurablyAdmissibleDensitySquared
      ρ
      (universalReducedLikelihood
        (universalShape n₁) (universalShape n₂))
      (fun θ => (θ : ℝ))
      universalReducedBaseline :=
  universalReducedBaseline_not_measurablyAdmissible_of_measurableCompleteClass
    ρ
    (universalShape_pos hn₁)
    (universalShape_pos hn₂)
    hopen hcomplete

/-- Sample-size specialization in the project's older, stronger
admissibility sense. -/
theorem
    universalReducedBaseline_not_admissible_sampleSizes_of_measurableCompleteClass
    (ρ : Measure UniversalReducedObservation)
    {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (hopen :
      ∀ U : Set UniversalReducedObservation,
        IsOpen U → U.Nonempty → 0 < ρ U)
    (hcomplete :
      UniversalMeasurableFiniteBayesCompleteClassProperty
        ρ (universalShape n₁) (universalShape n₂)) :
    ¬ IsAdmissibleDensitySquared
      ρ
      (universalReducedLikelihood
        (universalShape n₁) (universalShape n₂))
      (fun θ => (θ : ℝ))
      universalReducedBaseline :=
  universalReducedBaseline_not_admissible_of_measurableCompleteClass
    ρ
    (universalShape_pos hn₁)
    (universalShape_pos hn₂)
    hopen hcomplete

end

end GraybillDeal
