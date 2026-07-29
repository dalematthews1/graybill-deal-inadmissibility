import GraybillDeal.UniversalCanonicalReducedTheorem
import GraybillDeal.UniversalReducedRuleExtension

/-!
# Extracting a concrete measurable reduced dominator

The complete-class contradiction is stated as non-admissibility.  For the
raw transport it is convenient to unpack that negation into an actual
measurable dominating rule, then extend that rule to a total measurable
function on `ℝ × ℝ`.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

variable {Θ X : Type*} [MeasurableSpace X]

theorem exists_measurable_dominator_of_not_measurablyAdmissible
    {m : Measure X} {density : Θ → X → ℝ}
    {target : Θ → ℝ} {estimator : X → ℝ}
    (hestimator : Measurable estimator)
    (hnot :
      ¬ IsMeasurablyAdmissibleDensitySquared
        m density target estimator) :
    ∃ candidate : X → ℝ,
      MeasurableDensitySquaredRiskDominates
        m density target candidate estimator := by
  by_contra hcandidate
  exact hnot ⟨hestimator, hcandidate⟩

/-- At arbitrary positive shapes, the complete-class property supplies an
actual measurable reduced dominator of the Graybill--Deal rule. -/
theorem exists_canonicalUniversalReduced_dominator_of_completeClass
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcomplete :
      UniversalMeasurableFiniteBayesCompleteClassProperty
        (universalReducedObservationReference
          universalReducedLebesgueMeasure a b)
        a b) :
    ∃ candidate : UniversalReducedObservation → ℝ,
      MeasurableDensitySquaredRiskDominates
        (universalReducedObservationReference
          universalReducedLebesgueMeasure a b)
        (universalReducedLikelihood a b)
        (fun θ => (θ : ℝ))
        candidate
        universalReducedBaseline := by
  exact
    exists_measurable_dominator_of_not_measurablyAdmissible
      measurable_universalReducedBaseline
      (canonicalUniversalReducedBaseline_not_measurablyAdmissible_of_completeClass
        ha hb hcomplete)

/-- The same dominator can be represented by a total measurable rule on
`ℝ × ℝ`, while its restriction to the genuine reduced observation space
retains the exact dominance statement. -/
theorem exists_total_canonicalUniversalReduced_dominator_of_completeClass
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcomplete :
      UniversalMeasurableFiniteBayesCompleteClassProperty
        (universalReducedObservationReference
          universalReducedLebesgueMeasure a b)
        a b) :
    ∃ δ : ℝ × ℝ → ℝ,
      Measurable δ ∧
      MeasurableDensitySquaredRiskDominates
        (universalReducedObservationReference
          universalReducedLebesgueMeasure a b)
        (universalReducedLikelihood a b)
        (fun θ => (θ : ℝ))
        (fun x : UniversalReducedObservation => δ x.1)
        universalReducedBaseline := by
  obtain ⟨candidate, hcandidate, hdom⟩ :=
    exists_canonicalUniversalReduced_dominator_of_completeClass
      ha hb hcomplete
  obtain ⟨δ, hδ, hδeq⟩ :=
    exists_measurable_universalReducedRule_extension hcandidate
  refine ⟨δ, hδ, ?_⟩
  have heq :
      (fun x : UniversalReducedObservation => δ x.1)
        = candidate :=
    funext hδeq
  rw [heq]
  exact ⟨hcandidate, hdom⟩

end

end GraybillDeal
