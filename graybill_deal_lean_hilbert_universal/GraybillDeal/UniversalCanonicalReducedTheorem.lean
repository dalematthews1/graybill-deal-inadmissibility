import GraybillDeal.UniversalMeasurableCompleteClassBridge
import GraybillDeal.UniversalCompleteClassExhaustion
import GraybillDeal.UniversalReferenceMeasure

/-!
# Canonical universal reduced inadmissibility theorem

This module specializes the measurable complete-class endgame to the
canonical dominating measure.  Sigma-finiteness and positivity on
nonempty open sets are discharged here, rather than being carried as
abstract hypotheses.

The one remaining hypothesis is named explicitly:
`UniversalMeasurableFiniteBayesCompleteClassProperty`.  It is precisely
the finite-support Bayes approximation conclusion of the
Brown/Lehmann--Casella complete-class theorem.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

/-- The canonical universal reduced experiment satisfies all of the
dominated-model regularity properties already formalized in the project. -/
theorem canonicalUniversalReducedDominatedRegularity
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    UniversalReducedDominatedRegularity
      (universalReducedObservationReference
        universalReducedLebesgueMeasure a b)
      a b := by
  exact universalReducedDominatedRegularity
    (universalReducedObservationReference
      universalReducedLebesgueMeasure a b)
    ha hb

/-- Conditional universal reduced theorem at arbitrary positive residual
shapes, with the reference-measure assumptions fully discharged. -/
theorem
    canonicalUniversalReducedBaseline_not_measurablyAdmissible_of_completeClass
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcomplete :
      UniversalMeasurableFiniteBayesCompleteClassProperty
        (universalReducedObservationReference
          universalReducedLebesgueMeasure a b)
        a b) :
    ¬ IsMeasurablyAdmissibleDensitySquared
      (universalReducedObservationReference
        universalReducedLebesgueMeasure a b)
      (universalReducedLikelihood a b)
      (fun θ => (θ : ℝ))
      universalReducedBaseline := by
  exact
    universalReducedBaseline_not_measurablyAdmissible_of_measurableCompleteClass
      (universalReducedObservationReference
        universalReducedLebesgueMeasure a b)
      ha hb
      (universalReducedObservationReference_open_pos ha hb)
      hcomplete

/-- The canonical universal reduced theorem for every pair of normal
sample sizes `n₁,n₂ ≥ 2`, conditional only on the specialized
complete-class conclusion. -/
theorem
    canonicalUniversalReducedBaseline_not_measurablyAdmissible_sampleSizes_of_completeClass
    {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (hcomplete :
      UniversalMeasurableFiniteBayesCompleteClassProperty
        (universalReducedObservationReference
          universalReducedLebesgueMeasure
          (universalShape n₁) (universalShape n₂))
        (universalShape n₁) (universalShape n₂)) :
    ¬ IsMeasurablyAdmissibleDensitySquared
      (universalReducedObservationReference
        universalReducedLebesgueMeasure
        (universalShape n₁) (universalShape n₂))
      (universalReducedLikelihood
        (universalShape n₁) (universalShape n₂))
      (fun θ => (θ : ℝ))
      universalReducedBaseline := by
  exact
    canonicalUniversalReducedBaseline_not_measurablyAdmissible_of_completeClass
      (universalShape_pos hn₁)
      (universalShape_pos hn₂)
      hcomplete

/-- Canonical reduced inadmissibility from the sharply localized Brown
obligation on the canonical sigma-finite exhaustion. -/
theorem
    canonicalUniversalReducedBaseline_not_measurablyAdmissible_of_compatibleLocal
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlocal :
      CompleteClass.MeasurableCompatibleLocalCompleteClassProperty
        (m :=
          universalReducedObservationReference
            universalReducedLebesgueMeasure a b)
        (universalReducedLikelihood a b)
        (fun θ : UniversalInteriorTheta => (θ : ℝ))) :
    ¬ IsMeasurablyAdmissibleDensitySquared
      (universalReducedObservationReference
        universalReducedLebesgueMeasure a b)
      (universalReducedLikelihood a b)
      (fun θ => (θ : ℝ))
      universalReducedBaseline := by
  apply
    canonicalUniversalReducedBaseline_not_measurablyAdmissible_of_completeClass
      ha hb
  exact
    CompleteClass.measurablePositiveFiniteBayesCompleteClassProperty_of_compatibleLocal
      hlocal

/-- Sample-size specialization of the local-exhaustion formulation. -/
theorem
    canonicalUniversalReducedBaseline_not_measurablyAdmissible_sampleSizes_of_compatibleLocal
    {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (hlocal :
      CompleteClass.MeasurableCompatibleLocalCompleteClassProperty
        (m :=
          universalReducedObservationReference
            universalReducedLebesgueMeasure
            (universalShape n₁) (universalShape n₂))
        (universalReducedLikelihood
          (universalShape n₁) (universalShape n₂))
        (fun θ : UniversalInteriorTheta => (θ : ℝ))) :
    ¬ IsMeasurablyAdmissibleDensitySquared
      (universalReducedObservationReference
        universalReducedLebesgueMeasure
        (universalShape n₁) (universalShape n₂))
      (universalReducedLikelihood
        (universalShape n₁) (universalShape n₂))
      (fun θ => (θ : ℝ))
      universalReducedBaseline := by
  exact
    canonicalUniversalReducedBaseline_not_measurablyAdmissible_of_compatibleLocal
      (universalShape_pos hn₁)
      (universalShape_pos hn₂)
      hlocal

end

end GraybillDeal
