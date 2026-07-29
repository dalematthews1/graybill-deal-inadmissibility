import GraybillDeal.UniversalCanonicalReducedTheorem
import GraybillDeal.UniversalLocalCompleteClassRiskSet

/-!
# Canonical reduced theorem from local closed/convex risk sets

This module connects the reusable local risk-set closure criterion directly
to the canonical universal Graybill--Deal contradiction.  It makes the
remaining Brown obligation a single explicit proposition:
`MeasurableClosedConvexLocalRiskSetProperty`.

No assertion that this property holds is made here.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

/-- Arbitrary positive-shape canonical reduced theorem, conditional on
the explicit stagewise closed/convex local risk-set property. -/
theorem
    canonicalUniversalReducedBaseline_not_measurablyAdmissible_of_closedConvexLocalRiskSets
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hrisk :
      CompleteClass.MeasurableClosedConvexLocalRiskSetProperty
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
    canonicalUniversalReducedBaseline_not_measurablyAdmissible_of_compatibleLocal
      ha hb
  exact
    CompleteClass.measurableCompatibleLocalCompleteClassProperty_of_closedConvexLocalRiskSets
      (measurable_universalReducedLikelihood_observation ha hb)
      (fun θ : UniversalInteriorTheta => (θ : ℝ))
      hrisk

/-- Every-pair sample-size specialization of the closed/convex local
risk-set formulation. -/
theorem
    canonicalUniversalReducedBaseline_not_measurablyAdmissible_sampleSizes_of_closedConvexLocalRiskSets
    {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (hrisk :
      CompleteClass.MeasurableClosedConvexLocalRiskSetProperty
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
    canonicalUniversalReducedBaseline_not_measurablyAdmissible_of_closedConvexLocalRiskSets
      (universalShape_pos hn₁)
      (universalShape_pos hn₂)
      hrisk

end

end GraybillDeal
