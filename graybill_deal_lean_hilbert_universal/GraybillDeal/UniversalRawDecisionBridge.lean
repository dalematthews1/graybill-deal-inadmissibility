import GraybillDeal.UniversalRawParameters
import GraybillDeal.UniversalReducedRiskRebase

/-!
# From universal reduced domination to raw normal-sample domination

This file assembles the already formalized pieces at one raw parameter
point.  Once supplied with the two concrete law facts

* `HasUniversalReducedDensity`;
* `HasWeightedReducedLaw`,

a weak or strict reduced dominated-risk comparison becomes the
corresponding comparison of literal raw common-mean risks.

No change-of-variables or complete-class fact is assumed globally; both
remain explicit theorem inputs.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem integrable_sq_meanDifferenceU
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    Integrable (fun ω => meanDifferenceU ν₁ ν₂ X Y ω ^ 2) P := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hD : MemLp (meanDifferenceU ν₁ ν₂ X Y) 2 P :=
    h.hasGaussianLaw_meanDifference.memLp_two
  exact (memLp_two_iff_integrable_sq hD.1).1 hD

/-- Weak reduced domination transports to weak literal raw-risk
domination at one normal-model parameter point. -/
theorem universalRaw_sqRisk_le_of_density_domination
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (hraw : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (hθ :
      (θ : ℝ) = universalRawOracleTheta ν₁ ν₂ v₁ v₂)
    {reference Q : Measure UniversalReducedObservation}
    (hDensity : HasUniversalReducedDensity reference Q a b θ)
    {Z : Ω → UniversalReducedObservation}
    (hWeighted :
      HasWeightedReducedLaw P
        (meanDifferenceU ν₁ ν₂ X Y) Z Q)
    (hZ : Measurable Z)
    (hcoords :
      ∀ᵐ ω ∂P,
        (Z ω : ℝ × ℝ) =
          universalRawReducedCoordinates ν₁ ν₂ X Y ω)
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
  have hDsq := integrable_sq_meanDifferenceU hraw
  letI : IsFiniteMeasure Q :=
    hWeighted.isFiniteMeasure hDsq
  have hcandidateMeas :
      Measurable (universalReducedRuleOnObservation δ) :=
    measurable_universalReducedRuleOnObservation hδ
  have hbaseFinite :=
    hDensity.rebased_baselineRisk_ne_top ha hb θ
  have hcandidateFinite :
      densitySquaredRisk
          (universalReducedObservationReference reference a b)
          (universalReducedLikelihood a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          (universalReducedRuleOnObservation δ) θ ≠ ⊤ :=
    ne_top_of_le_ne_top hbaseFinite hle
  have hcandidateInt :=
    hDensity.rebased_integrable_squaredError_of_finite
      ha hb θ hcandidateMeas hcandidateFinite
  have hbaselineInt :=
    integrable_universalReducedBaseline_squaredError Q θ
  have hquadraticδθ :=
    hWeighted.integrable_universalRawReduced_quadratic
      hX hY hZ hcoords hδ (θ : ℝ) hcandidateInt
  have hquadraticGDθ :=
    hWeighted.integrable_universalRawGraybillDeal_quadratic
      hX hY hZ hcoords (θ : ℝ) hbaselineInt
  have hmeasure :=
    hDensity.rebased_measureSquaredRisk_le_of_finiteLaw
      ha hb θ hcandidateMeas hle
  have hreducedθ :
      universalRawReducedSquaredRisk (θ : ℝ)
          δ ν₁ ν₂ X Y P
        ≤
      universalRawGraybillDealReducedSquaredRisk (θ : ℝ)
          ν₁ ν₂ X Y P := by
    rw [← hWeighted.measureSquaredRisk_eq_universalRawReduced
        hX hY hZ hcoords hδ θ,
      ← hWeighted.measureSquaredRisk_eq_universalRawGraybillDeal
        hX hY hZ hcoords θ]
    exact hmeasure
  have hsum :
      0 < (v₁ : ℝ) / (ν₁ + 1) + (v₂ : ℝ) / (ν₂ + 1) := by
    by_contra hnot
    have hzero :
        (v₁ : ℝ) / (ν₁ + 1) + (v₂ : ℝ) / (ν₂ + 1) = 0 := by
      exact le_antisymm (le_of_not_gt hnot)
        (add_nonneg (by positivity) (by positivity))
    have horacle :
        universalRawOracleTheta ν₁ ν₂ v₁ v₂ = 0 := by
      unfold universalRawOracleTheta oracleVarianceWeightU
      rw [hzero]
      simp
    have hθzero : (θ : ℝ) = 0 := hθ.trans horacle
    exact (ne_of_gt θ.property.1) hθzero
  apply universalRaw_sqRisk_le_graybillDeal_of_reduced
    hraw hX hY hsum δ hδ
  · simpa only [← hθ] using hquadraticδθ
  · simpa only [← hθ] using hquadraticGDθ
  · simpa only [← hθ] using hreducedθ

/-- Strict reduced domination transports to strict literal raw-risk
domination at one normal-model parameter point. -/
theorem universalRaw_sqRisk_lt_of_density_domination
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (hraw : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (hθ :
      (θ : ℝ) = universalRawOracleTheta ν₁ ν₂ v₁ v₂)
    {reference Q : Measure UniversalReducedObservation}
    (hDensity : HasUniversalReducedDensity reference Q a b θ)
    {Z : Ω → UniversalReducedObservation}
    (hWeighted :
      HasWeightedReducedLaw P
        (meanDifferenceU ν₁ ν₂ X Y) Z Q)
    (hZ : Measurable Z)
    (hcoords :
      ∀ᵐ ω ∂P,
        (Z ω : ℝ × ℝ) =
          universalRawReducedCoordinates ν₁ ν₂ X Y ω)
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
  have hle := hlt.le
  have hDsq := integrable_sq_meanDifferenceU hraw
  letI : IsFiniteMeasure Q :=
    hWeighted.isFiniteMeasure hDsq
  have hcandidateMeas :
      Measurable (universalReducedRuleOnObservation δ) :=
    measurable_universalReducedRuleOnObservation hδ
  have hbaseFinite :=
    hDensity.rebased_baselineRisk_ne_top ha hb θ
  have hcandidateFinite :
      densitySquaredRisk
          (universalReducedObservationReference reference a b)
          (universalReducedLikelihood a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          (universalReducedRuleOnObservation δ) θ ≠ ⊤ :=
    ne_top_of_le_ne_top hbaseFinite hle
  have hcandidateInt :=
    hDensity.rebased_integrable_squaredError_of_finite
      ha hb θ hcandidateMeas hcandidateFinite
  have hbaselineInt :=
    integrable_universalReducedBaseline_squaredError Q θ
  have hquadraticδθ :=
    hWeighted.integrable_universalRawReduced_quadratic
      hX hY hZ hcoords hδ (θ : ℝ) hcandidateInt
  have hquadraticGDθ :=
    hWeighted.integrable_universalRawGraybillDeal_quadratic
      hX hY hZ hcoords (θ : ℝ) hbaselineInt
  have hmeasure :=
    hDensity.rebased_measureSquaredRisk_lt_of_finiteLaw
      ha hb θ hcandidateMeas hlt
  have hreducedθ :
      universalRawReducedSquaredRisk (θ : ℝ)
          δ ν₁ ν₂ X Y P
        <
      universalRawGraybillDealReducedSquaredRisk (θ : ℝ)
          ν₁ ν₂ X Y P := by
    rw [← hWeighted.measureSquaredRisk_eq_universalRawReduced
        hX hY hZ hcoords hδ θ,
      ← hWeighted.measureSquaredRisk_eq_universalRawGraybillDeal
        hX hY hZ hcoords θ]
    exact hmeasure
  have hsum :
      0 < (v₁ : ℝ) / (ν₁ + 1) + (v₂ : ℝ) / (ν₂ + 1) := by
    by_contra hnot
    have hzero :
        (v₁ : ℝ) / (ν₁ + 1) + (v₂ : ℝ) / (ν₂ + 1) = 0 := by
      exact le_antisymm (le_of_not_gt hnot)
        (add_nonneg (by positivity) (by positivity))
    have horacle :
        universalRawOracleTheta ν₁ ν₂ v₁ v₂ = 0 := by
      unfold universalRawOracleTheta oracleVarianceWeightU
      rw [hzero]
      simp
    have hθzero : (θ : ℝ) = 0 := hθ.trans horacle
    exact (ne_of_gt θ.property.1) hθzero
  apply universalRaw_sqRisk_lt_graybillDeal_of_reduced
    hraw hX hY hsum δ hδ
  · simpa only [← hθ] using hquadraticδθ
  · simpa only [← hθ] using hquadraticGDθ
  · simpa only [← hθ] using hreducedθ

end

end GraybillDeal
