import GraybillDeal.UniversalHilbertStrongConvergence
import GraybillDeal.UniversalHilbertBayesExtraction
import GraybillDeal.UniversalHilbertAdmissibleIdentification

/-!
# The measurable finite-Bayes complete-class theorem

The preceding Hilbert modules give, for every measurably admissible rule:

1. membership in the weak closure of anchor-risk-bounded positive
   finite-prior Bayes rules;
2. a weakly convergent sequence of such rules with selected priors;
3. strong `L²` convergence, by the anchor-risk Hilbert argument;
4. an almost-everywhere convergent subsequence.

This file composes those results into the exact complete-class property
used by the universal Graybill--Deal contradiction.
-/

namespace GraybillDeal

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

/-- A point in the canonical finite-Bayes witness closure is represented
almost everywhere by a sequence of positive finite-prior Bayes actions,
provided its `L²` representative agrees with the requested estimator. -/
theorem
    hasPositiveFiniteBayesApproximation_of_universalHilbertBayesWitnessClosure
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    [IsFiniteMeasure
      (universalHilbertProbabilityMeasure ν₁ ν₂)]
    (d₀ :
      WeakSpace ℝ
        (Lp ℝ 2
          (universalHilbertProbabilityMeasure ν₁ ν₂)))
    (hd₀ :
      d₀ ∈ closure
        (universalHilbertFiniteBayesWitnessSet ν₁ ν₂ d₀))
    {estimator : UniversalReducedObservation → ℝ}
    (hd₀ae :
      (fun x =>
        ((toWeakSpace ℝ
            (Lp ℝ 2
              (universalHilbertProbabilityMeasure ν₁ ν₂))).symm
          d₀) x)
        =ᵐ[universalHilbertDominatingMeasure ν₁ ν₂]
      estimator) :
    HasPositiveFiniteBayesApproximation
      (universalHilbertDominatingMeasure ν₁ ν₂)
      (universalReducedLikelihood
        ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2))
      (fun θ : UniversalInteriorTheta => (θ : ℝ))
      estimator := by
  obtain ⟨b, π, hbweak, hb⟩ :=
    exists_sequence_with_selected_universalFinitePriors d₀ hd₀
  have hstrong :
      Tendsto
        (fun n =>
          (toWeakSpace ℝ
            (Lp ℝ 2
              (universalHilbertProbabilityMeasure ν₁ ν₂))).symm
            (b n))
        atTop
        (𝓝
          ((toWeakSpace ℝ
            (Lp ℝ 2
              (universalHilbertProbabilityMeasure ν₁ ν₂))).symm
            d₀)) := by
    apply
      tendsto_strong_of_tendsto_weak_of_anchorRisk_le
        b d₀ (universalHilbertTheta : ℝ) hbweak
    intro n
    exact (hb n).1.2.1
  exact
    hasPositiveFiniteBayesApproximation_of_tendsto_Lp
      (μ := universalHilbertProbabilityMeasure ν₁ ν₂)
      (ρ := universalHilbertDominatingMeasure ν₁ ν₂)
      (universalHilbertDominatingMeasure_absolutelyContinuous
        hν₁ hν₂)
      (fun n =>
        (toWeakSpace ℝ
          (Lp ℝ 2
            (universalHilbertProbabilityMeasure ν₁ ν₂))).symm
          (b n))
      ((toWeakSpace ℝ
        (Lp ℝ 2
          (universalHilbertProbabilityMeasure ν₁ ν₂))).symm d₀)
      π hstrong
      (fun n => (hb n).2)
      hd₀ae

/-- The complete-class theorem for the canonical universal reduced
experiment at arbitrary positive residual degrees of freedom. -/
theorem universalMeasurableFiniteBayesCompleteClassProperty_halfShapes
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂) :
    UniversalMeasurableFiniteBayesCompleteClassProperty
      (universalHilbertDominatingMeasure ν₁ ν₂)
      ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2) := by
  letI :
      IsProbabilityMeasure
        (universalHilbertProbabilityMeasure ν₁ ν₂) :=
    isProbabilityMeasure_universalHilbertProbabilityMeasure
      hν₁ hν₂
  intro estimator hadmissible
  let d₀ :
      WeakSpace ℝ
        (Lp ℝ 2
          (universalHilbertProbabilityMeasure ν₁ ν₂)) :=
    universalHilbertActionOfMeasurablyAdmissible
      hν₁ hν₂ hadmissible
  apply
    hasPositiveFiniteBayesApproximation_of_universalHilbertBayesWitnessClosure
      hν₁ hν₂ d₀
  · exact
      universalHilbertActionOfMeasurablyAdmissible_mem_bayesWitnessClosure
        hν₁ hν₂ hadmissible
  · exact
      universalHilbertActionOfMeasurablyAdmissible_ae_eq
        hν₁ hν₂ hadmissible

end

end GraybillDeal
