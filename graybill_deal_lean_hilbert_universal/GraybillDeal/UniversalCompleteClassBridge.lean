import GraybillDeal.UniversalAnalyticContradiction
import GraybillDeal.UniversalInteriorDecision
import GraybillDeal.UniversalReducedAELimitBridge

/-!
# From the finite-Bayes complete-class conclusion to inadmissibility

This module assembles the formalized universal endgame.

The only decision-theoretic input is the explicitly named proposition
`UniversalInteriorFiniteBayesCompleteClassProperty`.  No theorem asserting
that proposition is introduced here: formalizing the Lehmann--Casella
finite-Bayes approximation theorem remains a separate task.

Given that input on the genuine reduced sample space
`(0,1) × (0,∞)`, the proof is now completely formal:

1. admissibility supplies positive finite-prior Bayes approximants;
2. endpoint reweighting and compactness supply one limiting probability
   measure on `[0,1]`;
3. a.e. equality becomes pointwise equality for `q > 0`;
4. continuity along `q_n = 1/(n+1)` supplies the identity at `q = 0`;
5. the universal equal/unequal analytic contradiction rules out that
   probability measure.
-/

namespace GraybillDeal

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- The ordinary open-space Bayes action equals the endpoint-reweighted
finite posterior action used by the compactness bridge. -/
theorem PositiveFinitePrior.bayesAction_reducedLikelihood_eq_fullReduced
    (π : PositiveFinitePrior UniversalInteriorTheta)
    (a b : ℝ) (x : UniversalReducedObservation) :
    π.bayesAction
        (universalReducedLikelihood a b)
        (fun θ => (θ : ℝ)) x
      =
    π.toUniversalInteriorFinitePrior.fullReducedPosteriorAction
      a b x.r x.q := by
  unfold PositiveFinitePrior.bayesAction
    PositiveFinitePrior.posteriorWeight
    universalReducedLikelihood
    UniversalInteriorFinitePrior.fullReducedPosteriorAction
  congr 1
  funext i
  simp only [PositiveFinitePrior.toUniversalInteriorFinitePrior]
  ring

/-- The complete-class-to-contradiction theorem at arbitrary positive
gamma shapes.

The reference measure is assumed to charge every nonempty open subset of
the genuine reduced sample space.  This is the exact support property used
to turn the a.e. limiting-Bayes conclusion into pointwise equality.
-/
theorem universalReducedBaseline_not_admissible_of_completeClass
    (ρ : Measure UniversalReducedObservation)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hopen :
      ∀ U : Set UniversalReducedObservation,
        IsOpen U → U.Nonempty → 0 < ρ U)
    (hcomplete :
      UniversalInteriorFiniteBayesCompleteClassProperty
        ρ
        (universalReducedLikelihood a b)
        (fun θ => (θ : ℝ))) :
    ¬ IsAdmissibleDensitySquared
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

/-- Sample-size specialization: conditional only on the finite-Bayes
complete-class property, the reduced Graybill--Deal rule is inadmissible
for every `n₁,n₂ ≥ 2`. -/
theorem universalReducedBaseline_not_admissible_sampleSizes_of_completeClass
    (ρ : Measure UniversalReducedObservation)
    {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (hopen :
      ∀ U : Set UniversalReducedObservation,
        IsOpen U → U.Nonempty → 0 < ρ U)
    (hcomplete :
      UniversalInteriorFiniteBayesCompleteClassProperty
        ρ
        (universalReducedLikelihood
          (universalShape n₁) (universalShape n₂))
        (fun θ => (θ : ℝ))) :
    ¬ IsAdmissibleDensitySquared
      ρ
      (universalReducedLikelihood
        (universalShape n₁) (universalShape n₂))
      (fun θ => (θ : ℝ))
      universalReducedBaseline :=
  universalReducedBaseline_not_admissible_of_completeClass
    ρ
    (universalShape_pos hn₁)
    (universalShape_pos hn₂)
    hopen hcomplete

end

end GraybillDeal
