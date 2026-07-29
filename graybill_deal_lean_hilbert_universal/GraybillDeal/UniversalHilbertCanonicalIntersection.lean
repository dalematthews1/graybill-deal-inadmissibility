import GraybillDeal.UniversalHilbertGlobalIntersection
import GraybillDeal.UniversalHilbertUniversalFiniteGrid

/-!
# Canonical compact intersection of finite-prior Bayes witnesses

For a clipped baseline rule `d₀`, let `B₀` consist of clipped weak `L²`
rules represented by positive finite-prior Bayes actions whose risk at the
distinguished parameter `θ₀ = 1/2` is no larger than that of `d₀`.

The canonical finite-grid posterior theorem supplies a member of `B₀`
meeting every finite collection of baseline risk bounds.  Weak compactness
and the finite-intersection property then produce one point in the weak
closure of `B₀` which weakly dominates `d₀` at every interior parameter.
-/

namespace GraybillDeal

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

noncomputable section

/-- Weak `L²` rules represented by positive finite-prior posterior means
and satisfying the distinguished-parameter risk bound.  The existential
prior is retained so that it can later be selected along a closure
sequence. -/
def universalHilbertFiniteBayesWitnessSet
    (ν₁ ν₂ : ℕ)
    [IsFiniteMeasure
      (universalHilbertProbabilityMeasure ν₁ ν₂)]
    (d₀ :
      WeakSpace ℝ
        (Lp ℝ 2
          (universalHilbertProbabilityMeasure ν₁ ν₂))) :
    Set
      (WeakSpace ℝ
        (Lp ℝ 2
          (universalHilbertProbabilityMeasure ν₁ ν₂))) :=
  {d |
    d ∈ weakHilbertActionSet
        (universalHilbertProbabilityMeasure ν₁ ν₂) ∧
      weakLpSquaredRisk
          (universalHilbertProbabilityMeasure ν₁ ν₂)
          (universalHilbertTheta : ℝ) d
        ≤
      weakLpSquaredRisk
          (universalHilbertProbabilityMeasure ν₁ ν₂)
          (universalHilbertTheta : ℝ) d₀ ∧
      ∃ π : PositiveFinitePrior UniversalInteriorTheta,
        (fun x =>
          ((toWeakSpace ℝ
              (Lp ℝ 2
                (universalHilbertProbabilityMeasure ν₁ ν₂))).symm
            d) x)
          =ᵐ[universalHilbertDominatingMeasure ν₁ ν₂]
        π.bayesAction
          (universalReducedLikelihood
            ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2))
          (fun θ : UniversalInteriorTheta => (θ : ℝ))}

theorem universalHilbertFiniteBayesWitnessSet_subset_action
    (ν₁ ν₂ : ℕ)
    [IsFiniteMeasure
      (universalHilbertProbabilityMeasure ν₁ ν₂)]
    (d₀ :
      WeakSpace ℝ
        (Lp ℝ 2
          (universalHilbertProbabilityMeasure ν₁ ν₂))) :
    universalHilbertFiniteBayesWitnessSet ν₁ ν₂ d₀
      ⊆
    weakHilbertActionSet
      (universalHilbertProbabilityMeasure ν₁ ν₂) :=
  fun _ hd => hd.1

/-- The finite-grid posterior witnesses establish the finite-intersection
property for the canonical Bayes-witness set. -/
theorem universalHilbertFiniteBayesWitnessSet_fip
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    [IsFiniteMeasure
      (universalHilbertProbabilityMeasure ν₁ ν₂)]
    (d₀ :
      WeakSpace ℝ
        (Lp ℝ 2
          (universalHilbertProbabilityMeasure ν₁ ν₂)))
    (hd₀ :
      d₀ ∈ weakHilbertActionSet
        (universalHilbertProbabilityMeasure ν₁ ν₂))
    (G : Finset UniversalInteriorTheta) :
    (closure
        (universalHilbertFiniteBayesWitnessSet ν₁ ν₂ d₀) ∩
      ⋂ θ ∈ G,
        {d |
          weakLpSquaredRisk
              (universalHilbertModelMeasure ν₁ ν₂ θ)
              (θ : ℝ) d
            ≤
          weakLpSquaredRisk
              (universalHilbertModelMeasure ν₁ ν₂ θ)
              (θ : ℝ) d₀}).Nonempty := by
  classical
  let F : Finset UniversalInteriorTheta :=
    insert universalHilbertTheta G
  have hF : F.Nonempty :=
    ⟨universalHilbertTheta, by simp [F]⟩
  obtain ⟨dF, hdFle, π, hdFbayes⟩ :=
    exists_universalHilbertFiniteGridBayesWitness
      hν₁ hν₂ F hF d₀ hd₀
  refine
    ⟨(dF :
        WeakSpace ℝ
          (Lp ℝ 2
            (universalHilbertProbabilityMeasure ν₁ ν₂))),
      ?_, ?_⟩
  · apply subset_closure
    refine ⟨dF.property, ?_, π, hdFbayes⟩
    simpa only
        [universalHilbertProbabilityMeasure] using
      hdFle universalHilbertTheta
        (by simp [F])
  · simp only [mem_iInter]
    intro θ hθ
    exact hdFle θ (by simp [F, hθ])

/-- There is a global weak-closure point, represented as a limit of
anchor-risk-bounded finite-prior Bayes rules, whose risk is no larger than
the baseline risk at every interior parameter. -/
theorem exists_universalHilbertBayesClosureDominator
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    [IsFiniteMeasure
      (universalHilbertProbabilityMeasure ν₁ ν₂)]
    (d₀ :
      WeakSpace ℝ
        (Lp ℝ 2
          (universalHilbertProbabilityMeasure ν₁ ν₂)))
    (hd₀ :
      d₀ ∈ weakHilbertActionSet
        (universalHilbertProbabilityMeasure ν₁ ν₂)) :
    ∃ d ∈
        closure
          (universalHilbertFiniteBayesWitnessSet ν₁ ν₂ d₀),
      ∀ θ : UniversalInteriorTheta,
        weakLpSquaredRisk
            (universalHilbertModelMeasure ν₁ ν₂ θ)
            (θ : ℝ) d
          ≤
        weakLpSquaredRisk
            (universalHilbertModelMeasure ν₁ ν₂ θ)
            (θ : ℝ) d₀ := by
  apply
    exists_global_weakHilbertRisk_below_of_fip
      (μ := universalHilbertProbabilityMeasure ν₁ ν₂)
      (P := universalHilbertModelMeasure ν₁ ν₂)
      (fun θ : UniversalInteriorTheta =>
        universalHilbertModelMeasure_absolutelyContinuous_probability
          hν₁ hν₂ θ)
      (fun θ : UniversalInteriorTheta => (θ : ℝ))
      (fun θ : UniversalInteriorTheta =>
        weakLpSquaredRisk
          (universalHilbertModelMeasure ν₁ ν₂ θ)
          (θ : ℝ) d₀)
      (universalHilbertFiniteBayesWitnessSet ν₁ ν₂ d₀)
      (universalHilbertFiniteBayesWitnessSet_subset_action
        ν₁ ν₂ d₀)
  exact universalHilbertFiniteBayesWitnessSet_fip
    hν₁ hν₂ d₀ hd₀

end

end GraybillDeal
