import GraybillDeal.UniversalFinitePriorMap
import GraybillDeal.UniversalHilbertFiniteGridPosterior
import GraybillDeal.UniversalHilbertReference

/-!
# Canonical universal finite-grid Bayes witnesses

This file specializes the abstract finite-grid posterior theorem to the
canonical universal reduced experiment.  A prior produced on the finite
grid subtype is pushed forward to the full interior parameter space, and
the corresponding Bayes actions agree definitionally.
-/

namespace GraybillDeal

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

noncomputable section

/-- Every nonempty finite grid in the universal interior parameter space
has a positive finite-prior posterior rule which weakly improves a given
clipped baseline at every point of the grid. -/
theorem exists_universalHilbertFiniteGridBayesWitness
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    [IsFiniteMeasure
      (universalHilbertProbabilityMeasure ν₁ ν₂)]
    (F : Finset UniversalInteriorTheta)
    (hF : F.Nonempty)
    (d₀ :
      WeakSpace ℝ
        (Lp ℝ 2
          (universalHilbertProbabilityMeasure ν₁ ν₂)))
    (hd₀ :
      d₀ ∈ weakHilbertActionSet
        (universalHilbertProbabilityMeasure ν₁ ν₂)) :
    ∃ dF : WeakHilbertAction
        (universalHilbertProbabilityMeasure ν₁ ν₂),
      (∀ θ : UniversalInteriorTheta, θ ∈ F →
        weakLpSquaredRisk
            (universalHilbertModelMeasure ν₁ ν₂ θ)
            (θ : ℝ)
            (dF :
              WeakSpace ℝ
                (Lp ℝ 2
                  (universalHilbertProbabilityMeasure ν₁ ν₂)))
          ≤
        weakLpSquaredRisk
            (universalHilbertModelMeasure ν₁ ν₂ θ)
            (θ : ℝ) d₀) ∧
      ∃ π : PositiveFinitePrior UniversalInteriorTheta,
        (fun x =>
          ((toWeakSpace ℝ
              (Lp ℝ 2
                (universalHilbertProbabilityMeasure ν₁ ν₂))).symm
            (dF :
              WeakSpace ℝ
                (Lp ℝ 2
                  (universalHilbertProbabilityMeasure ν₁ ν₂)))) x)
          =ᵐ[universalHilbertDominatingMeasure ν₁ ν₂]
        π.bayesAction
          (universalReducedLikelihood
            ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2))
          (fun θ : UniversalInteriorTheta => (θ : ℝ)) := by
  classical
  letI :
      IsProbabilityMeasure
        (universalHilbertProbabilityMeasure ν₁ ν₂) :=
    isProbabilityMeasure_universalHilbertProbabilityMeasure
      hν₁ hν₂
  let grid := {θ : UniversalInteriorTheta // θ ∈ F}
  let Pgrid : grid → Measure UniversalReducedObservation :=
    fun i => universalHilbertModelMeasure ν₁ ν₂ i.1
  let densityGrid :
      grid → UniversalReducedObservation → ℝ :=
    fun i =>
      universalReducedLikelihood
        ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2) i.1
  let targetGrid : grid → ℝ := fun i => (i.1 : ℝ)
  letI : Nonempty grid := hF.to_subtype
  have ha : 0 < (ν₁ : ℝ) / 2 := by positivity
  have hb : 0 < (ν₂ : ℝ) / 2 := by positivity
  have hPgridμ :
      ∀ i : grid,
        Pgrid i ≪
          universalHilbertProbabilityMeasure ν₁ ν₂ :=
    fun i =>
      universalHilbertModelMeasure_absolutelyContinuous_probability
        hν₁ hν₂ i.1
  have hPgridProb :
      ∀ i : grid, IsProbabilityMeasure (Pgrid i) :=
    fun i =>
      isProbabilityMeasure_universalHilbertModelMeasure
        hν₁ hν₂ i.1
  have hdensityGrid :
      ∀ i : grid, Measurable (densityGrid i) :=
    fun i =>
      measurable_universalReducedLikelihood_observation
        ha hb i.1
  have hdensityGridPos :
      ∀ i : grid,
        ∀ x : UniversalReducedObservation,
          0 < densityGrid i x :=
    fun i x =>
      universalReducedLikelihood_pos ha hb i.1 x
  have hPgrid :
      ∀ i : grid,
        Pgrid i =
          (universalHilbertDominatingMeasure ν₁ ν₂).withDensity
            (fun x => ENNReal.ofReal (densityGrid i x)) :=
    fun i => rfl
  have htargetGrid :
      ∀ i : grid,
        targetGrid i ∈ Set.Icc (0 : ℝ) 1 :=
    fun i => ⟨i.1.property.1.le, i.1.property.2.le⟩
  obtain ⟨dF, hdFle, πgrid, hdFbayes⟩ :=
    exists_weakHilbertFiniteGrid_posterior
      (μ := universalHilbertProbabilityMeasure ν₁ ν₂)
      (m := universalHilbertDominatingMeasure ν₁ ν₂)
      hPgridμ hPgridProb
      (universalHilbertDominatingMeasure_absolutelyContinuous
        hν₁ hν₂)
      densityGrid hdensityGrid hdensityGridPos hPgrid
      targetGrid htargetGrid d₀ hd₀
  let π : PositiveFinitePrior UniversalInteriorTheta :=
    πgrid.map (fun i : grid => i.1)
  refine ⟨dF, ?_, π, ?_⟩
  · intro θ hθ
    exact hdFle ⟨θ, hθ⟩
  · filter_upwards [hdFbayes] with x hx
    calc
      ((toWeakSpace ℝ
          (Lp ℝ 2
            (universalHilbertProbabilityMeasure ν₁ ν₂))).symm
        (dF :
          WeakSpace ℝ
            (Lp ℝ 2
              (universalHilbertProbabilityMeasure ν₁ ν₂)))) x
          =
        πgrid.bayesAction densityGrid targetGrid x :=
        hx
      _ =
        π.bayesAction
          (universalReducedLikelihood
            ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2))
          (fun θ : UniversalInteriorTheta => (θ : ℝ)) x := by
        exact
          (πgrid.bayesAction_map
            (fun i : grid => i.1)
            (universalReducedLikelihood
              ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2))
            (fun θ : UniversalInteriorTheta => (θ : ℝ))
            x).symm

end

end GraybillDeal
