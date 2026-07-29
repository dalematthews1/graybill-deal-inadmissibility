import GraybillDeal.UniversalFiniteStatisticalRiskSet
import GraybillDeal.UniversalHilbertFiniteRisk

/-!
# Finite-grid supporting priors in the Hilbert experiment

This module combines compact finite-grid minimization with the project's
checked finite-dimensional risk-separation theorem.

For a nonempty finite family of normalized model measures and a clipped
baseline rule, it constructs:

* a clipped rule weakly improving the baseline at every grid point; and
* a positive finite prior on the grid which supports that rule's real risk
  vector over the entire clipped Hilbert action space.

The remaining identification of the supported rule with the posterior mean
uses the model-specific density/Bayes-risk bridge and is intentionally kept
separate.
-/

namespace GraybillDeal

open MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal Topology

noncomputable section

variable {X ι : Type*} [MeasurableSpace X]
variable {μ : Measure X} [IsFiniteMeasure μ]
variable [Fintype ι] [Nonempty ι]

/-- A compact finite-grid Pareto rule has a supporting positive finite prior
when each grid model is an absolutely continuous probability measure and
each target lies in `[0,1]`. -/
theorem exists_positiveFinitePrior_supporting_weakHilbertGrid
    {P : ι → Measure X}
    (hPμ : ∀ i, P i ≪ μ)
    (hPprob : ∀ i, IsProbabilityMeasure (P i))
    (target : ι → ℝ)
    (htarget : ∀ i, target i ∈ Set.Icc (0 : ℝ) 1)
    (d₀ : WeakSpace ℝ (Lp ℝ 2 μ))
    (hd₀ : d₀ ∈ weakHilbertActionSet μ) :
    ∃ dF : WeakHilbertAction μ,
      (∀ i,
        weakLpSquaredRisk (P i) (target i)
            (dF : WeakSpace ℝ (Lp ℝ 2 μ))
          ≤
        weakLpSquaredRisk (P i) (target i) d₀) ∧
      ∃ π : PositiveFinitePrior ι,
        ∀ d : WeakHilbertAction μ,
          (∑ j, (π.weight j : ℝ) *
            weakLpSquaredRiskReal
              (P (π.point j)) (target (π.point j))
              (dF : WeakSpace ℝ (Lp ℝ 2 μ)))
            ≤
          ∑ j, (π.weight j : ℝ) *
            weakLpSquaredRiskReal
              (P (π.point j)) (target (π.point j))
              (d : WeakSpace ℝ (Lp ℝ 2 μ)) := by
  classical
  obtain ⟨dF, hdF, hparetoENN⟩ :=
    exists_weakHilbertFiniteGrid_pareto
      (μ := μ) hPμ target d₀ hd₀
  let dFs : WeakHilbertAction μ := ⟨dF, hdF.1⟩
  let risk : WeakHilbertAction μ → ι → ℝ :=
    fun d i =>
      weakLpSquaredRiskReal (P i) (target i)
        (d : WeakSpace ℝ (Lp ℝ 2 μ))
  have hmix :
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        ∀ d e i,
          risk (weakHilbertActionMix μ a b d e) i
            ≤ a * risk d i + b * risk e i := by
    intro a b ha hb hab d e i
    letI : IsProbabilityMeasure (P i) := hPprob i
    exact
      weakLpSquaredRiskReal_actionMix_le
        (μ := μ) (hPμ i) (htarget i)
        a b ha hb hab d e
  have hparetoReal :
      ∀ d : WeakHilbertAction μ,
        ¬ ∀ i, risk d i < risk dFs i := by
    intro d hall
    apply hparetoENN
      (d : WeakSpace ℝ (Lp ℝ 2 μ)) d.2
    intro i
    letI : IsProbabilityMeasure (P i) := hPprob i
    exact
      (weakLpSquaredRiskReal_lt_iff
        (μ := μ) (hPμ i) (htarget i)
        d.2 dFs.2).mp (hall i)
  obtain ⟨π, hπ⟩ :=
    FiniteStatisticalRiskSet.exists_positiveFinitePrior_supporting_risk
      risk (weakHilbertActionMix μ) hmix dFs hparetoReal
  refine ⟨dFs, ?_, π, ?_⟩
  · intro i
    exact mem_iInter.mp hdF.2 i
  · simpa [risk, dFs] using hπ

end

end GraybillDeal
