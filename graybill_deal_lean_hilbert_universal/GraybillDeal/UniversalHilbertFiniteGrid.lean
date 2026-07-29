import GraybillDeal.UniversalHilbertRisk
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Compact minimization on a finite parameter grid

This file supplies the first missing compactness wrapper in the specialized
Hilbert-space complete-class proof.

For a finite family of model measures `P i`, all absolutely continuous with
respect to the Hilbert reference measure `μ`, and a clipped baseline rule
`d₀`, consider the clipped rules whose risk at every grid point is no larger
than the corresponding risk of `d₀`.  This feasible set is nonempty and weakly
compact.  The finite sum of its weakly lower-semicontinuous risks therefore
attains a minimum.

The minimizer is Pareto efficient on the grid among all clipped rules: no
other clipped rule can have strictly smaller risk at every grid point.  This
is the exact input needed by the existing finite-dimensional supporting-prior
theorem.
-/

namespace GraybillDeal

open MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal Topology

noncomputable section

variable {X ι : Type*} [MeasurableSpace X]
variable {μ : Measure X} [IsFiniteMeasure μ]
variable [Fintype ι] [Nonempty ι]

/-- The sum of the extended-real squared risks over a finite parameter grid. -/
def weakFiniteGridRiskSum
    (P : ι → Measure X) (target : ι → ℝ)
    (f : WeakSpace ℝ (Lp ℝ 2 μ)) : ℝ≥0∞ :=
  ∑ i, weakLpSquaredRisk (P i) (target i) f

/-- A finite sum of weak squared risks is weakly lower semicontinuous. -/
theorem lowerSemicontinuous_weakFiniteGridRiskSum
    {P : ι → Measure X} (hPμ : ∀ i, P i ≪ μ)
    (target : ι → ℝ) :
    LowerSemicontinuous
      (weakFiniteGridRiskSum (μ := μ) P target) := by
  unfold weakFiniteGridRiskSum
  exact lowerSemicontinuous_sum fun i _ =>
    lowerSemicontinuous_weakLpSquaredRisk
      (hPμ i) (target i)

/-- The clipped feasible set whose grid risks are bounded by those of a
fixed baseline rule. -/
def weakHilbertFiniteGridFeasibleSet
    (P : ι → Measure X) (target : ι → ℝ)
    (d₀ : WeakSpace ℝ (Lp ℝ 2 μ)) :
    Set (WeakSpace ℝ (Lp ℝ 2 μ)) :=
  weakHilbertRiskFeasibleSet μ P target
    (fun i => weakLpSquaredRisk (P i) (target i) d₀)

/-- A clipped baseline belongs to its own finite-grid feasible set. -/
theorem baseline_mem_weakHilbertFiniteGridFeasibleSet
    (P : ι → Measure X) (target : ι → ℝ)
    {d₀ : WeakSpace ℝ (Lp ℝ 2 μ)}
    (hd₀ : d₀ ∈ weakHilbertActionSet μ) :
    d₀ ∈ weakHilbertFiniteGridFeasibleSet
      (μ := μ) P target d₀ := by
  change
    d₀ ∈ weakHilbertActionSet μ ∩
      ⋂ i,
        {f |
          weakLpSquaredRisk (P i) (target i) f
            ≤ weakLpSquaredRisk (P i) (target i) d₀}
  refine ⟨hd₀, ?_⟩
  exact mem_iInter.mpr fun i => by
    change
      weakLpSquaredRisk (P i) (target i) d₀
        ≤ weakLpSquaredRisk (P i) (target i) d₀
    exact le_rfl

/-- The baseline-bounded finite-grid feasible set is weakly compact. -/
theorem isCompact_weakHilbertFiniteGridFeasibleSet
    {P : ι → Measure X} (hPμ : ∀ i, P i ≪ μ)
    (target : ι → ℝ)
    (d₀ : WeakSpace ℝ (Lp ℝ 2 μ)) :
    IsCompact
      (weakHilbertFiniteGridFeasibleSet
        (μ := μ) P target d₀) :=
  isCompact_weakHilbertRiskFeasibleSet
    μ hPμ target
      (fun i => weakLpSquaredRisk (P i) (target i) d₀)

/-- On every nonempty finite grid, the sum of risks attains its minimum
over the clipped rules that weakly improve the baseline at every grid
point. -/
theorem exists_weakHilbertFiniteGrid_minimizer
    {P : ι → Measure X} (hPμ : ∀ i, P i ≪ μ)
    (target : ι → ℝ)
    (d₀ : WeakSpace ℝ (Lp ℝ 2 μ))
    (hd₀ : d₀ ∈ weakHilbertActionSet μ) :
    ∃ dF,
      dF ∈ weakHilbertFiniteGridFeasibleSet
        (μ := μ) P target d₀ ∧
      IsMinOn
        (weakFiniteGridRiskSum (μ := μ) P target)
        (weakHilbertFiniteGridFeasibleSet
          (μ := μ) P target d₀)
        dF := by
  let C :=
    weakHilbertFiniteGridFeasibleSet
      (μ := μ) P target d₀
  have hCne : C.Nonempty :=
    ⟨d₀,
      baseline_mem_weakHilbertFiniteGridFeasibleSet
        (μ := μ) P target hd₀⟩
  have hCcompact : IsCompact C :=
    isCompact_weakHilbertFiniteGridFeasibleSet
      (μ := μ) hPμ target d₀
  have hlsc :
      LowerSemicontinuous
        (weakFiniteGridRiskSum (μ := μ) P target) :=
    lowerSemicontinuous_weakFiniteGridRiskSum
      (μ := μ) hPμ target
  exact
    hlsc.lowerSemicontinuousOn C
      |>.exists_isMinOn hCne hCcompact

/-- A finite-grid risk-sum minimizer is weakly Pareto efficient among all
clipped rules: no clipped competitor has strictly lower risk at every
grid point. -/
theorem weakHilbertFiniteGrid_minimizer_pareto
    {P : ι → Measure X} (target : ι → ℝ)
    (d₀ dF : WeakSpace ℝ (Lp ℝ 2 μ))
    (hdF :
      dF ∈ weakHilbertFiniteGridFeasibleSet
        (μ := μ) P target d₀)
    (hmin :
      IsMinOn
        (weakFiniteGridRiskSum (μ := μ) P target)
        (weakHilbertFiniteGridFeasibleSet
          (μ := μ) P target d₀)
        dF) :
    ∀ e ∈ weakHilbertActionSet μ,
      ¬ ∀ i,
        weakLpSquaredRisk (P i) (target i) e
          < weakLpSquaredRisk (P i) (target i) dF := by
  intro e he hstrict
  have heFeasible :
      e ∈ weakHilbertFiniteGridFeasibleSet
        (μ := μ) P target d₀ := by
    change
      e ∈ weakHilbertActionSet μ ∩
        ⋂ i,
          {f |
            weakLpSquaredRisk (P i) (target i) f
              ≤ weakLpSquaredRisk (P i) (target i) d₀}
    refine ⟨he, ?_⟩
    refine mem_iInter.mpr fun i => ?_
    exact
      (hstrict i).le.trans
        (mem_iInter.mp hdF.2 i)
  have hsumlt :
      weakFiniteGridRiskSum (μ := μ) P target e
        <
      weakFiniteGridRiskSum (μ := μ) P target dF := by
    unfold weakFiniteGridRiskSum
    exact ENNReal.sum_lt_sum_of_nonempty
      Finset.univ_nonempty
      (fun i _ => hstrict i)
  exact (not_lt_of_ge (hmin heFeasible)) hsumlt

/-- Combined finite-grid output: a feasible Pareto minimizer exists. -/
theorem exists_weakHilbertFiniteGrid_pareto
    {P : ι → Measure X} (hPμ : ∀ i, P i ≪ μ)
    (target : ι → ℝ)
    (d₀ : WeakSpace ℝ (Lp ℝ 2 μ))
    (hd₀ : d₀ ∈ weakHilbertActionSet μ) :
    ∃ dF,
      dF ∈ weakHilbertFiniteGridFeasibleSet
        (μ := μ) P target d₀ ∧
      ∀ e ∈ weakHilbertActionSet μ,
        ¬ ∀ i,
          weakLpSquaredRisk (P i) (target i) e
            < weakLpSquaredRisk (P i) (target i) dF := by
  obtain ⟨dF, hdF, hmin⟩ :=
    exists_weakHilbertFiniteGrid_minimizer
      (μ := μ) hPμ target d₀ hd₀
  exact
    ⟨dF, hdF,
      weakHilbertFiniteGrid_minimizer_pareto
        (μ := μ) target d₀ dF hdF hmin⟩

end

end GraybillDeal
