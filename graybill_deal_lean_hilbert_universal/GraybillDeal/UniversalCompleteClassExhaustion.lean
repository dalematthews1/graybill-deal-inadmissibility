import GraybillDeal.UniversalCompleteClassConvergence
import GraybillDeal.UniversalInteriorDecision
import GraybillDeal.UniversalMeasurableDecision
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Sigma-finite exhaustion and the complete-class diagonal step

This file isolates a purely measure-theoretic part of the
Brown--Lehmann--Casella limiting-Bayes argument.

* `FiniteMeasureExhaustion` is an increasing measurable exhaustion by
  sets of finite measure.
* Every sigma-finite measure has the canonical exhaustion by
  `MeasureTheory.spanningSets`.
* If, on the `n`th exhaustion set, one can choose an approximating rule
  whose probability of an error of size at least `2⁻ⁿ` is at most
  `2⁻ⁿ`, then the chosen diagonal sequence converges almost everywhere
  on the whole space.
* Specializing the approximating rules to posterior means of positive
  finite priors turns a compatible family of local finite-Bayes
  approximants into the global finite-Bayes sequence required by the
  complete-class conclusion.

The existence of the local finite priors is deliberately an explicit
ordinary proposition.  This file does not assume or postulate the hard
decision-theoretic separation construction.
-/

namespace GraybillDeal

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace CompleteClass

variable {X Θ : Type*} [MeasurableSpace X]
variable {m : Measure X}

/-- An increasing measurable exhaustion of `X` by finite-measure sets. -/
structure FiniteMeasureExhaustion (m : Measure X) where
  /-- The `n`th finite-measure region. -/
  region : ℕ → Set X
  /-- Each region is measurable. -/
  measurable_region : ∀ n, MeasurableSet (region n)
  /-- The regions are increasing. -/
  monotone_region : Monotone region
  /-- Every region has finite measure. -/
  measure_region_lt_top : ∀ n, m (region n) < ∞
  /-- The regions cover the whole sample space. -/
  iUnion_region : ⋃ n, region n = Set.univ

namespace FiniteMeasureExhaustion

/-- The canonical finite-measure exhaustion supplied by sigma-finiteness. -/
def spanningSets (m : Measure X) [SigmaFinite m] :
    FiniteMeasureExhaustion m where
  region := MeasureTheory.spanningSets m
  measurable_region := measurableSet_spanningSets m
  monotone_region := monotone_spanningSets m
  measure_region_lt_top := measure_spanningSets_lt_top m
  iUnion_region := iUnion_spanningSets m

/-- Every point eventually belongs to every later exhaustion region. -/
theorem eventually_mem_region
    (E : FiniteMeasureExhaustion m) (x : X) :
    ∀ᶠ n in atTop, x ∈ E.region n := by
  have hx : x ∈ ⋃ n, E.region n := by
    rw [E.iUnion_region]
    exact Set.mem_univ x
  rw [Set.mem_iUnion] at hx
  obtain ⟨k, hxk⟩ := hx
  exact eventually_atTop.2
    ⟨k, fun n hkn => E.monotone_region hkn hxk⟩

end FiniteMeasureExhaustion

/-- The geometric accuracy scale used in the diagonal argument. -/
def diagonalAccuracy (n : ℕ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ ^ n

theorem diagonalAccuracy_pos (n : ℕ) :
    0 < diagonalAccuracy n := by
  unfold diagonalAccuracy
  exact ENNReal.pow_pos
    (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) n

theorem diagonalAccuracy_tendsto_zero :
    Tendsto diagonalAccuracy atTop (𝓝 0) := by
  unfold diagonalAccuracy
  apply ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
  norm_num

theorem diagonalAccuracy_tsum_ne_top :
    (∑' n, diagonalAccuracy n) ≠ ∞ := by
  unfold diagonalAccuracy
  simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two,
    inv_inv] using (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ∞)

theorem PositiveFinitePrior.measurable_bayesAction
    (π : PositiveFinitePrior Θ)
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ, Measurable (density θ))
    (target : Θ → ℝ) :
    Measurable (π.bayesAction density target) := by
  change Measurable (fun x => π.bayesAction density target x)
  simp_rw [π.bayesAction_eq_ratio]
  apply Measurable.div
  · fun_prop
  · fun_prop

/-- A Borel--Cantelli diagonal lemma on an increasing exhaustion.

At stage `n`, only errors inside `E.region n` are counted.  Since every
point is eventually in these regions and the error thresholds tend to
zero, summability of the bad-set measures gives global almost-everywhere
convergence.
-/
theorem ae_tendsto_of_exhausting_badSets_summable
    (E : FiniteMeasureExhaustion m)
    {f : ℕ → X → ℝ} {g : X → ℝ}
    {ε : ℕ → ℝ≥0∞}
    (hε : Tendsto ε atTop (𝓝 0))
    (hsum :
      (∑' n,
        m (E.region n ∩
          {x | ε n ≤ edist (f n x) (g x)})) ≠ ∞) :
    ∀ᵐ x ∂m,
      Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  let bad : ℕ → Set X :=
    fun n =>
      E.region n ∩
        {x | ε n ≤ edist (f n x) (g x)}
  have hnotBad :
      ∀ᵐ x ∂m, ∀ᶠ n in atTop, x ∉ bad n := by
    apply ae_eventually_notMem
    simpa only [bad] using hsum
  filter_upwards [hnotBad] with x hxNotBad
  rw [EMetric.tendsto_atTop]
  intro δ hδ
  have hεlt : ∀ᶠ n in atTop, ε n < δ :=
    hε (Iio_mem_nhds hδ)
  have hall :
      ∀ᶠ n in atTop, edist (f n x) (g x) < δ := by
    filter_upwards
        [E.eventually_mem_region x, hxNotBad, hεlt]
        with n hxRegion hxNot hxεδ
    have hdist : edist (f n x) (g x) < ε n := by
      by_contra h
      have hle : ε n ≤ edist (f n x) (g x) :=
        le_of_not_gt h
      exact hxNot ⟨hxRegion, hle⟩
    exact hdist.trans hxεδ
  exact eventually_atTop.1 hall

/-- Concrete geometric version of
`ae_tendsto_of_exhausting_badSets_summable`. -/
theorem ae_tendsto_of_exhausting_geometric_badSet_bound
    (E : FiniteMeasureExhaustion m)
    {f : ℕ → X → ℝ} {g : X → ℝ}
    (hbad :
      ∀ n,
        m (E.region n ∩
          {x |
            diagonalAccuracy n ≤
              edist (f n x) (g x)})
          ≤ diagonalAccuracy n) :
    ∀ᵐ x ∂m,
      Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  apply ae_tendsto_of_exhausting_badSets_summable
    E diagonalAccuracy_tendsto_zero
  exact ne_top_of_le_ne_top
    diagonalAccuracy_tsum_ne_top
    (ENNReal.tsum_le_tsum hbad)

/-- The exact local hypothesis needed to diagonalize positive
finite-prior Bayes rules.

For every exhaustion stage, it asks for one positive finite prior whose
posterior mean misses `estimator` by at least `2⁻ⁿ` only on a set of
measure at most `2⁻ⁿ` inside the `n`th finite region.

This is an ordinary proposition.  Establishing it from admissibility is
the remaining Brown/Lehmann--Casella separation problem.
-/
def HasCompatibleLocalPositiveFiniteBayesApproximation
    (E : FiniteMeasureExhaustion m)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (estimator : X → ℝ) : Prop :=
  ∀ n, ∃ π : PositiveFinitePrior Θ,
    m (E.region n ∩
      {x |
        diagonalAccuracy n ≤
          edist
            (π.bayesAction density target x)
            (estimator x)})
      ≤ diagonalAccuracy n

/-- Compatible local positive finite-Bayes approximants yield one
global almost-everywhere convergent finite-Bayes sequence. -/
theorem hasPositiveFiniteBayesApproximation_of_compatibleLocal
    (E : FiniteMeasureExhaustion m)
    {density : Θ → X → ℝ}
    {target : Θ → ℝ}
    {estimator : X → ℝ}
    (hlocal :
      HasCompatibleLocalPositiveFiniteBayesApproximation
        E density target estimator) :
    HasPositiveFiniteBayesApproximation
      m density target estimator := by
  choose priors hpriors using hlocal
  refine ⟨priors, ?_⟩
  apply ae_tendsto_of_exhausting_geometric_badSet_bound E
  exact hpriors

/-- Sigma-finite specialization using Mathlib's canonical spanning
sets. -/
theorem hasPositiveFiniteBayesApproximation_of_sigmaFinite_compatibleLocal
    [SigmaFinite m]
    {density : Θ → X → ℝ}
    {target : Θ → ℝ}
    {estimator : X → ℝ}
    (hlocal :
      HasCompatibleLocalPositiveFiniteBayesApproximation
        (FiniteMeasureExhaustion.spanningSets m)
        density target estimator) :
    HasPositiveFiniteBayesApproximation
      m density target estimator :=
  hasPositiveFiniteBayesApproximation_of_compatibleLocal
    (FiniteMeasureExhaustion.spanningSets m) hlocal

/-- The remaining local Brown separation statement, packaged at the
complete-class level.

Unlike `MeasurablePositiveFiniteBayesCompleteClassProperty`, this asks
only for one approximation on each finite-measure exhaustion region.
The diagonal theorem above converts it into the global a.e. statement. -/
def MeasurableCompatibleLocalCompleteClassProperty
    [SigmaFinite m]
    (density : Θ → X → ℝ)
    (target : Θ → ℝ) : Prop :=
  ∀ estimator : X → ℝ,
    IsMeasurablyAdmissibleDensitySquared
        m density target estimator →
      HasCompatibleLocalPositiveFiniteBayesApproximation
        (FiniteMeasureExhaustion.spanningSets m)
        density target estimator

/-- The local exhaustion formulation implies the exact measurable
finite-Bayes complete-class property consumed by the universal
Graybill--Deal contradiction. -/
theorem measurablePositiveFiniteBayesCompleteClassProperty_of_compatibleLocal
    [SigmaFinite m]
    {density : Θ → X → ℝ}
    {target : Θ → ℝ}
    (hlocal :
      MeasurableCompatibleLocalCompleteClassProperty
        (m := m) density target) :
    MeasurablePositiveFiniteBayesCompleteClassProperty
      m density target := by
  intro estimator hadmissible
  exact
    hasPositiveFiniteBayesApproximation_of_sigmaFinite_compatibleLocal
      (hlocal estimator hadmissible)

end CompleteClass

end

end GraybillDeal
