import GraybillDeal.UniversalCompleteClassExhaustion
import GraybillDeal.UniversalFiniteStatisticalRiskSet
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# A local risk-set closure criterion for the complete-class step

This file isolates a precise intermediate statement in the
Brown--Lehmann--Casella complete-class argument.

For a finite positive prior `π`, let its local gap at a measurable
finite-measure region `s` be

```
∫⁻ x in s, edist (π.bayesAction density target x) (estimator x) ∂m.
```

The one-dimensional set of all such gaps is the local-gap projection of
the finite-prior statistical risk set.  If zero belongs to its closure,
then Markov's inequality produces exactly the geometric bad-set estimate
needed by `UniversalCompleteClassExhaustion`.

`ClosedConvexLocalFiniteBayesRiskSet` packages the traditional output of
a local closed/convex risk-set argument: a closed convex set which is
exactly the closure of the attainable finite-prior local gaps and contains
zero.  The diagonal argument itself only needs the last two facts; the
closedness and convexity fields make explicit what remains to be proved by
the statistical separation/compactness argument.

This is not a proof of Brown's theorem.  It reduces that theorem to the
concrete, stagewise closed-risk-set statement and proves all subsequent
measure-theoretic steps.
-/

namespace GraybillDeal

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace CompleteClass

variable {X Θ : Type*} [MeasurableSpace X]
variable {m : Measure X}

/-- The local `L¹` extended-distance gap between a finite-prior Bayes rule
and a proposed limiting rule. -/
def localFiniteBayesEDistGap
    (m : Measure X) (s : Set X)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (estimator : X → ℝ)
    (π : PositiveFinitePrior Θ) : ℝ≥0∞ :=
  ∫⁻ x in s,
    edist
      (π.bayesAction density target x)
      (estimator x) ∂m

/-- The real-valued attainable local-gap set.  Finiteness of each
extended-real gap is kept as a separate hypothesis below. -/
def localFiniteBayesGapRange
    (m : Measure X) (s : Set X)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (estimator : X → ℝ) : Set ℝ :=
  Set.range fun π : PositiveFinitePrior Θ =>
    (localFiniteBayesEDistGap
      m s density target estimator π).toReal

/-- Explicit closed/convex local statistical risk-set hypothesis.

The set is the closed convex local-gap projection supplied by a putative
local risk-set theorem.  The equality with the closure of the attainable
finite-prior gaps is the substantive approximation/closure assertion.
The `gap_ne_top` field is the local finiteness needed to pass between
`ℝ≥0∞` and `ℝ`.
-/
structure ClosedConvexLocalFiniteBayesRiskSet
    (m : Measure X) (s : Set X)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (estimator : X → ℝ) where
  /-- The closed local risk-set projection. -/
  riskSet : Set ℝ
  /-- Local compactness/closure output. -/
  riskSet_closed : IsClosed riskSet
  /-- Mixtures give convexity of the statistical risk set. -/
  riskSet_convex : Convex ℝ riskSet
  /-- The risk set is exhausted by attainable finite-prior gaps. -/
  riskSet_eq_closure :
    riskSet =
      closure
        (localFiniteBayesGapRange
          m s density target estimator)
  /-- The candidate rule is a zero-gap boundary point. -/
  zero_mem : 0 ∈ riskSet
  /-- Every attainable local gap is finite. -/
  gap_ne_top :
    ∀ π : PositiveFinitePrior Θ,
      localFiniteBayesEDistGap
        m s density target estimator π ≠ ∞

/-- The core closure assertion, without the traditional closedness and
convexity bookkeeping.  This is the weakest stagewise assumption consumed
by the Markov/diagonal part of the proof. -/
def HasZeroInLocalFiniteBayesGapClosure
    (m : Measure X) (s : Set X)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (estimator : X → ℝ) : Prop :=
  (∀ π : PositiveFinitePrior Θ,
      localFiniteBayesEDistGap
        m s density target estimator π ≠ ∞)
    ∧
  0 ∈ closure
    (localFiniteBayesGapRange
      m s density target estimator)

theorem ClosedConvexLocalFiniteBayesRiskSet.hasZeroInGapClosure
    {s : Set X}
    {density : Θ → X → ℝ}
    {target : Θ → ℝ}
    {estimator : X → ℝ}
    (h :
      ClosedConvexLocalFiniteBayesRiskSet
        m s density target estimator) :
    HasZeroInLocalFiniteBayesGapClosure
      m s density target estimator := by
  refine ⟨h.gap_ne_top, ?_⟩
  rw [← h.riskSet_eq_closure]
  exact h.zero_mem

/-- Zero in the closure of the attainable finite-prior gaps gives a prior
with arbitrarily small local gap. -/
theorem exists_positiveFinitePrior_localEDistGap_lt
    {s : Set X}
    {density : Θ → X → ℝ}
    {target : Θ → ℝ}
    {estimator : X → ℝ}
    (hclosure :
      HasZeroInLocalFiniteBayesGapClosure
        m s density target estimator)
    {η : ℝ≥0∞} (hη0 : η ≠ 0) (hηtop : η ≠ ∞) :
    ∃ π : PositiveFinitePrior Θ,
      localFiniteBayesEDistGap
        m s density target estimator π < η := by
  have hηreal : 0 < η.toReal :=
    ENNReal.toReal_pos hη0 hηtop
  obtain ⟨π, hπ⟩ :=
    (Metric.mem_closure_range_iff.mp hclosure.2)
      η.toReal hηreal
  have hgap_nonneg :
      0 ≤
        (localFiniteBayesEDistGap
          m s density target estimator π).toReal :=
    ENNReal.toReal_nonneg
  have hπreal :
      (localFiniteBayesEDistGap
        m s density target estimator π).toReal < η.toReal := by
    simpa [Real.dist_eq, abs_of_nonneg hgap_nonneg] using hπ
  refine ⟨π, ?_⟩
  rw [← ENNReal.ofReal_toReal (hclosure.1 π),
    ← ENNReal.ofReal_toReal hηtop]
  exact
    (ENNReal.ofReal_lt_ofReal_iff hηreal).2 hπreal

/-- Measurability of the local extended-distance integrand. -/
theorem measurable_bayesAction_edist
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ, Measurable (density θ))
    (target : Θ → ℝ)
    (estimator : X → ℝ)
    (hestimator : Measurable estimator)
    (π : PositiveFinitePrior Θ) :
    Measurable fun x =>
      edist
        (π.bayesAction density target x)
        (estimator x) := by
  exact
    (GraybillDeal.CompleteClass.PositiveFinitePrior.measurable_bayesAction
      π hdensity target).edist hestimator

/-- A local `L¹` gap at most `ε²` implies the exact `ε` bad-set bound
used by the exhaustion argument. -/
theorem measure_local_bayes_badSet_le
    {s : Set X} (hs : MeasurableSet s)
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ, Measurable (density θ))
    (target : Θ → ℝ)
    (estimator : X → ℝ)
    (hestimator : Measurable estimator)
    (π : PositiveFinitePrior Θ)
    {ε : ℝ≥0∞} (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞)
    (hgap :
      localFiniteBayesEDistGap
        m s density target estimator π ≤ ε * ε) :
    m (s ∩
      {x |
        ε ≤
          edist
            (π.bayesAction density target x)
            (estimator x)})
      ≤ ε := by
  let f : X → ℝ≥0∞ :=
    fun x =>
      edist
        (π.bayesAction density target x)
        (estimator x)
  have hf : Measurable f :=
    measurable_bayesAction_edist
      hdensity target estimator hestimator π
  have hmarkov :
      (m.restrict s) {x | ε ≤ f x}
        ≤
      (∫⁻ x, f x ∂(m.restrict s)) / ε :=
    meas_ge_le_lintegral_div
      hf.aemeasurable hε0 hεtop
  have hdiv :
      (∫⁻ x, f x ∂(m.restrict s)) / ε ≤ ε := by
    apply ENNReal.div_le_of_le_mul'
    simpa [localFiniteBayesEDistGap, f] using hgap
  calc
    m (s ∩ {x | ε ≤
        edist
          (π.bayesAction density target x)
          (estimator x)})
        =
      (m.restrict s) {x | ε ≤ f x} := by
        rw [Measure.restrict_apply' hs]
        simp only [f]
        rw [inter_comm]
    _ ≤ (∫⁻ x, f x ∂(m.restrict s)) / ε :=
      hmarkov
    _ ≤ ε := hdiv

/-- A zero-in-closure local risk-set certificate supplies one geometric
finite-Bayes approximant on the given stage. -/
theorem exists_positiveFinitePrior_geometric_badSet_bound
    {s : Set X} (hs : MeasurableSet s)
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ, Measurable (density θ))
    (target : Θ → ℝ)
    (estimator : X → ℝ)
    (hestimator : Measurable estimator)
    (n : ℕ)
    (hclosure :
      HasZeroInLocalFiniteBayesGapClosure
        m s density target estimator) :
    ∃ π : PositiveFinitePrior Θ,
      m (s ∩
        {x |
          diagonalAccuracy n ≤
            edist
              (π.bayesAction density target x)
              (estimator x)})
        ≤ diagonalAccuracy n := by
  have hε0 : diagonalAccuracy n ≠ 0 :=
    ne_of_gt (diagonalAccuracy_pos n)
  have hεtop : diagonalAccuracy n ≠ ∞ := by
    simp [diagonalAccuracy]
  have hεsq0 :
      diagonalAccuracy n * diagonalAccuracy n ≠ 0 :=
    mul_ne_zero hε0 hε0
  have hεsqtop :
      diagonalAccuracy n * diagonalAccuracy n ≠ ∞ :=
    ENNReal.mul_ne_top hεtop hεtop
  obtain ⟨π, hπ⟩ :=
    exists_positiveFinitePrior_localEDistGap_lt
      hclosure hεsq0 hεsqtop
  refine ⟨π, ?_⟩
  exact measure_local_bayes_badSet_le
    hs hdensity target estimator hestimator π
    hε0 hεtop hπ.le

/-- Stagewise closed/convex local risk-set hypothesis for every measurably
admissible rule. -/
def MeasurableClosedConvexLocalRiskSetProperty
    [SigmaFinite m]
    (density : Θ → X → ℝ)
    (target : Θ → ℝ) : Prop :=
  ∀ estimator : X → ℝ,
    IsMeasurablyAdmissibleDensitySquared
        m density target estimator →
      ∀ n,
        Nonempty
          (ClosedConvexLocalFiniteBayesRiskSet
            m
            ((FiniteMeasureExhaustion.spanningSets m).region n)
            density target estimator)

/-- The explicit closed/convex local risk-set hypotheses imply the
compatible local complete-class property used by the universal theorem.

All separation/compactness content is confined to
`MeasurableClosedConvexLocalRiskSetProperty`; after that hypothesis,
closure extraction plus Markov's inequality and the canonical
sigma-finite exhaustion are sufficient.
-/
theorem measurableCompatibleLocalCompleteClassProperty_of_closedConvexLocalRiskSets
    [SigmaFinite m]
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ, Measurable (density θ))
    (target : Θ → ℝ)
    (hrisk :
      MeasurableClosedConvexLocalRiskSetProperty
        (m := m) density target) :
    MeasurableCompatibleLocalCompleteClassProperty
      (m := m) density target := by
  intro estimator hadmissible n
  have hestimator : Measurable estimator :=
    hadmissible.1
  let E := FiniteMeasureExhaustion.spanningSets m
  obtain ⟨hcertificate⟩ :=
    hrisk estimator hadmissible n
  have hstage :=
    hcertificate.hasZeroInGapClosure
  exact exists_positiveFinitePrior_geometric_badSet_bound
    (E.measurable_region n)
    hdensity target estimator hestimator n hstage

/-- Consequently, the closed/convex local risk-set hypotheses imply the
global measurable finite-Bayes complete-class conclusion. -/
theorem measurablePositiveFiniteBayesCompleteClassProperty_of_closedConvexLocalRiskSets
    [SigmaFinite m]
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ, Measurable (density θ))
    (target : Θ → ℝ)
    (hrisk :
      MeasurableClosedConvexLocalRiskSetProperty
        (m := m) density target) :
    MeasurablePositiveFiniteBayesCompleteClassProperty
      m density target :=
  measurablePositiveFiniteBayesCompleteClassProperty_of_compatibleLocal
    (measurableCompatibleLocalCompleteClassProperty_of_closedConvexLocalRiskSets
      hdensity target hrisk)

end CompleteClass

end

end GraybillDeal
