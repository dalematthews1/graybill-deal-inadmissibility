import GraybillDeal.UniversalReducedKernel
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Sequences

/-!
# Weak limits of finite priors

This module supplies the compactness step in the universal limiting-Bayes
argument.  A finite prior is represented by finitely many points of the
compactified parameter interval and nonnegative weights summing to one.
It therefore determines a bundled probability measure on
`UniversalTheta`.

The space of probability measures on the compact metric space
`UniversalTheta` is itself compact and metrizable.  Consequently every
sequence of finite priors has a weakly convergent subsequence.  Weak
convergence then gives convergence of the denominator and numerator
integrals from `UniversalReducedKernel`.

There is no decision-theoretic assumption in this file.
-/

namespace GraybillDeal

open Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-- A probability measure with an explicitly finite presentation.

Repeated support points are allowed.  This keeps the representation
independent of a decidable equality on `UniversalTheta`; repeated points
simply combine their masses in `toProbabilityMeasure`.
-/
structure UniversalFinitePrior where
  /-- Number of entries in the finite presentation. -/
  card : ℕ
  /-- Parameter point at each entry. -/
  point : Fin card → UniversalTheta
  /-- Nonnegative mass at each entry. -/
  weight : Fin card → ℝ≥0
  /-- The masses sum to one. -/
  weight_sum : ∑ i, weight i = 1

namespace UniversalFinitePrior

/-- The probability measure represented by a finite prior. -/
def toProbabilityMeasure (π : UniversalFinitePrior) :
    ProbabilityMeasure UniversalTheta :=
  ⟨∑ i, (π.weight i : ℝ≥0∞) • Measure.dirac (π.point i), by
    constructor
    simpa using
      congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) π.weight_sum⟩

@[simp]
theorem toProbabilityMeasure_toMeasure (π : UniversalFinitePrior) :
    ((π.toProbabilityMeasure : ProbabilityMeasure UniversalTheta) :
      Measure UniversalTheta)
      =
    ∑ i, (π.weight i : ℝ≥0∞) • Measure.dirac (π.point i) :=
  rfl

end UniversalFinitePrior

/-- Every sequence of probability measures on `UniversalTheta` admits a
weakly convergent subsequence.

Weak convergence is the topology carried by `ProbabilityMeasure`, hence
is expressed by `Tendsto`.
-/
theorem exists_universalProbabilityMeasure_tendsto_subseq
    (νs : ℕ → ProbabilityMeasure UniversalTheta) :
    ∃ (ν : ProbabilityMeasure UniversalTheta) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (νs ∘ φ) atTop (𝓝 ν) :=
  CompactSpace.tendsto_subseq νs

/-- In particular, every sequence of explicitly finite priors admits a
weakly convergent subsequence, whose limit may place mass at either
endpoint of `UniversalTheta`. -/
theorem exists_universalFinitePrior_tendsto_subseq
    (πs : ℕ → UniversalFinitePrior) :
    ∃ (ν : ProbabilityMeasure UniversalTheta) (φ : ℕ → ℕ),
      StrictMono φ ∧
        Tendsto
          ((fun n => (πs n).toProbabilityMeasure) ∘ φ)
          atTop (𝓝 ν) :=
  exists_universalProbabilityMeasure_tendsto_subseq
    (fun n => (πs n).toProbabilityMeasure)

/-- Weak convergence of probability measures implies convergence of the
universal posterior denominator at every fixed interior `r` and
nonnegative `q`. -/
theorem tendsto_universalPosteriorDenominator
    {ι : Type*} {l : Filter ι}
    {νs : ι → ProbabilityMeasure UniversalTheta}
    {ν : ProbabilityMeasure UniversalTheta}
    (hν : Tendsto νs l (𝓝 ν))
    {a b r q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q) :
    Tendsto
      (fun i =>
        universalPosteriorDenominator
          (νs i : Measure UniversalTheta) a b r q)
      l
      (𝓝
        (universalPosteriorDenominator
          (ν : Measure UniversalTheta) a b r q)) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν)
      (universalKernelBCF ha hb hr0 hr1 hq)
  simpa [universalPosteriorDenominator, universalKernelBCF] using h

/-- Weak convergence of probability measures implies convergence of the
universal posterior numerator at every fixed interior `r` and
nonnegative `q`. -/
theorem tendsto_universalPosteriorNumerator
    {ι : Type*} {l : Filter ι}
    {νs : ι → ProbabilityMeasure UniversalTheta}
    {ν : ProbabilityMeasure UniversalTheta}
    (hν : Tendsto νs l (𝓝 ν))
    {a b r q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q) :
    Tendsto
      (fun i =>
        universalPosteriorNumerator
          (νs i : Measure UniversalTheta) a b r q)
      l
      (𝓝
        (universalPosteriorNumerator
          (ν : Measure UniversalTheta) a b r q)) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν)
      (universalNumeratorKernelBCF ha hb hr0 hr1 hq)
  simpa [universalPosteriorNumerator, universalNumeratorKernelBCF] using h

/-- A packaged form of the weak-limit step: for any fixed legal kernel
parameters, one subsequence simultaneously converges weakly and has
convergent denominator and numerator integrals. -/
theorem exists_universalFinitePrior_tendsto_subseq_integrals
    (πs : ℕ → UniversalFinitePrior)
    {a b r q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q) :
    ∃ (ν : ProbabilityMeasure UniversalTheta) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto
        ((fun n => (πs n).toProbabilityMeasure) ∘ φ)
        atTop (𝓝 ν) ∧
      Tendsto
        (fun j =>
          universalPosteriorDenominator
            (((πs (φ j)).toProbabilityMeasure :
              ProbabilityMeasure UniversalTheta) :
              Measure UniversalTheta)
            a b r q)
        atTop
        (𝓝
          (universalPosteriorDenominator
            (ν : Measure UniversalTheta) a b r q)) ∧
      Tendsto
        (fun j =>
          universalPosteriorNumerator
            (((πs (φ j)).toProbabilityMeasure :
              ProbabilityMeasure UniversalTheta) :
              Measure UniversalTheta)
            a b r q)
        atTop
        (𝓝
          (universalPosteriorNumerator
            (ν : Measure UniversalTheta) a b r q)) := by
  obtain ⟨ν, φ, hφ, hν⟩ :=
    exists_universalFinitePrior_tendsto_subseq πs
  refine ⟨ν, φ, hφ, hν, ?_, ?_⟩
  · exact tendsto_universalPosteriorDenominator
      hν ha hb hr0 hr1 hq
  · exact tendsto_universalPosteriorNumerator
      hν ha hb hr0 hr1 hq

end

end GraybillDeal
