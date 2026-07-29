import GraybillDeal.UniversalFiniteBayes
import GraybillDeal.UniversalPosteriorIdentity
import GraybillDeal.UniversalWeakLimit

/-!
# Finite posterior actions and their weak limits

This module identifies the elementary finite weighted mean from
`UniversalFiniteBayes` with the posterior-action integral from
`UniversalReducedKernel`.  It then proves the fixed-coordinate limiting
step used by the universal limiting-Bayes argument.

No complete-class or admissibility principle is assumed here.
-/

namespace GraybillDeal

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Integration against an explicitly finite prior is the corresponding
finite weighted sum. -/
theorem UniversalFinitePrior.integral_toProbabilityMeasure
    (π : UniversalFinitePrior) (f : UniversalTheta → ℝ) :
    ∫ θ, f θ ∂(π.toProbabilityMeasure : Measure UniversalTheta)
      =
    ∑ i, (π.weight i : ℝ) * f (π.point i) := by
  rw [UniversalFinitePrior.toProbabilityMeasure_toMeasure]
  rw [integral_finsetSum_measure]
  · simp [NNReal.smul_def]
  · intro i hi
    exact (integrable_dirac (by simp)).smul_measure (by simp)

/-- The finite-prior posterior action: posterior weights are prior mass
times the universal likelihood kernel, and the target is the parameter
coordinate `θ`. -/
def universalFinitePriorPosteriorAction
    (π : UniversalFinitePrior) (a b r q : ℝ) : ℝ :=
  finiteWeightedMean Finset.univ
    (fun i =>
      (π.weight i : ℝ) *
        universalKernel a b r q (π.point i))
    (fun i => (π.point i : ℝ))

theorem universalPosteriorDenominator_finitePrior
    (π : UniversalFinitePrior) (a b r q : ℝ) :
    universalPosteriorDenominator
        (π.toProbabilityMeasure : Measure UniversalTheta) a b r q
      =
    ∑ i, (π.weight i : ℝ) *
      universalKernel a b r q (π.point i) := by
  exact π.integral_toProbabilityMeasure
    (fun θ => universalKernel a b r q θ)

theorem universalPosteriorNumerator_finitePrior
    (π : UniversalFinitePrior) (a b r q : ℝ) :
    universalPosteriorNumerator
        (π.toProbabilityMeasure : Measure UniversalTheta) a b r q
      =
    ∑ i, ((π.weight i : ℝ) *
      universalKernel a b r q (π.point i)) * (π.point i : ℝ) := by
  rw [universalPosteriorNumerator]
  rw [π.integral_toProbabilityMeasure]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The explicit finite weighted mean is exactly the integral-ratio
posterior action of the probability measure represented by the prior. -/
theorem universalFinitePriorPosteriorAction_eq_universalPosteriorAction
    (π : UniversalFinitePrior) (a b r q : ℝ) :
    universalFinitePriorPosteriorAction π a b r q
      =
    universalPosteriorAction
      (π.toProbabilityMeasure : Measure UniversalTheta) a b r q := by
  unfold universalFinitePriorPosteriorAction
    finiteWeightedMean finiteWeightTotal universalPosteriorAction
  rw [universalPosteriorNumerator_finitePrior,
    universalPosteriorDenominator_finitePrior]

/-- Fixed-coordinate limiting-Bayes step.

If finite priors converge weakly along a subsequence and their explicit
posterior weighted means converge to the observation coordinate `r`,
then the posterior action of the weak limit is exactly `r`.
-/
theorem universalPosteriorAction_eq_of_finitePrior_tendsto
    {πs : ℕ → UniversalFinitePrior}
    {φ : ℕ → ℕ}
    {ν : ProbabilityMeasure UniversalTheta}
    {a b r q : ℝ}
    (hν :
      Tendsto
        ((fun n => (πs n).toProbabilityMeasure) ∘ φ)
        atTop (𝓝 ν))
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q)
    (haction :
      Tendsto
        (fun j =>
          universalFinitePriorPosteriorAction
            (πs (φ j)) a b r q)
        atTop (𝓝 r)) :
    universalPosteriorAction
        (ν : Measure UniversalTheta) a b r q = r := by
  have hnum :=
    tendsto_universalPosteriorNumerator
      hν ha hb hr0 hr1 hq
  have hden :=
    tendsto_universalPosteriorDenominator
      hν ha hb hr0 hr1 hq
  have hden_ne :
      universalPosteriorDenominator
        (ν : Measure UniversalTheta) a b r q ≠ 0 :=
    ne_of_gt
      (universalPosteriorDenominator_pos
        (ν : Measure UniversalTheta) ha hb hr0 hr1 hq)
  have hratio :
      Tendsto
        (fun j =>
          universalPosteriorNumerator
              ((πs (φ j)).toProbabilityMeasure :
                Measure UniversalTheta)
              a b r q
            /
          universalPosteriorDenominator
              ((πs (φ j)).toProbabilityMeasure :
                Measure UniversalTheta)
              a b r q)
        atTop
        (𝓝
          (universalPosteriorAction
            (ν : Measure UniversalTheta) a b r q)) := by
    unfold universalPosteriorAction
    refine (hnum.div hden hden_ne).congr'
      (Eventually.of_forall fun j => ?_)
    rfl
  have hfinite :
      Tendsto
        (fun j =>
          universalFinitePriorPosteriorAction
            (πs (φ j)) a b r q)
        atTop
        (𝓝
          (universalPosteriorAction
            (ν : Measure UniversalTheta) a b r q)) := by
    convert hratio using 1
    funext j
    exact
      universalFinitePriorPosteriorAction_eq_universalPosteriorAction
        (πs (φ j)) a b r q
  exact tendsto_nhds_unique hfinite haction

/-- A sequence-level packaged version.  Compactness supplies a weakly
convergent subsequence, and convergence of the original finite posterior
actions forces the limiting posterior identity along that subsequence. -/
theorem exists_universalFinitePrior_subseq_posteriorAction_eq
    (πs : ℕ → UniversalFinitePrior)
    {a b r q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q)
    (haction :
      Tendsto
        (fun n =>
          universalFinitePriorPosteriorAction
            (πs n) a b r q)
        atTop (𝓝 r)) :
    ∃ (ν : ProbabilityMeasure UniversalTheta) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto
        ((fun n => (πs n).toProbabilityMeasure) ∘ φ)
        atTop (𝓝 ν) ∧
      universalPosteriorAction
        (ν : Measure UniversalTheta) a b r q = r := by
  obtain ⟨ν, φ, hφ, hν⟩ :=
    exists_universalFinitePrior_tendsto_subseq πs
  refine ⟨ν, φ, hφ, hν, ?_⟩
  apply universalPosteriorAction_eq_of_finitePrior_tendsto
    hν ha hb hr0 hr1 hq
  simpa only [Function.comp_def] using
    haction.comp hφ.tendsto_atTop

/-- Global limiting-Bayes package.

If one sequence of finite-prior posterior actions converges to the
Graybill--Deal action `r` at every legal reduced observation, compactness
produces a *single* limiting probability measure whose posterior action is
identically `r`.  The subsequence is chosen before the observation
coordinates are introduced, so no diagonal argument is needed here.
-/
theorem exists_universalPosteriorIdentity_of_finitePrior_tendsto
    (πs : ℕ → UniversalFinitePrior)
    {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (haction :
      ∀ r q : ℝ, 0 < r → r < 1 → 0 ≤ q →
        Tendsto
          (fun n =>
            universalFinitePriorPosteriorAction
              (πs n) a b r q)
          atTop (𝓝 r)) :
    ∃ ν : ProbabilityMeasure UniversalTheta,
      UniversalPosteriorIdentity
        (ν : Measure UniversalTheta) a b := by
  obtain ⟨ν, φ, hφ, hν⟩ :=
    exists_universalFinitePrior_tendsto_subseq πs
  refine ⟨ν, ⟨?_⟩⟩
  intro r q hr0 hr1 hq
  apply universalPosteriorAction_eq_of_finitePrior_tendsto
    hν ha hb hr0 hr1 hq
  simpa only [Function.comp_def] using
    (haction r q hr0 hr1 hq).comp hφ.tendsto_atTop

end

end GraybillDeal
