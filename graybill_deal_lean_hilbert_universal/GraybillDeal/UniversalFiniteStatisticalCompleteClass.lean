import GraybillDeal.UniversalFiniteStatisticalRiskSet

/-!
# Exact finite-experiment complete-class theorem

The local Brown argument is genuinely topological only because its sample
and parameter spaces are infinite.  This file closes the corresponding
finite problem completely.

For a finite parameter space and a finite sample space with strictly
positive dominating masses and likelihoods, convex risk-set separation
produces a positive finite supporting prior.  The squared-loss
Pythagorean identity then forces the original admissible rule to equal
that prior's posterior mean at every sample point.

This theorem is a useful finite local model for the remaining universal
closed-risk-set step.  It does not assert that the continuous reduced
experiment is a finite experiment.
-/

namespace GraybillDeal

open scoped BigOperators NNReal

noncomputable section

namespace FiniteStatisticalRiskSet

variable {ι X : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype X] [DecidableEq X]

/-- Bayes risk of a rule under an explicitly positive finite prior in the
finite dominated experiment. -/
def finitePriorSquaredRisk
    (π : PositiveFinitePrior ι)
    (mass : X → ℝ)
    (density : ι → X → ℝ)
    (target : ι → ℝ)
    (estimator : X → ℝ) : ℝ :=
  ∑ j, (π.weight j : ℝ) *
    finiteSquaredRisk mass density target estimator (π.point j)

/-- Finite sums may be interchanged to express finite-prior risk as the
sum of posterior squared losses over the sample space. -/
theorem finitePriorSquaredRisk_eq_sum_posteriorSquaredLoss
    (π : PositiveFinitePrior ι)
    (mass : X → ℝ)
    (density : ι → X → ℝ)
    (target : ι → ℝ)
    (estimator : X → ℝ) :
    finitePriorSquaredRisk
        π mass density target estimator
      =
    ∑ x, mass x *
      π.posteriorSquaredLoss
        density target x (estimator x) := by
  unfold finitePriorSquaredRisk finiteSquaredRisk
    PositiveFinitePrior.posteriorSquaredLoss
    finiteWeightedSquaredLoss
    PositiveFinitePrior.posteriorWeight
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Exact finite-prior Pythagorean decomposition after summing over the
finite sample space. -/
theorem finitePriorSquaredRisk_decomposition
    (π : PositiveFinitePrior ι)
    (mass : X → ℝ)
    {density : ι → X → ℝ}
    (hdensity : ∀ i x, 0 < density i x)
    (target : ι → ℝ)
    (estimator : X → ℝ) :
    finitePriorSquaredRisk
        π mass density target estimator
      =
    finitePriorSquaredRisk
        π mass density target
          (π.bayesAction density target)
      +
    ∑ x, mass x * π.posteriorTotal density x
      * (estimator x -
          π.bayesAction density target x) ^ 2 := by
  rw [finitePriorSquaredRisk_eq_sum_posteriorSquaredLoss,
    finitePriorSquaredRisk_eq_sum_posteriorSquaredLoss]
  calc
    (∑ x, mass x *
        π.posteriorSquaredLoss density target x (estimator x))
        =
      ∑ x,
        (mass x *
            π.posteriorSquaredLoss density target x
              (π.bayesAction density target x)
          +
        mass x * π.posteriorTotal density x
          * (estimator x -
              π.bayesAction density target x) ^ 2) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [π.posteriorSquaredLoss_decomposition
              hdensity target x (estimator x)]
            ring
    _ =
      (∑ x, mass x *
        π.posteriorSquaredLoss density target x
          (π.bayesAction density target x))
      +
      ∑ x, mass x * π.posteriorTotal density x
        * (estimator x -
            π.bayesAction density target x) ^ 2 := by
          rw [Finset.sum_add_distrib]

/-- A rule which minimizes finite-prior risk must equal the posterior mean
at every sample point carrying positive dominating mass. -/
theorem eq_bayesAction_of_finitePrior_support
    (π : PositiveFinitePrior ι)
    {mass : X → ℝ}
    (hmass : ∀ x, 0 < mass x)
    {density : ι → X → ℝ}
    (hdensity : ∀ i x, 0 < density i x)
    (target : ι → ℝ)
    (estimator : X → ℝ)
    (hsupport :
      ∀ candidate : X → ℝ,
        finitePriorSquaredRisk
            π mass density target estimator
          ≤
        finitePriorSquaredRisk
            π mass density target candidate) :
    estimator = π.bayesAction density target := by
  let bayes := π.bayesAction density target
  have hdecomp :=
    finitePriorSquaredRisk_decomposition
      π mass hdensity target estimator
  have hsupport_bayes := hsupport bayes
  have hgap_nonneg :
      0 ≤
        ∑ x, mass x * π.posteriorTotal density x
          * (estimator x - bayes x) ^ 2 := by
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg
      (mul_nonneg (hmass x).le
        (π.posteriorTotal_pos hdensity x).le)
      (sq_nonneg _)
  have hgap_zero :
      (∑ x, mass x * π.posteriorTotal density x
          * (estimator x - bayes x) ^ 2) = 0 := by
    dsimp only [bayes] at hdecomp hsupport_bayes ⊢
    linarith
  funext x
  have hxzero :
      mass x * π.posteriorTotal density x
          * (estimator x - bayes x) ^ 2 = 0 := by
    have hall :=
      Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset X))
        (f := fun y =>
          mass y * π.posteriorTotal density y
            * (estimator y - bayes y) ^ 2)
        (fun y hy =>
          mul_nonneg
            (mul_nonneg (hmass y).le
              (π.posteriorTotal_pos hdensity y).le)
            (sq_nonneg _))
    exact (hall.mp hgap_zero) x (Finset.mem_univ x)
  have hcoef :
      mass x * π.posteriorTotal density x ≠ 0 :=
    ne_of_gt
      (mul_pos (hmass x)
        (π.posteriorTotal_pos hdensity x))
  have hsq :
      (estimator x - bayes x) ^ 2 = 0 :=
    (mul_eq_zero.mp hxzero).resolve_left hcoef
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)

/-- Exact finite statistical complete-class theorem.

Every admissible rule in a strictly positive finite dominated
squared-loss experiment is the posterior mean for an actual
`PositiveFinitePrior`.  Convex risk-set separation is supplied by
`exists_positiveFinitePrior_supporting_finite_admissible`; strict
convexity of squared loss turns supporting Bayes optimality into
pointwise equality.
-/
theorem exists_positiveFinitePrior_bayesAction_eq_of_finite_admissible
    {mass : X → ℝ}
    (hmass : ∀ x, 0 < mass x)
    {density : ι → X → ℝ}
    (hdensity : ∀ i x, 0 < density i x)
    (target : ι → ℝ)
    (estimator : X → ℝ)
    (hadmissible :
      IsFiniteSquaredRiskAdmissible
        mass density target estimator) :
    ∃ π : PositiveFinitePrior ι,
      estimator = π.bayesAction density target := by
  obtain ⟨π, hsupport⟩ :=
    exists_positiveFinitePrior_supporting_finite_admissible
      (fun x => (hmass x).le)
      (fun i x => (hdensity i x).le)
      target estimator hadmissible
  refine ⟨π, ?_⟩
  apply eq_bayesAction_of_finitePrior_support
    π hmass hdensity target estimator
  intro candidate
  simpa [finitePriorSquaredRisk] using hsupport candidate

end FiniteStatisticalRiskSet

end

end GraybillDeal
