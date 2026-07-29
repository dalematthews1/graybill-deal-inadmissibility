import GraybillDeal.UniversalMeasurableDecision
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite-prior Bayes risk under squared loss

This file connects the algebraic posterior mean from
`UniversalFiniteBayes` with ordinary integrated Bayes risk.  For an
explicitly positive finite prior and an everywhere-positive likelihood:

* the posterior total is strictly positive at every observation;
* the posterior mean is the unique pointwise minimizer;
* posterior squared loss has an exact Pythagorean decomposition;
* after integration, the same decomposition gives weak and strict Bayes
  optimality under explicit integrability assumptions.

These are reusable prerequisites for the Brown/Lehmann--Casella
finite-support approximation theorem.  They do not assert that theorem.
-/

namespace GraybillDeal

open MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

variable {Θ X : Type*}

namespace PositiveFinitePrior

/-- Total unnormalized posterior mass at an observation. -/
def posteriorTotal
    (π : PositiveFinitePrior Θ)
    (density : Θ → X → ℝ) (x : X) : ℝ :=
  finiteWeightTotal Finset.univ (π.posteriorWeight density x)

theorem card_pos (π : PositiveFinitePrior Θ) :
    0 < π.card := by
  by_contra h
  have hcard : π.card = 0 := Nat.eq_zero_of_not_pos h
  have hempty : IsEmpty (Fin π.card) := by
    rw [hcard]
    infer_instance
  letI : IsEmpty (Fin π.card) := hempty
  have hsumzero : ∑ i, π.weight i = 0 := by simp
  have hcontra : (0 : NNReal) = 1 :=
    hsumzero.symm.trans π.weight_sum
  exact zero_ne_one hcontra

theorem posteriorWeight_pos
    (π : PositiveFinitePrior Θ)
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ x, 0 < density θ x)
    (x : X) (i : Fin π.card) :
    0 < π.posteriorWeight density x i := by
  unfold posteriorWeight
  exact mul_pos (by exact_mod_cast π.weight_pos i)
    (hdensity (π.point i) x)

theorem posteriorTotal_pos
    (π : PositiveFinitePrior Θ)
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ x, 0 < density θ x)
    (x : X) :
    0 < π.posteriorTotal density x := by
  unfold posteriorTotal
  apply Finset.sum_pos
  · intro i hi
    exact π.posteriorWeight_pos hdensity x i
  · exact Finset.univ_nonempty_iff.mpr
      ⟨⟨0, π.card_pos⟩⟩

/-- The finite posterior squared loss at one observation and action. -/
def posteriorSquaredLoss
    (π : PositiveFinitePrior Θ)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (x : X) (action : ℝ) : ℝ :=
  finiteWeightedSquaredLoss Finset.univ
    (π.posteriorWeight density x)
    (fun i => target (π.point i))
    action

theorem bayesAction_eq_finiteWeightedMean
    (π : PositiveFinitePrior Θ)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ) (x : X) :
    π.bayesAction density target x
      =
    finiteWeightedMean Finset.univ
      (π.posteriorWeight density x)
      (fun i => target (π.point i)) :=
  rfl

/-- Exact pointwise Pythagorean decomposition around the posterior mean. -/
theorem posteriorSquaredLoss_decomposition
    (π : PositiveFinitePrior Θ)
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ x, 0 < density θ x)
    (target : Θ → ℝ)
    (x : X) (action : ℝ) :
    π.posteriorSquaredLoss density target x action
      =
    π.posteriorSquaredLoss density target x
        (π.bayesAction density target x)
      + π.posteriorTotal density x
          * (action - π.bayesAction density target x) ^ 2 := by
  exact finite_weighted_squared_loss_decomposition
    Finset.univ
    (π.posteriorWeight density x)
    (fun i => target (π.point i))
    (ne_of_gt (π.posteriorTotal_pos hdensity x))
    action

theorem bayesAction_pointwise_minimizer
    (π : PositiveFinitePrior Θ)
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ x, 0 < density θ x)
    (target : Θ → ℝ)
    (x : X) (action : ℝ) :
    π.posteriorSquaredLoss density target x
        (π.bayesAction density target x)
      ≤
    π.posteriorSquaredLoss density target x action := by
  exact finiteWeightedMean_is_minimizer
    Finset.univ
    (π.posteriorWeight density x)
    (fun i => target (π.point i))
    (π.posteriorTotal_pos hdensity x)
    action

theorem bayesAction_pointwise_unique
    (π : PositiveFinitePrior Θ)
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ x, 0 < density θ x)
    (target : Θ → ℝ)
    (x : X) {action : ℝ}
    (haction : action ≠ π.bayesAction density target x) :
    π.posteriorSquaredLoss density target x
        (π.bayesAction density target x)
      <
    π.posteriorSquaredLoss density target x action := by
  exact finiteWeightedMean_unique_minimizer
    Finset.univ
    (π.posteriorWeight density x)
    (fun i => target (π.point i))
    (π.posteriorTotal_pos hdensity x)
    haction

/-- Integrated Bayes risk of a rule, written as the integral of finite
posterior squared loss. -/
def integratedSquaredRisk
    [MeasurableSpace X]
    (π : PositiveFinitePrior Θ)
    (m : Measure X)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (estimator : X → ℝ) : ℝ :=
  ∫ x, π.posteriorSquaredLoss density target x (estimator x) ∂m

/-- The nonnegative pointwise excess Bayes-risk integrand. -/
def integratedRiskGapIntegrand
    (π : PositiveFinitePrior Θ)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (estimator : X → ℝ) (x : X) : ℝ :=
  π.posteriorTotal density x
    * (estimator x - π.bayesAction density target x) ^ 2

theorem integratedSquaredRisk_decomposition
    [MeasurableSpace X]
    (π : PositiveFinitePrior Θ)
    (m : Measure X)
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ x, 0 < density θ x)
    (target : Θ → ℝ)
    (estimator : X → ℝ)
    (hbayes :
      Integrable
        (fun x =>
          π.posteriorSquaredLoss density target x
            (π.bayesAction density target x)) m)
    (hgap :
      Integrable
        (π.integratedRiskGapIntegrand density target estimator) m) :
    π.integratedSquaredRisk m density target estimator
      =
    π.integratedSquaredRisk m density target
        (π.bayesAction density target)
      + ∫ x,
          π.integratedRiskGapIntegrand density target estimator x ∂m := by
  unfold integratedSquaredRisk
  rw [← integral_add hbayes hgap]
  apply integral_congr_ae
  filter_upwards [] with x
  exact π.posteriorSquaredLoss_decomposition
    hdensity target x (estimator x)

theorem integratedSquaredRisk_bayes_le
    [MeasurableSpace X]
    (π : PositiveFinitePrior Θ)
    (m : Measure X)
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ x, 0 < density θ x)
    (target : Θ → ℝ)
    (estimator : X → ℝ)
    (hbayes :
      Integrable
        (fun x =>
          π.posteriorSquaredLoss density target x
            (π.bayesAction density target x)) m)
    (hgap :
      Integrable
        (π.integratedRiskGapIntegrand density target estimator) m) :
    π.integratedSquaredRisk m density target
        (π.bayesAction density target)
      ≤
    π.integratedSquaredRisk m density target estimator := by
  rw [π.integratedSquaredRisk_decomposition
    m hdensity target estimator hbayes hgap]
  exact le_add_of_nonneg_right
    (integral_nonneg fun x =>
      mul_nonneg (π.posteriorTotal_pos hdensity x).le
        (sq_nonneg _))

/-- Strict integrated Bayes optimality whenever the competing rule differs
from the posterior mean on a set of positive dominating measure. -/
theorem integratedSquaredRisk_bayes_lt
    [MeasurableSpace X]
    (π : PositiveFinitePrior Θ)
    (m : Measure X)
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ x, 0 < density θ x)
    (target : Θ → ℝ)
    (estimator : X → ℝ)
    (hbayes :
      Integrable
        (fun x =>
          π.posteriorSquaredLoss density target x
            (π.bayesAction density target x)) m)
    (hgap :
      Integrable
        (π.integratedRiskGapIntegrand density target estimator) m)
    (hdiff :
      0 < m {x |
        estimator x ≠ π.bayesAction density target x}) :
    π.integratedSquaredRisk m density target
        (π.bayesAction density target)
      <
    π.integratedSquaredRisk m density target estimator := by
  rw [π.integratedSquaredRisk_decomposition
    m hdensity target estimator hbayes hgap]
  apply lt_add_of_pos_right
  change 0 <
    ∫ x,
      π.posteriorTotal density x
        * (estimator x - π.bayesAction density target x) ^ 2 ∂m
  rw [integral_pos_iff_support_of_nonneg
    (fun x =>
      mul_nonneg (π.posteriorTotal_pos hdensity x).le
        (sq_nonneg _))
    hgap]
  have hsupp :
      Function.support
          (fun x =>
            π.posteriorTotal density x
              * (estimator x - π.bayesAction density target x) ^ 2)
        =
      {x | estimator x ≠ π.bayesAction density target x} := by
    ext x
    simp only [Function.mem_support, mem_setOf_eq]
    constructor
    · intro h
      by_contra heq
      apply h
      rw [heq, sub_self, zero_pow (by norm_num), mul_zero]
    · intro h
      exact mul_ne_zero
        (ne_of_gt (π.posteriorTotal_pos hdensity x))
        (pow_ne_zero 2 (sub_ne_zero.mpr h))
  rw [hsupp]
  exact hdiff

end PositiveFinitePrior

end

end GraybillDeal
