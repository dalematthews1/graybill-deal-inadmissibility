import GraybillDeal.UniversalFiniteBayes
import GraybillDeal.UniversalWeakLimit
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Decision-theoretic interface for the universal argument

This module fixes the precise statement that has to be supplied by the
specialized complete-class theorem.  It deliberately contains no
complete-class axiom: `FiniteBayesCompleteClassProperty` is an ordinary
proposition, and downstream partial results may take a proof of it as an
explicit hypothesis until the Lehmann--Casella approximation theorem has
itself been formalized.

Risks take values in `ℝ≥0∞`.  This avoids the undesirable convention that
the Bochner integral of a nonintegrable real function is zero.
-/

namespace GraybillDeal

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section

variable {Θ X : Type*}

/-- Squared-error risk in an experiment dominated by `m`, expressed
directly through its density. -/
def densitySquaredRisk
    [MeasurableSpace X]
    (m : Measure X) (density : Θ → X → ℝ)
    (target : Θ → ℝ) (estimator : X → ℝ) (θ : Θ) : ℝ≥0∞ :=
  ∫⁻ x,
    ENNReal.ofReal (density θ x)
      * ENNReal.ofReal ((estimator x - target θ) ^ 2) ∂m

/-- `candidate` dominates `baseline` when its risk is nowhere larger and
is strictly smaller at at least one parameter value. -/
def DensitySquaredRiskDominates
    [MeasurableSpace X]
    (m : Measure X) (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (candidate baseline : X → ℝ) : Prop :=
  (∀ θ, densitySquaredRisk m density target candidate θ
      ≤ densitySquaredRisk m density target baseline θ)
    ∧
  ∃ θ, densitySquaredRisk m density target candidate θ
      < densitySquaredRisk m density target baseline θ

/-- Admissibility among all real-valued estimators for the dominated
squared-loss experiment. -/
def IsAdmissibleDensitySquared
    [MeasurableSpace X]
    (m : Measure X) (density : Θ → X → ℝ)
    (target : Θ → ℝ) (estimator : X → ℝ) : Prop :=
  ¬ ∃ candidate : X → ℝ,
      DensitySquaredRiskDominates
        m density target candidate estimator

theorem not_admissible_of_dominator
    [MeasurableSpace X]
    {m : Measure X} {density : Θ → X → ℝ}
    {target : Θ → ℝ} {estimator candidate : X → ℝ}
    (hdom :
      DensitySquaredRiskDominates
        m density target candidate estimator) :
    ¬ IsAdmissibleDensitySquared m density target estimator := by
  intro hadm
  exact hadm ⟨candidate, hdom⟩

namespace UniversalFinitePrior

/-- The unnormalized posterior weight at an observation. -/
def posteriorWeight
    (π : UniversalFinitePrior)
    (density : UniversalTheta → X → ℝ) (x : X)
    (i : Fin π.card) : ℝ :=
  (π.weight i : ℝ) * density (π.point i) x

/-- The finite-prior Bayes action under squared loss.  Positivity of the
posterior total is stated separately wherever the action is used. -/
def bayesAction
    (π : UniversalFinitePrior)
    (density : UniversalTheta → X → ℝ)
    (target : UniversalTheta → ℝ) (x : X) : ℝ :=
  finiteWeightedMean Finset.univ
    (π.posteriorWeight density x) (fun i => target (π.point i))

theorem bayesAction_eq_ratio
    (π : UniversalFinitePrior)
    (density : UniversalTheta → X → ℝ)
    (target : UniversalTheta → ℝ) (x : X) :
    π.bayesAction density target x
      =
    (∑ i, (π.weight i : ℝ) * density (π.point i) x
          * target (π.point i))
      / ∑ i, (π.weight i : ℝ) * density (π.point i) x := by
  unfold bayesAction posteriorWeight finiteWeightedMean finiteWeightTotal
  rfl

end UniversalFinitePrior

/-- The exact approximation conclusion used in the universal
limiting-Bayes argument. -/
def HasFiniteBayesApproximation
    [MeasurableSpace X]
    (m : Measure X) (density : UniversalTheta → X → ℝ)
    (target : UniversalTheta → ℝ) (estimator : X → ℝ) : Prop :=
  ∃ priors : ℕ → UniversalFinitePrior,
    ∀ᵐ x ∂m,
      Tendsto
        (fun j => (priors j).bayesAction density target x)
        atTop (𝓝 (estimator x))

/-- A project-specific statement of the finite-prior complete-class
property.  Proving this proposition from regularity assumptions is the
formal counterpart of the Lehmann--Casella theorem used on paper. -/
def FiniteBayesCompleteClassProperty
    [MeasurableSpace X]
    (m : Measure X) (density : UniversalTheta → X → ℝ)
    (target : UniversalTheta → ℝ) : Prop :=
  ∀ estimator : X → ℝ,
    IsAdmissibleDensitySquared m density target estimator →
      HasFiniteBayesApproximation m density target estimator

theorem hasFiniteBayesApproximation_of_admissible
    [MeasurableSpace X]
    {m : Measure X}
    {density : UniversalTheta → X → ℝ}
    {target : UniversalTheta → ℝ}
    (hcomplete :
      FiniteBayesCompleteClassProperty m density target)
    {estimator : X → ℝ}
    (hadmissible :
      IsAdmissibleDensitySquared m density target estimator) :
    HasFiniteBayesApproximation m density target estimator :=
  hcomplete estimator hadmissible

end

end GraybillDeal
