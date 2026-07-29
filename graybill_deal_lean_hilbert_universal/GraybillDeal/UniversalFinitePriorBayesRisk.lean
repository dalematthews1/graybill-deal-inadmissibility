import GraybillDeal.UniversalFinitePriorRisk

/-!
# Bayes-risk decomposition for a positive finite prior

This file records the exact continuous-sample-space calculation behind the
finite-prior part of a squared-loss complete-class argument.  The parameter
prior is finite, but the dominated sample space is an arbitrary measurable
space.

The principal identity is

```
BayesRisk(δ)
  = BayesRisk(δπ)
    + ∫ x, posteriorTotal(x) * (δ(x) - δπ(x))² ∂m,
```

where `δπ` is the finite posterior mean.  All interchanges of finite sums
and integrals are made under explicit componentwise integrability
hypotheses.  Positivity of the posterior denominator is required only
almost everywhere.  Consequently equality of finite Bayes risks forces a
measurable competitor to equal `δπ` almost everywhere.

This is a reusable finite-prior lemma.  It is not a continuous
complete-class or Brown separation theorem.
-/

namespace GraybillDeal

open MeasureTheory Set
open scoped BigOperators

noncomputable section

variable {Θ X : Type*}

namespace PositiveFinitePrior

/-- Frequentist squared risk at one parameter value, as a finite real
Bochner integral.  Statements using this definition therefore carry
integrability hypotheses explicitly. -/
def parameterSquaredRisk
    [MeasurableSpace X]
    (m : Measure X) (density : Θ → X → ℝ)
    (target : Θ → ℝ) (estimator : X → ℝ) (θ : Θ) : ℝ :=
  ∫ x, density θ x * (estimator x - target θ) ^ 2 ∂m

/-- Bayes risk obtained by averaging the parameterwise real squared risks
over an explicitly positive finite prior. -/
def finitePriorBayesRisk
    [MeasurableSpace X]
    (π : PositiveFinitePrior Θ)
    (m : Measure X) (density : Θ → X → ℝ)
    (target : Θ → ℝ) (estimator : X → ℝ) : ℝ :=
  ∑ i, (π.weight i : ℝ) *
    parameterSquaredRisk m density target estimator (π.point i)

/-- The posterior denominator is measurable whenever every likelihood
section is measurable. -/
theorem measurable_posteriorTotal
    [MeasurableSpace X]
    (π : PositiveFinitePrior Θ)
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ, Measurable (density θ)) :
    Measurable (π.posteriorTotal density) := by
  unfold posteriorTotal posteriorWeight finiteWeightTotal
  fun_prop

/-- The finite posterior mean is a measurable rule whenever every
likelihood section is measurable.  Division is total in Lean, so this
statement does not require denominator positivity. -/
theorem measurable_bayesAction_of_measurable_density
    [MeasurableSpace X]
    (π : PositiveFinitePrior Θ)
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ, Measurable (density θ))
    (target : Θ → ℝ) :
    Measurable (π.bayesAction density target) := by
  unfold bayesAction posteriorWeight finiteWeightedMean finiteWeightTotal
  fun_prop

/-- Integrability of each likelihood-weighted squared-loss component
implies integrability of the finite posterior squared loss. -/
theorem integrable_posteriorSquaredLoss
    [MeasurableSpace X]
    (π : PositiveFinitePrior Θ)
    (m : Measure X)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (estimator : X → ℝ)
    (hcomponent :
      ∀ i : Fin π.card,
        Integrable
          (fun x =>
            density (π.point i) x
              * (estimator x - target (π.point i)) ^ 2) m) :
    Integrable
      (fun x =>
        π.posteriorSquaredLoss density target x (estimator x)) m := by
  unfold posteriorSquaredLoss finiteWeightedSquaredLoss posteriorWeight
  apply integrable_finsetSum
  intro i hi
  simpa only [mul_assoc] using
    (hcomponent i).const_mul (π.weight i : ℝ)

/-- Interchanging the finite prior sum and the sample-space integral
identifies the prior-weighted parameter risks with integrated posterior
squared loss. -/
theorem finitePriorBayesRisk_eq_integratedSquaredRisk
    [MeasurableSpace X]
    (π : PositiveFinitePrior Θ)
    (m : Measure X)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (estimator : X → ℝ)
    (hcomponent :
      ∀ i : Fin π.card,
        Integrable
          (fun x =>
            density (π.point i) x
              * (estimator x - target (π.point i)) ^ 2) m) :
    π.finitePriorBayesRisk m density target estimator
      =
    π.integratedSquaredRisk m density target estimator := by
  unfold finitePriorBayesRisk parameterSquaredRisk integratedSquaredRisk
    posteriorSquaredLoss finiteWeightedSquaredLoss posteriorWeight
  calc
    (∑ i,
        (π.weight i : ℝ) *
          ∫ x,
            density (π.point i) x
              * (estimator x - target (π.point i)) ^ 2 ∂m)
        =
      ∑ i,
        ∫ x,
          (π.weight i : ℝ) *
            (density (π.point i) x
              * (estimator x - target (π.point i)) ^ 2) ∂m := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [integral_const_mul]
    _ =
      ∫ x,
        ∑ i,
          (π.weight i : ℝ) *
            (density (π.point i) x
              * (estimator x - target (π.point i)) ^ 2) ∂m := by
            rw [integral_finsetSum]
            intro i hi
            exact (hcomponent i).const_mul (π.weight i : ℝ)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Pointwise posterior Pythagorean identity under the weakest algebraic
condition: the posterior total is nonzero at this observation. -/
theorem posteriorSquaredLoss_decomposition_of_total_ne_zero
    (π : PositiveFinitePrior Θ)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (x : X)
    (htotal : π.posteriorTotal density x ≠ 0)
    (action : ℝ) :
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
    htotal action

/-- Almost-everywhere posterior Pythagorean identity. -/
theorem ae_posteriorSquaredLoss_decomposition
    [MeasurableSpace X]
    (π : PositiveFinitePrior Θ)
    (m : Measure X)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (estimator : X → ℝ)
    (htotal : ∀ᵐ x ∂m, 0 < π.posteriorTotal density x) :
    (fun x =>
      π.posteriorSquaredLoss density target x (estimator x))
      =ᵐ[m]
    (fun x =>
      π.posteriorSquaredLoss density target x
          (π.bayesAction density target x)
        + π.integratedRiskGapIntegrand density target estimator x) := by
  filter_upwards [htotal] with x hx
  exact π.posteriorSquaredLoss_decomposition_of_total_ne_zero
    density target x hx.ne' (estimator x)

/-- The gap integrand is integrable whenever both the competitor's and the
posterior mean's posterior squared-loss integrands are integrable. -/
theorem integrable_integratedRiskGapIntegrand
    [MeasurableSpace X]
    (π : PositiveFinitePrior Θ)
    (m : Measure X)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (estimator : X → ℝ)
    (htotal : ∀ᵐ x ∂m, 0 < π.posteriorTotal density x)
    (hestimator :
      Integrable
        (fun x =>
          π.posteriorSquaredLoss density target x (estimator x)) m)
    (hbayes :
      Integrable
        (fun x =>
          π.posteriorSquaredLoss density target x
            (π.bayesAction density target x)) m) :
    Integrable
      (π.integratedRiskGapIntegrand density target estimator) m := by
  have hae := π.ae_posteriorSquaredLoss_decomposition
    m density target estimator htotal
  have hdiff :
      (π.integratedRiskGapIntegrand density target estimator)
        =ᵐ[m]
      (fun x =>
        π.posteriorSquaredLoss density target x (estimator x)
          - π.posteriorSquaredLoss density target x
              (π.bayesAction density target x)) := by
    filter_upwards [hae] with x hx
    linarith
  exact (hestimator.sub hbayes).congr hdiff.symm

/-- Integrated Pythagorean decomposition, stated with only componentwise
integrability and almost-everywhere positivity of the posterior
denominator. -/
theorem finitePriorBayesRisk_decomposition
    [MeasurableSpace X]
    (π : PositiveFinitePrior Θ)
    (m : Measure X)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (estimator : X → ℝ)
    (htotal : ∀ᵐ x ∂m, 0 < π.posteriorTotal density x)
    (hcomponent :
      ∀ i : Fin π.card,
        Integrable
          (fun x =>
            density (π.point i) x
              * (estimator x - target (π.point i)) ^ 2) m)
    (hcomponent_bayes :
      ∀ i : Fin π.card,
        Integrable
          (fun x =>
            density (π.point i) x
              * (π.bayesAction density target x
                  - target (π.point i)) ^ 2) m) :
    π.finitePriorBayesRisk m density target estimator
      =
    π.finitePriorBayesRisk m density target
        (π.bayesAction density target)
      + ∫ x,
          π.integratedRiskGapIntegrand density target estimator x ∂m := by
  have hestimator :=
    π.integrable_posteriorSquaredLoss
      m density target estimator hcomponent
  have hbayes :=
    π.integrable_posteriorSquaredLoss
      m density target (π.bayesAction density target) hcomponent_bayes
  have hgap :=
    π.integrable_integratedRiskGapIntegrand
      m density target estimator htotal hestimator hbayes
  rw [π.finitePriorBayesRisk_eq_integratedSquaredRisk
    m density target estimator hcomponent]
  rw [π.finitePriorBayesRisk_eq_integratedSquaredRisk
    m density target (π.bayesAction density target) hcomponent_bayes]
  unfold integratedSquaredRisk
  rw [← integral_add hbayes hgap]
  exact integral_congr_ae
    (π.ae_posteriorSquaredLoss_decomposition
      m density target estimator htotal)

/-- The posterior mean minimizes finite-prior Bayes risk among competitors
for which the displayed real risks are finite. -/
theorem finitePriorBayesRisk_bayes_le
    [MeasurableSpace X]
    (π : PositiveFinitePrior Θ)
    (m : Measure X)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (estimator : X → ℝ)
    (htotal : ∀ᵐ x ∂m, 0 < π.posteriorTotal density x)
    (hcomponent :
      ∀ i : Fin π.card,
        Integrable
          (fun x =>
            density (π.point i) x
              * (estimator x - target (π.point i)) ^ 2) m)
    (hcomponent_bayes :
      ∀ i : Fin π.card,
        Integrable
          (fun x =>
            density (π.point i) x
              * (π.bayesAction density target x
                  - target (π.point i)) ^ 2) m) :
    π.finitePriorBayesRisk m density target
        (π.bayesAction density target)
      ≤
    π.finitePriorBayesRisk m density target estimator := by
  rw [π.finitePriorBayesRisk_decomposition
    m density target estimator htotal hcomponent hcomponent_bayes]
  apply le_add_of_nonneg_right
  apply integral_nonneg_of_ae
  filter_upwards [htotal] with x hx
  exact mul_nonneg hx.le (sq_nonneg _)

/-- Equality in the finite-prior Bayes-risk inequality forces a measurable
competitor to equal the posterior Bayes action almost everywhere. -/
theorem ae_eq_bayesAction_of_finitePriorBayesRisk_eq
    [MeasurableSpace X]
    (π : PositiveFinitePrior Θ)
    (m : Measure X)
    {density : Θ → X → ℝ}
    (_hdensity : ∀ θ, Measurable (density θ))
    (target : Θ → ℝ)
    (estimator : X → ℝ)
    (_hestimator : Measurable estimator)
    (htotal : ∀ᵐ x ∂m, 0 < π.posteriorTotal density x)
    (hcomponent :
      ∀ i : Fin π.card,
        Integrable
          (fun x =>
            density (π.point i) x
              * (estimator x - target (π.point i)) ^ 2) m)
    (hcomponent_bayes :
      ∀ i : Fin π.card,
        Integrable
          (fun x =>
            density (π.point i) x
              * (π.bayesAction density target x
                  - target (π.point i)) ^ 2) m)
    (hrisk :
      π.finitePriorBayesRisk m density target estimator
        =
      π.finitePriorBayesRisk m density target
        (π.bayesAction density target)) :
    estimator =ᵐ[m] π.bayesAction density target := by
  have hestimator_int :=
    π.integrable_posteriorSquaredLoss
      m density target estimator hcomponent
  have hbayes_int :=
    π.integrable_posteriorSquaredLoss
      m density target (π.bayesAction density target) hcomponent_bayes
  have hgap_int :=
    π.integrable_integratedRiskGapIntegrand
      m density target estimator htotal hestimator_int hbayes_int
  have hdecomp :=
    π.finitePriorBayesRisk_decomposition
      m density target estimator htotal hcomponent hcomponent_bayes
  have hgap_zero :
      (∫ x,
        π.integratedRiskGapIntegrand density target estimator x ∂m) = 0 := by
    linarith
  have hgap_nonneg :
      0 ≤ᵐ[m] π.integratedRiskGapIntegrand density target estimator := by
    filter_upwards [htotal] with x hx
    exact mul_nonneg hx.le (sq_nonneg _)
  have hgap_ae_zero :
      π.integratedRiskGapIntegrand density target estimator =ᵐ[m] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hgap_nonneg hgap_int).mp hgap_zero
  filter_upwards [htotal, hgap_ae_zero] with x hx hzero
  have hsq :
      (estimator x - π.bayesAction density target x) ^ 2 = 0 := by
    unfold integratedRiskGapIntegrand at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hx.ne'
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)

end PositiveFinitePrior

end

end GraybillDeal
