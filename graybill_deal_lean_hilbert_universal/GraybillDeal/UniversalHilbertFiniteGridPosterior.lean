import GraybillDeal.UniversalCompactAction
import GraybillDeal.UniversalHilbertBayesRiskBridge

/-!
# Finite-grid minimizers are posterior means

This module completes the finite-grid step of the Hilbert complete-class
argument.  Compact minimization and finite-dimensional separation produce a
clipped rule supported by a positive finite prior.  The finite-prior
Pythagorean identity then proves that the rule equals the corresponding
posterior mean almost everywhere.
-/

namespace GraybillDeal

open MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal Topology

noncomputable section

variable {X ι : Type*} [MeasurableSpace X]
variable {μ m : Measure X} [IsFiniteMeasure μ]
variable [Fintype ι] [Nonempty ι]

/-- A finite-grid compact minimizer can be represented by the posterior
mean of a positive finite prior on that grid, while retaining all of its
baseline risk bounds. -/
theorem exists_weakHilbertFiniteGrid_posterior
    {P : ι → Measure X}
    (hPμ : ∀ i, P i ≪ μ)
    (hPprob : ∀ i, IsProbabilityMeasure (P i))
    (hmμ : m ≪ μ)
    (density : ι → X → ℝ)
    (hdensity : ∀ i, Measurable (density i))
    (hdensity_pos : ∀ i x, 0 < density i x)
    (hP :
      ∀ i,
        P i = m.withDensity
          (fun x => ENNReal.ofReal (density i x)))
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
        (fun x =>
          ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm
            (dF : WeakSpace ℝ (Lp ℝ 2 μ))) x)
          =ᵐ[m]
        π.bayesAction density target := by
  classical
  obtain ⟨dF, hdFle, π, hsupport⟩ :=
    exists_positiveFinitePrior_supporting_weakHilbertGrid
      (μ := μ) hPμ hPprob target htarget d₀ hd₀
  let dEst : X → ℝ :=
    fun x =>
      ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm
        (dF : WeakSpace ℝ (Lp ℝ 2 μ))) x
  have hdEstMeas : Measurable dEst :=
    measurable_weakHilbertRepresentative
      (dF : WeakSpace ℝ (Lp ℝ 2 μ))
  let bayes : X → ℝ := π.bayesAction density target
  have hbayesMeas : Measurable bayes :=
    π.measurable_bayesAction_of_measurable_density
      hdensity target
  have hbayesBound :
      ∀ᵐ x ∂μ, bayes x ∈ Set.Icc (0 : ℝ) 1 :=
    Filter.Eventually.of_forall fun x =>
      π.bayesAction_mem_Icc
        hdensity_pos target htarget x
  let bH : WeakHilbertAction μ :=
    weakHilbertActionOfMeasurable
      bayes hbayesMeas hbayesBound
  have hbHrepμ :
      (fun x =>
        ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm
          (bH : WeakSpace ℝ (Lp ℝ 2 μ))) x)
        =ᵐ[μ]
      bayes :=
    weakHilbertActionOfMeasurable_ae_eq
      bayes hbayesMeas hbayesBound
  have hbHrepm :
      (fun x =>
        ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm
          (bH : WeakSpace ℝ (Lp ℝ 2 μ))) x)
        =ᵐ[m]
      bayes :=
    hmμ.ae_le hbHrepμ
  have hdRisk (i : ι) :
      weakLpSquaredRiskReal (P i) (target i)
          (dF : WeakSpace ℝ (Lp ℝ 2 μ))
        =
      PositiveFinitePrior.parameterSquaredRisk
        m density target dEst i := by
    letI : IsProbabilityMeasure (P i) := hPprob i
    exact
      weakLpSquaredRiskReal_eq_parameterSquaredRisk
        (μ := μ) (hPμ i) density target i
        (hdensity i) (fun x => (hdensity_pos i x).le)
        (hP i) (htarget i) dF.2
  have hbHRisk (i : ι) :
      weakLpSquaredRiskReal (P i) (target i)
          (bH : WeakSpace ℝ (Lp ℝ 2 μ))
        =
      PositiveFinitePrior.parameterSquaredRisk
        m density target bayes i := by
    letI : IsProbabilityMeasure (P i) := hPprob i
    calc
      weakLpSquaredRiskReal (P i) (target i)
          (bH : WeakSpace ℝ (Lp ℝ 2 μ))
          =
        PositiveFinitePrior.parameterSquaredRisk
          m density target
            (fun x =>
              ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm
                (bH : WeakSpace ℝ (Lp ℝ 2 μ))) x)
          i :=
        weakLpSquaredRiskReal_eq_parameterSquaredRisk
          (μ := μ) (hPμ i) density target i
          (hdensity i) (fun x => (hdensity_pos i x).le)
          (hP i) (htarget i) bH.2
      _ =
        PositiveFinitePrior.parameterSquaredRisk
          m density target bayes i := by
        unfold PositiveFinitePrior.parameterSquaredRisk
        apply integral_congr_ae
        filter_upwards [hbHrepm] with x hx
        rw [hx]
  have hsupportBayes := hsupport bH
  have hsupportReal :
      π.finitePriorBayesRisk m density target dEst
        ≤
      π.finitePriorBayesRisk m density target bayes := by
    unfold PositiveFinitePrior.finitePriorBayesRisk
    calc
      (∑ j, (π.weight j : ℝ) *
          PositiveFinitePrior.parameterSquaredRisk
            m density target dEst (π.point j))
          =
        ∑ j, (π.weight j : ℝ) *
          weakLpSquaredRiskReal
            (P (π.point j)) (target (π.point j))
            (dF : WeakSpace ℝ (Lp ℝ 2 μ)) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hdRisk (π.point j)]
      _ ≤
        ∑ j, (π.weight j : ℝ) *
          weakLpSquaredRiskReal
            (P (π.point j)) (target (π.point j))
            (bH : WeakSpace ℝ (Lp ℝ 2 μ)) :=
        hsupportBayes
      _ =
        ∑ j, (π.weight j : ℝ) *
          PositiveFinitePrior.parameterSquaredRisk
            m density target bayes (π.point j) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hbHRisk (π.point j)]
  have htotal :
      ∀ᵐ x ∂m, 0 < π.posteriorTotal density x :=
    Filter.Eventually.of_forall fun x =>
      π.posteriorTotal_pos hdensity_pos x
  have hdcomponent :
      ∀ j : Fin π.card,
        Integrable
          (fun x =>
            density (π.point j) x *
              (dEst x - target (π.point j)) ^ 2)
          m := by
    intro j
    letI : IsProbabilityMeasure (P (π.point j)) :=
      hPprob (π.point j)
    exact
      integrable_density_mul_squaredLoss_of_mem_action
        (μ := μ) (hPμ (π.point j))
        density target (π.point j)
        (hdensity (π.point j))
        (fun x => (hdensity_pos (π.point j) x).le)
        (hP (π.point j))
        (htarget (π.point j))
        dF.2
  have hbcomponent :
      ∀ j : Fin π.card,
        Integrable
          (fun x =>
            density (π.point j) x *
              (bayes x - target (π.point j)) ^ 2)
          m := by
    intro j
    letI : IsProbabilityMeasure (P (π.point j)) :=
      hPprob (π.point j)
    have hrepComponent :
        Integrable
          (fun x =>
            density (π.point j) x *
              (((toWeakSpace ℝ (Lp ℝ 2 μ)).symm
                    (bH : WeakSpace ℝ (Lp ℝ 2 μ))) x
                - target (π.point j)) ^ 2)
          m :=
      integrable_density_mul_squaredLoss_of_mem_action
        (μ := μ) (hPμ (π.point j))
        density target (π.point j)
        (hdensity (π.point j))
        (fun x => (hdensity_pos (π.point j) x).le)
        (hP (π.point j))
        (htarget (π.point j))
        bH.2
    apply hrepComponent.congr
    filter_upwards [hbHrepm] with x hx
    rw [hx]
  have hbayesLe :
      π.finitePriorBayesRisk m density target bayes
        ≤
      π.finitePriorBayesRisk m density target dEst :=
    π.finitePriorBayesRisk_bayes_le
      m density target dEst
      htotal hdcomponent hbcomponent
  have hriskEq :
      π.finitePriorBayesRisk m density target dEst
        =
      π.finitePriorBayesRisk m density target bayes :=
    le_antisymm hsupportReal hbayesLe
  have hae :
      dEst =ᵐ[m] bayes :=
    π.ae_eq_bayesAction_of_finitePriorBayesRisk_eq
      m hdensity target dEst hdEstMeas
      htotal hdcomponent hbcomponent hriskEq
  exact ⟨dF, hdFle, π, hae⟩

end

end GraybillDeal
