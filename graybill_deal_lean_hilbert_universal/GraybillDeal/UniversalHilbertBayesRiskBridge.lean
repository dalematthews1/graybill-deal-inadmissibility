import GraybillDeal.UniversalFinitePriorBayesRisk
import GraybillDeal.UniversalHilbertFiniteGridBayes
import GraybillDeal.UniversalReducedRiskRebase
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# From Hilbert risk to finite-prior Bayes risk

The compact Hilbert layer integrates squared loss under a model probability
measure, while the existing finite-prior uniqueness theorem uses a real
integral of likelihood times squared loss under the dominating measure.
This file proves that these are exactly the same finite real risk.
-/

namespace GraybillDeal

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

noncomputable section

variable {Θ X : Type*} [MeasurableSpace X]
variable {μ m P : Measure X} [IsFiniteMeasure μ]

/-- The representative chosen by `Lp` is measurable, not merely
almost-everywhere measurable. -/
theorem measurable_weakHilbertRepresentative
    (f : WeakSpace ℝ (Lp ℝ 2 μ)) :
    Measurable
      (fun x =>
        ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x) :=
  (Lp.stronglyMeasurable
    ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f)).measurable

/-- A measurable `[0,1]`-valued rule defines an `L²` element for every
finite reference measure. -/
theorem memLp_two_of_ae_mem_Icc
    {estimator : X → ℝ}
    (hestimator : Measurable estimator)
    (hbounded :
      ∀ᵐ x ∂μ, estimator x ∈ Set.Icc (0 : ℝ) 1) :
    MemLp estimator 2 μ :=
  memLp_of_bounded hbounded
    hestimator.aestronglyMeasurable 2

/-- Package a measurable clipped rule as a point of the weak Hilbert
action subtype. -/
def weakHilbertActionOfMeasurable
    (estimator : X → ℝ)
    (hestimator : Measurable estimator)
    (hbounded :
      ∀ᵐ x ∂μ, estimator x ∈ Set.Icc (0 : ℝ) 1) :
    WeakHilbertAction μ := by
  let hmem : MemLp estimator 2 μ :=
    memLp_two_of_ae_mem_Icc hestimator hbounded
  let f : Lp ℝ 2 μ := hmem.toLp estimator
  refine
    ⟨toWeakSpace ℝ (Lp ℝ 2 μ) f, ?_⟩
  refine ⟨f, ?_, rfl⟩
  rw [mem_hilbertActionSet_iff_ae]
  filter_upwards [hmem.coeFn_toLp, hbounded]
    with x hfx hx
  rwa [hfx]

/-- The packaged Hilbert rule agrees almost everywhere with the original
measurable clipped rule. -/
theorem weakHilbertActionOfMeasurable_ae_eq
    (estimator : X → ℝ)
    (hestimator : Measurable estimator)
    (hbounded :
      ∀ᵐ x ∂μ, estimator x ∈ Set.Icc (0 : ℝ) 1) :
    (fun x =>
      ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm
        (weakHilbertActionOfMeasurable
          (μ := μ) estimator hestimator hbounded :
          WeakSpace ℝ (Lp ℝ 2 μ))) x)
      =ᵐ[μ]
    estimator := by
  exact MemLp.coeFn_toLp
    (memLp_two_of_ae_mem_Icc hestimator hbounded)

/-- Hilbert risk under a density-defined model measure is the project's
existing dominated extended-real risk of the same representative. -/
theorem weakLpSquaredRisk_eq_densitySquaredRisk
    (density : Θ → X → ℝ)
    (target : Θ → ℝ) (θ : Θ)
    (hdensity : Measurable (density θ))
    (hP :
      P = m.withDensity
        (fun x => ENNReal.ofReal (density θ x)))
    (f : WeakSpace ℝ (Lp ℝ 2 μ)) :
    weakLpSquaredRisk P (target θ) f
      =
    densitySquaredRisk m density target
      (fun x =>
        ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x)
      θ := by
  symm
  exact
    densitySquaredRisk_eq_lintegral_of_eq_withDensity
      hdensity
      (measurable_weakHilbertRepresentative f)
      hP

/-- Integrating squared loss under `m.withDensity (ofReal density)` equals
the real likelihood-weighted parameter risk under `m`. -/
theorem measureSquaredRisk_eq_parameterSquaredRisk_of_eq_withDensity
    (density : Θ → X → ℝ)
    (target : Θ → ℝ) (estimator : X → ℝ) (θ : Θ)
    (hdensity : Measurable (density θ))
    (hdensity_nonneg : ∀ x, 0 ≤ density θ x)
    (hP :
      P = m.withDensity
        (fun x => ENNReal.ofReal (density θ x))) :
    measureSquaredRisk P target estimator θ
      =
    PositiveFinitePrior.parameterSquaredRisk
      m density target estimator θ := by
  unfold measureSquaredRisk PositiveFinitePrior.parameterSquaredRisk
  rw [hP,
    integral_withDensity_eq_integral_toReal_smul
      hdensity.ennreal_ofReal
      (Filter.Eventually.of_forall
        fun x => ENNReal.ofReal_lt_top)
      (fun x => (estimator x - target θ) ^ 2)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (hdensity_nonneg x)]
  simp only [smul_eq_mul]

/-- On the clipped action set, finite real Hilbert risk is exactly the
real parameter risk used by `PositiveFinitePrior.finitePriorBayesRisk`. -/
theorem weakLpSquaredRiskReal_eq_parameterSquaredRisk
    (hPμ : P ≪ μ) [IsProbabilityMeasure P]
    (density : Θ → X → ℝ)
    (target : Θ → ℝ) (θ : Θ)
    (hdensity : Measurable (density θ))
    (hdensity_nonneg : ∀ x, 0 ≤ density θ x)
    (hP :
      P = m.withDensity
        (fun x => ENNReal.ofReal (density θ x)))
    (htarget : target θ ∈ Set.Icc (0 : ℝ) 1)
    {f : WeakSpace ℝ (Lp ℝ 2 μ)}
    (hf : f ∈ weakHilbertActionSet μ) :
    weakLpSquaredRiskReal P (target θ) f
      =
    PositiveFinitePrior.parameterSquaredRisk
      m density target
        (fun x =>
          ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x)
        θ := by
  have hriskEq :=
    weakLpSquaredRisk_eq_densitySquaredRisk
      (μ := μ) density target θ hdensity hP f
  have hfiniteWeak :
      weakLpSquaredRisk P (target θ) f ≠ ∞ :=
    weakLpSquaredRisk_ne_top_of_mem_action
      (μ := μ) hPμ htarget hf
  have hfiniteDensity :
      densitySquaredRisk m density target
          (fun x =>
            ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x)
          θ
        ≠ ∞ := by
    rwa [← hriskEq]
  have hmeasure :
      measureSquaredRisk P target
          (fun x =>
            ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x)
          θ
        =
      (densitySquaredRisk m density target
          (fun x =>
            ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x)
          θ).toReal :=
    measureSquaredRisk_eq_densitySquaredRisk_toReal
      hdensity
      (measurable_weakHilbertRepresentative f)
      hP hfiniteDensity
  calc
    weakLpSquaredRiskReal P (target θ) f
        =
      (densitySquaredRisk m density target
        (fun x =>
          ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x)
        θ).toReal := by
          unfold weakLpSquaredRiskReal
          rw [hriskEq]
    _ =
      measureSquaredRisk P target
        (fun x =>
          ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x)
        θ :=
      hmeasure.symm
    _ =
      PositiveFinitePrior.parameterSquaredRisk
        m density target
          (fun x =>
            ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x)
          θ :=
      measureSquaredRisk_eq_parameterSquaredRisk_of_eq_withDensity
        density target
        (fun x =>
          ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x)
        θ hdensity hdensity_nonneg hP

/-- Every likelihood-weighted squared-loss component of a clipped Hilbert
rule is integrable under the dominating measure. -/
theorem integrable_density_mul_squaredLoss_of_mem_action
    (hPμ : P ≪ μ) [IsProbabilityMeasure P]
    (density : Θ → X → ℝ)
    (target : Θ → ℝ) (θ : Θ)
    (hdensity : Measurable (density θ))
    (hdensity_nonneg : ∀ x, 0 ≤ density θ x)
    (hP :
      P = m.withDensity
        (fun x => ENNReal.ofReal (density θ x)))
    (htarget : target θ ∈ Set.Icc (0 : ℝ) 1)
    {f : WeakSpace ℝ (Lp ℝ 2 μ)}
    (hf : f ∈ weakHilbertActionSet μ) :
    Integrable
      (fun x =>
        density θ x *
          (((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x
            - target θ) ^ 2)
      m := by
  have hriskEq :=
    weakLpSquaredRisk_eq_densitySquaredRisk
      (μ := μ) density target θ hdensity hP f
  have hfiniteWeak :
      weakLpSquaredRisk P (target θ) f ≠ ∞ :=
    weakLpSquaredRisk_ne_top_of_mem_action
      (μ := μ) hPμ htarget hf
  have hfiniteDensity :
      densitySquaredRisk m density target
          (fun x =>
            ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x)
          θ
        ≠ ∞ := by
    rwa [← hriskEq]
  have hintP :
      Integrable
        (fun x =>
          (((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x
            - target θ) ^ 2)
        P :=
    integrable_squaredError_of_densitySquaredRisk_ne_top
      hdensity
      (measurable_weakHilbertRepresentative f)
      hP hfiniteDensity
  rw [hP] at hintP
  have hweighted :
      Integrable
        (fun x =>
          (ENNReal.ofReal (density θ x)).toReal •
            (((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x
              - target θ) ^ 2)
        m :=
    (integrable_withDensity_iff_integrable_smul'
      hdensity.ennreal_ofReal
      (Filter.Eventually.of_forall
        fun x => ENNReal.ofReal_lt_top)).mp hintP
  simpa only
      [ENNReal.toReal_ofReal (hdensity_nonneg _),
       smul_eq_mul] using hweighted

end

end GraybillDeal
