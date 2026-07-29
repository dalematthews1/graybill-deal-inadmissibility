import GraybillDeal.Elementary
import GraybillDeal.UniversalFinitePriorRisk
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Compact-action reductions for the universal decision problem

For the universal Graybill--Deal experiment the parameter of interest lies
in `(0,1)`, while decision rules are initially allowed to take arbitrary
real values.  This file records the two elementary reductions needed by a
compact-action complete-class argument.

* Every positive finite-prior posterior mean lies in the closed convex
  hull `[0,1]` of the target values.
* Projecting an arbitrary rule onto `[0,1]` weakly decreases its
  `ENNReal`-valued squared-error risk at every parameter.

There is also a strict version of the clipping result.  It applies when
the likelihood is everywhere positive, the original risk is finite, and
the rule leaves `[0,1]` on a set of positive reference-measure mass.
-/

namespace GraybillDeal

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

variable {Θ X : Type*}

namespace PositiveFinitePrior

/-- A positive finite-prior posterior mean belongs to every closed interval
containing all target values. -/
theorem bayesAction_mem_Icc
    (π : PositiveFinitePrior Θ)
    {density : Θ → X → ℝ}
    (hdensity : ∀ θ x, 0 < density θ x)
    (target : Θ → ℝ)
    {lower upper : ℝ}
    (htarget : ∀ θ, target θ ∈ Icc lower upper)
    (x : X) :
    π.bayesAction density target x ∈ Icc lower upper := by
  have htotal :
      0 <
        ∑ i : Fin π.card,
          (π.weight i : ℝ) * density (π.point i) x := by
    simpa [posteriorTotal, finiteWeightTotal, posteriorWeight] using
      π.posteriorTotal_pos hdensity x
  rw [π.bayesAction_eq_ratio]
  constructor
  · rw [le_div_iff₀ htotal]
    calc
      lower *
            ∑ i : Fin π.card,
              (π.weight i : ℝ) * density (π.point i) x
          =
        ∑ i : Fin π.card,
          lower * ((π.weight i : ℝ) * density (π.point i) x) := by
            rw [Finset.mul_sum]
      _ ≤
        ∑ i : Fin π.card,
          ((π.weight i : ℝ) * density (π.point i) x)
            * target (π.point i) := by
              apply Finset.sum_le_sum
              intro i hi
              calc
                lower *
                      ((π.weight i : ℝ) * density (π.point i) x)
                    =
                  ((π.weight i : ℝ) * density (π.point i) x) *
                    lower := by ring
                _ ≤
                  ((π.weight i : ℝ) * density (π.point i) x) *
                    target (π.point i) :=
                  mul_le_mul_of_nonneg_left
                    (htarget (π.point i)).1
                    (le_of_lt (π.posteriorWeight_pos hdensity x i))
  · rw [div_le_iff₀ htotal]
    calc
      (∑ i : Fin π.card,
          (π.weight i : ℝ) * density (π.point i) x
            * target (π.point i))
          ≤
        ∑ i : Fin π.card,
          ((π.weight i : ℝ) * density (π.point i) x) * upper := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_left
              (htarget (π.point i)).2
              (le_of_lt (π.posteriorWeight_pos hdensity x i))
      _ =
        upper *
          ∑ i : Fin π.card,
            (π.weight i : ℝ) * density (π.point i) x := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring

/-- In the universal open-parameter experiment, every positive
finite-prior Bayes action takes values in `[0,1]`. -/
theorem bayesAction_universalInterior_mem_Icc
    (π : PositiveFinitePrior UniversalInteriorTheta)
    {density : UniversalInteriorTheta → X → ℝ}
    (hdensity : ∀ θ x, 0 < density θ x)
    (x : X) :
    π.bayesAction density (fun θ => (θ : ℝ)) x ∈ Icc (0 : ℝ) 1 := by
  exact π.bayesAction_mem_Icc hdensity
    (fun θ : UniversalInteriorTheta => (θ : ℝ))
    (fun θ => ⟨θ.property.1.le, θ.property.2.le⟩) x

end PositiveFinitePrior

/-- Clipping preserves measurability of a real-valued decision rule. -/
theorem Measurable.clip01
    [MeasurableSpace X]
    {estimator : X → ℝ}
    (hestimator : Measurable estimator) :
    Measurable (fun x => clip01 (estimator x)) := by
  change Measurable (fun x => min (1 : ℝ) (max 0 (estimator x)))
  exact measurable_const.min (measurable_const.max hestimator)

/-- Clipping is strictly closer to an interior target whenever the
unclipped action lies outside `[0,1]`. -/
theorem clip01_sq_sub_lt_sq_sub
    {action target : ℝ}
    (htarget : target ∈ Ioo (0 : ℝ) 1)
    (haction : action ∉ Icc (0 : ℝ) 1) :
    (clip01 action - target) ^ 2 < (action - target) ^ 2 := by
  by_cases hneg : action < 0
  · rw [clip01_of_nonpos hneg.le]
    have hprod : 0 < (-action) * (2 * target - action) :=
      mul_pos (neg_pos.mpr hneg) (by linarith [htarget.1])
    nlinarith
  · have hnonneg : 0 ≤ action := le_of_not_gt hneg
    have hone : 1 < action := by
      by_contra hnot
      exact haction ⟨hnonneg, le_of_not_gt hnot⟩
    rw [clip01_of_one_le hone.le]
    have hprod : 0 < (action - 1) * (action + 1 - 2 * target) :=
      mul_pos (by linarith) (by linarith [htarget.2])
    nlinarith

/-- Pointwise projection onto `[0,1]` weakly decreases dominated
`ENNReal` squared-error risk whenever all targets lie in `[0,1]`.

No measurability or integrability hypothesis is needed for this weak
comparison because `lintegral_mono` applies directly to the nonnegative
integrands. -/
theorem densitySquaredRisk_clip01_le
    [MeasurableSpace X]
    (m : Measure X)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (htarget : ∀ θ, target θ ∈ Icc (0 : ℝ) 1)
    (estimator : X → ℝ)
    (θ : Θ) :
    densitySquaredRisk m density target
        (fun x => clip01 (estimator x)) θ
      ≤
    densitySquaredRisk m density target estimator θ := by
  unfold densitySquaredRisk
  apply lintegral_mono
  intro x
  exact mul_le_mul_left'
    (ENNReal.ofReal_le_ofReal
      (clip01_sq_sub_le_sq_sub
        (estimator x) (target θ) (htarget θ)))
    (ENNReal.ofReal (density θ x))

/-- A normalized likelihood makes the squared risk of the constant-zero
rule finite.  No integrability convention is involved: the risk is an
`ENNReal` lintegral and the constant loss factor pulls out exactly. -/
theorem densitySquaredRisk_const_zero_ne_top_of_normalized
    [MeasurableSpace X]
    (m : Measure X)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (θ : Θ)
    (hnormalized :
      (∫⁻ x, ENNReal.ofReal (density θ x) ∂m) = 1) :
    densitySquaredRisk m density target
        (fun _ : X => (0 : ℝ)) θ ≠ ⊤ := by
  unfold densitySquaredRisk
  rw [lintegral_mul_const'
    (ENNReal.ofReal (((0 : ℝ) - target θ) ^ 2))
    (fun x => ENNReal.ofReal (density θ x))
    ENNReal.ofReal_ne_top]
  simpa [hnormalized] using
    (ENNReal.ofReal_ne_top :
      ENNReal.ofReal (((0 : ℝ) - target θ) ^ 2) ≠ ⊤)

/-- In a nonempty normalized experiment, every measurably admissible
rule has finite risk at at least one parameter.  Otherwise the measurable
constant-zero rule has finite, hence strictly smaller, risk at any chosen
parameter and weakly smaller risk everywhere else. -/
theorem exists_densitySquaredRisk_ne_top_of_measurablyAdmissible
    [MeasurableSpace X]
    [Nonempty Θ]
    (m : Measure X)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (hnormalized :
      ∀ θ, (∫⁻ x, ENNReal.ofReal (density θ x) ∂m) = 1)
    {estimator : X → ℝ}
    (hadmissible :
      IsMeasurablyAdmissibleDensitySquared
        m density target estimator) :
    ∃ θ,
      densitySquaredRisk m density target estimator θ ≠ ⊤ := by
  by_contra hno
  have hall :
      ∀ θ, densitySquaredRisk m density target estimator θ = ⊤ := by
    intro θ
    by_contra hne
    exact hno ⟨θ, hne⟩
  let θ₀ : Θ := Classical.choice inferInstance
  have hzero_finite :
      densitySquaredRisk m density target
          (fun _ : X => (0 : ℝ)) θ₀ ≠ ⊤ :=
    densitySquaredRisk_const_zero_ne_top_of_normalized
      m density target θ₀ (hnormalized θ₀)
  apply hadmissible.2
  refine ⟨fun _ : X => (0 : ℝ), measurable_const, ?_⟩
  refine ⟨?_, ⟨θ₀, ?_⟩⟩
  · intro θ
    rw [hall θ]
    exact le_top
  · rw [hall θ₀]
    exact lt_top_iff_ne_top.mpr hzero_finite

/-- Strict clipping improvement at one parameter.

The strictness premise is precisely that the estimator leaves `[0,1]` on
a set of positive reference-measure mass.  Everywhere positivity of the
likelihood transfers that reference-measure strictness to the risk
integrand.  Finiteness of the original risk rules out the `∞ < ∞`
obstruction. -/
theorem densitySquaredRisk_clip01_lt
    [MeasurableSpace X]
    (m : Measure X)
    {density : Θ → X → ℝ}
    (hdensity_measurable : ∀ θ, Measurable (density θ))
    (hdensity_pos : ∀ θ x, 0 < density θ x)
    (target : Θ → ℝ)
    (htarget : ∀ θ, target θ ∈ Ioo (0 : ℝ) 1)
    {estimator : X → ℝ}
    (hestimator : Measurable estimator)
    (θ : Θ)
    (hfinite :
      densitySquaredRisk m density target estimator θ ≠ ⊤)
    (houtside :
      m {x | estimator x ∉ Icc (0 : ℝ) 1} ≠ 0) :
    densitySquaredRisk m density target
        (fun x => clip01 (estimator x)) θ
      <
    densitySquaredRisk m density target estimator θ := by
  let clipped : X → ℝ := fun x => clip01 (estimator x)
  let f : X → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (density θ x)
      * ENNReal.ofReal ((clipped x - target θ) ^ 2)
  let g : X → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (density θ x)
      * ENNReal.ofReal ((estimator x - target θ) ^ 2)
  have hle :
      densitySquaredRisk m density target clipped θ
        ≤ densitySquaredRisk m density target estimator θ := by
    exact densitySquaredRisk_clip01_le m density target
      (fun η => ⟨(htarget η).1.le, (htarget η).2.le⟩) estimator θ
  have hf_ne_top :
      (∫⁻ x, f x ∂m) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hfinite
    simpa [densitySquaredRisk, clipped, f] using hle
  have hg_measurable : Measurable g := by
    dsimp [g]
    exact
      (hdensity_measurable θ).ennreal_ofReal.mul
        ((hestimator.sub measurable_const).pow_const 2).ennreal_ofReal
  have hfg : ∀ᵐ x ∂m, f x ≤ g x := by
    filter_upwards [] with x
    dsimp [f, g, clipped]
    exact mul_le_mul_left'
        (ENNReal.ofReal_le_ofReal
        (clip01_sq_sub_le_sq_sub
          (estimator x) (target θ)
          ⟨(htarget θ).1.le, (htarget θ).2.le⟩))
      (ENNReal.ofReal (density θ x))
  have hstrict :
      ∀ᵐ x ∂m,
        x ∈ {x | estimator x ∉ Icc (0 : ℝ) 1} →
          f x < g x := by
    filter_upwards [] with x hx
    have hreal :
        (clip01 (estimator x) - target θ) ^ 2
          < (estimator x - target θ) ^ 2 :=
      clip01_sq_sub_lt_sq_sub (htarget θ) hx
    have haction_ne : estimator x ≠ target θ := by
      intro heq
      apply hx
      rw [heq]
      exact ⟨(htarget θ).1.le, (htarget θ).2.le⟩
    have hsquare_pos : 0 < (estimator x - target θ) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr haction_ne)
    have hofReal :
        ENNReal.ofReal
            ((clip01 (estimator x) - target θ) ^ 2)
          <
        ENNReal.ofReal ((estimator x - target θ) ^ 2) :=
      (ENNReal.ofReal_lt_ofReal_iff hsquare_pos).2 hreal
    dsimp [f, g, clipped]
    simpa only [mul_comm] using
      (ENNReal.mul_lt_mul_left
        (ne_of_gt ((ENNReal.ofReal_pos).2 (hdensity_pos θ x)))
        ENNReal.ofReal_ne_top hofReal)
  have hlt :
      (∫⁻ x, f x ∂m) < ∫⁻ x, g x ∂m :=
    lintegral_strict_mono_of_ae_le_of_ae_lt_on
      hg_measurable.aemeasurable hf_ne_top hfg houtside hstrict
  simpa [densitySquaredRisk, clipped, f, g] using hlt

/-- If an estimator leaves `[0,1]` on a set of positive reference-measure
mass and has finite risk at one parameter, then its measurable clipping
strictly dominates it. -/
theorem measurableDensitySquaredRiskDominates_clip01
    [MeasurableSpace X]
    (m : Measure X)
    {density : Θ → X → ℝ}
    (hdensity_measurable : ∀ θ, Measurable (density θ))
    (hdensity_pos : ∀ θ x, 0 < density θ x)
    (target : Θ → ℝ)
    (htarget : ∀ θ, target θ ∈ Ioo (0 : ℝ) 1)
    {estimator : X → ℝ}
    (hestimator : Measurable estimator)
    (θ₀ : Θ)
    (hfinite :
      densitySquaredRisk m density target estimator θ₀ ≠ ⊤)
    (houtside :
      m {x | estimator x ∉ Icc (0 : ℝ) 1} ≠ 0) :
    MeasurableDensitySquaredRiskDominates
      m density target
        (fun x => clip01 (estimator x)) estimator := by
  refine ⟨Measurable.clip01 hestimator, ?_⟩
  refine ⟨?_, ⟨θ₀, ?_⟩⟩
  · intro θ
    exact densitySquaredRisk_clip01_le
      m density target
        (fun η => ⟨(htarget η).1.le, (htarget η).2.le⟩)
        estimator θ
  · exact densitySquaredRisk_clip01_lt
      m hdensity_measurable hdensity_pos target htarget
      hestimator θ₀ hfinite houtside

/-- A measurably admissible finite-risk rule is `[0,1]`-valued almost
everywhere.  This is the direct reduction from the original real action
space to the compact action interval. -/
theorem measure_outside_Icc_eq_zero_of_measurablyAdmissible
    [MeasurableSpace X]
    (m : Measure X)
    {density : Θ → X → ℝ}
    (hdensity_measurable : ∀ θ, Measurable (density θ))
    (hdensity_pos : ∀ θ x, 0 < density θ x)
    (target : Θ → ℝ)
    (htarget : ∀ θ, target θ ∈ Ioo (0 : ℝ) 1)
    {estimator : X → ℝ}
    (hadmissible :
      IsMeasurablyAdmissibleDensitySquared
        m density target estimator)
    (θ₀ : Θ)
    (hfinite :
      densitySquaredRisk m density target estimator θ₀ ≠ ⊤) :
    m {x | estimator x ∉ Icc (0 : ℝ) 1} = 0 := by
  by_contra houtside
  exact hadmissible.2
    ⟨fun x => clip01 (estimator x),
      measurableDensitySquaredRiskDominates_clip01
        m hdensity_measurable hdensity_pos target htarget
        hadmissible.1 θ₀ hfinite houtside⟩

/-- Almost-everywhere formulation of
`measure_outside_Icc_eq_zero_of_measurablyAdmissible`. -/
theorem ae_mem_Icc_of_measurablyAdmissible
    [MeasurableSpace X]
    (m : Measure X)
    {density : Θ → X → ℝ}
    (hdensity_measurable : ∀ θ, Measurable (density θ))
    (hdensity_pos : ∀ θ x, 0 < density θ x)
    (target : Θ → ℝ)
    (htarget : ∀ θ, target θ ∈ Ioo (0 : ℝ) 1)
    {estimator : X → ℝ}
    (hadmissible :
      IsMeasurablyAdmissibleDensitySquared
        m density target estimator)
    (θ₀ : Θ)
    (hfinite :
      densitySquaredRisk m density target estimator θ₀ ≠ ⊤) :
    ∀ᵐ x ∂m, estimator x ∈ Icc (0 : ℝ) 1 := by
  rw [ae_iff]
  exact measure_outside_Icc_eq_zero_of_measurablyAdmissible
    m hdensity_measurable hdensity_pos target htarget
    hadmissible θ₀ hfinite

/-- Compact-action reduction with no separate finite-risk premise.
Likelihood normalization supplies that premise automatically in every
nonempty experiment. -/
theorem ae_mem_Icc_of_measurablyAdmissible_of_normalized
    [MeasurableSpace X]
    [Nonempty Θ]
    (m : Measure X)
    {density : Θ → X → ℝ}
    (hdensity_measurable : ∀ θ, Measurable (density θ))
    (hdensity_pos : ∀ θ x, 0 < density θ x)
    (hnormalized :
      ∀ θ, (∫⁻ x, ENNReal.ofReal (density θ x) ∂m) = 1)
    (target : Θ → ℝ)
    (htarget : ∀ θ, target θ ∈ Ioo (0 : ℝ) 1)
    {estimator : X → ℝ}
    (hadmissible :
      IsMeasurablyAdmissibleDensitySquared
        m density target estimator) :
    ∀ᵐ x ∂m, estimator x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨θ₀, hfinite⟩ :=
    exists_densitySquaredRisk_ne_top_of_measurablyAdmissible
      m density target hnormalized hadmissible
  exact ae_mem_Icc_of_measurablyAdmissible
    m hdensity_measurable hdensity_pos target htarget
    hadmissible θ₀ hfinite

end

end GraybillDeal
