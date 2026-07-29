import GraybillDeal.UniversalHilbertCanonicalIntersection
import GraybillDeal.UniversalHilbertStrictMidpoint
import GraybillDeal.UniversalCompactAction

/-!
# Admissibility identifies the global Hilbert dominator

The compact finite-intersection argument produces a clipped weak `L²`
rule whose risk is no larger than a baseline rule at every interior
parameter.  If the baseline is measurably admissible, the two `L²`
classes must coincide.

The proof uses the midpoint of the two rules.  Convexity gives weak risk
improvement at every parameter, while at the distinguished model
`P_{1/2} = μ` the Hilbert-space midpoint identity gives strict improvement
unless the classes are equal.
-/

namespace GraybillDeal

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Dominated squared risk is unchanged by altering a rule on a
reference-null set. -/
theorem densitySquaredRisk_congr_ae
    {Θ : Type*}
    (m : Measure X) (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    {estimator₁ estimator₂ : X → ℝ}
    (h : estimator₁ =ᵐ[m] estimator₂)
    (θ : Θ) :
    densitySquaredRisk m density target estimator₁ θ
      =
    densitySquaredRisk m density target estimator₂ θ := by
  unfold densitySquaredRisk
  apply lintegral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- A clipped global Hilbert dominator of a measurably admissible rule is
the same `L²` class as that rule. -/
theorem universalHilbert_dominator_eq_of_measurablyAdmissible
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    [IsFiniteMeasure
      (universalHilbertProbabilityMeasure ν₁ ν₂)]
    {estimator : UniversalReducedObservation → ℝ}
    {dstar d₀ :
      WeakSpace ℝ
        (Lp ℝ 2
          (universalHilbertProbabilityMeasure ν₁ ν₂))}
    (hdstar :
      dstar ∈ weakHilbertActionSet
        (universalHilbertProbabilityMeasure ν₁ ν₂))
    (hd₀ :
      d₀ ∈ weakHilbertActionSet
        (universalHilbertProbabilityMeasure ν₁ ν₂))
    (hd₀ae :
      (fun x =>
        ((toWeakSpace ℝ
            (Lp ℝ 2
              (universalHilbertProbabilityMeasure ν₁ ν₂))).symm
          d₀) x)
        =ᵐ[universalHilbertDominatingMeasure ν₁ ν₂]
      estimator)
    (hle :
      ∀ θ : UniversalInteriorTheta,
        weakLpSquaredRisk
            (universalHilbertModelMeasure ν₁ ν₂ θ)
            (θ : ℝ) dstar
          ≤
        weakLpSquaredRisk
            (universalHilbertModelMeasure ν₁ ν₂ θ)
            (θ : ℝ) d₀)
    (hadmissible :
      IsMeasurablyAdmissibleDensitySquared
        (universalHilbertDominatingMeasure ν₁ ν₂)
        (universalReducedLikelihood
          ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2))
        (fun θ : UniversalInteriorTheta => (θ : ℝ))
        estimator) :
    dstar = d₀ := by
  let μ := universalHilbertProbabilityMeasure ν₁ ν₂
  let ρ := universalHilbertDominatingMeasure ν₁ ν₂
  let density :=
    universalReducedLikelihood
      ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2)
  let target := fun θ : UniversalInteriorTheta => (θ : ℝ)
  let mid :
      WeakSpace ℝ (Lp ℝ 2 μ) :=
    (1 / 2 : ℝ) • dstar + (1 / 2 : ℝ) • d₀
  have hmid :
      mid ∈ weakHilbertActionSet μ := by
    exact convex_weakHilbertActionSet μ hdstar hd₀
      (by norm_num) (by norm_num) (by norm_num)
  have hmidle :
      ∀ θ : UniversalInteriorTheta,
        weakLpSquaredRisk
            (universalHilbertModelMeasure ν₁ ν₂ θ)
            (θ : ℝ) mid
          ≤
        weakLpSquaredRisk
            (universalHilbertModelMeasure ν₁ ν₂ θ)
            (θ : ℝ) d₀ := by
    intro θ
    letI :
        IsProbabilityMeasure
          (universalHilbertModelMeasure ν₁ ν₂ θ) :=
      isProbabilityMeasure_universalHilbertModelMeasure hν₁ hν₂ θ
    have htarget : (θ : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨θ.property.1.le, θ.property.2.le⟩
    have hstarReal :
        weakLpSquaredRiskReal
            (universalHilbertModelMeasure ν₁ ν₂ θ)
            (θ : ℝ) dstar
          ≤
        weakLpSquaredRiskReal
            (universalHilbertModelMeasure ν₁ ν₂ θ)
            (θ : ℝ) d₀ :=
      (weakLpSquaredRiskReal_le_iff
        (μ := μ)
        (universalHilbertModelMeasure_absolutelyContinuous_probability
          hν₁ hν₂ θ)
        htarget hdstar hd₀).2 (hle θ)
    let ds : WeakHilbertAction μ := ⟨dstar, hdstar⟩
    let d0s : WeakHilbertAction μ := ⟨d₀, hd₀⟩
    have hmix :=
      weakLpSquaredRiskReal_actionMix_le
        (μ := μ)
        (universalHilbertModelMeasure_absolutelyContinuous_probability
          hν₁ hν₂ θ)
        htarget
        (1 / 2 : ℝ) (1 / 2 : ℝ)
        (by norm_num) (by norm_num) (by norm_num)
        ds d0s
    rw [weakHilbertActionMix_coe
      (μ := μ)
      (1 / 2 : ℝ) (1 / 2 : ℝ)
      (by norm_num) (by norm_num) (by norm_num)
      ds d0s] at hmix
    have hmidReal :
        weakLpSquaredRiskReal
            (universalHilbertModelMeasure ν₁ ν₂ θ)
            (θ : ℝ) mid
          ≤
        weakLpSquaredRiskReal
            (universalHilbertModelMeasure ν₁ ν₂ θ)
            (θ : ℝ) d₀ := by
      dsimp [mid, ds, d0s] at hmix
      nlinarith
    exact
      (weakLpSquaredRiskReal_le_iff
        (μ := μ)
        (universalHilbertModelMeasure_absolutelyContinuous_probability
          hν₁ hν₂ θ)
        htarget hmid hd₀).1 hmidReal
  by_contra hne
  letI :
      IsProbabilityMeasure μ :=
    isProbabilityMeasure_universalHilbertProbabilityMeasure hν₁ hν₂
  have hanchor :
      weakLpSquaredRisk μ
          (universalHilbertTheta : ℝ) dstar
        ≤
      weakLpSquaredRisk μ
          (universalHilbertTheta : ℝ) d₀ := by
    simpa only [μ, universalHilbertProbabilityMeasure] using
      hle universalHilbertTheta
  have hanchorReal :
      weakLpSquaredRiskReal μ
          (universalHilbertTheta : ℝ) dstar
        ≤
      weakLpSquaredRiskReal μ
          (universalHilbertTheta : ℝ) d₀ :=
    (weakLpSquaredRiskReal_le_iff
      (μ := μ)
      Measure.AbsolutelyContinuous.rfl
      (by
        rw [universalHilbertTheta_coe]
        constructor <;> norm_num)
      hdstar hd₀).2 hanchor
  have hmidAnchorReal :
      weakLpSquaredRiskReal μ
          (universalHilbertTheta : ℝ) mid
        <
      weakLpSquaredRiskReal μ
          (universalHilbertTheta : ℝ) d₀ := by
    exact weakLpSquaredRiskReal_midpoint_lt_right
      dstar d₀ (universalHilbertTheta : ℝ) hne hanchorReal
  have hmidAnchor :
      weakLpSquaredRisk μ
          (universalHilbertTheta : ℝ) mid
        <
      weakLpSquaredRisk μ
          (universalHilbertTheta : ℝ) d₀ :=
    (weakLpSquaredRiskReal_lt_iff
      (μ := μ)
      Measure.AbsolutelyContinuous.rfl
      (by
        rw [universalHilbertTheta_coe]
        constructor <;> norm_num)
      hmid hd₀).1 hmidAnchorReal
  let midEstimator : UniversalReducedObservation → ℝ :=
    fun x =>
      ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm mid) x
  have hmidMeas : Measurable midEstimator :=
    measurable_weakHilbertRepresentative mid
  have ha : 0 < (ν₁ : ℝ) / 2 := by positivity
  have hb : 0 < (ν₂ : ℝ) / 2 := by positivity
  have hriskEq :
      ∀ (θ : UniversalInteriorTheta)
        (d : WeakSpace ℝ (Lp ℝ 2 μ)),
        weakLpSquaredRisk
            (universalHilbertModelMeasure ν₁ ν₂ θ)
            (θ : ℝ) d
          =
        densitySquaredRisk ρ density target
          (fun x =>
            ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm d) x)
          θ := by
    intro θ d
    exact weakLpSquaredRisk_eq_densitySquaredRisk
      (μ := μ) density target θ
      (measurable_universalReducedLikelihood_observation ha hb θ)
      rfl d
  have hdomle :
      ∀ θ : UniversalInteriorTheta,
        densitySquaredRisk ρ density target midEstimator θ
          ≤
        densitySquaredRisk ρ density target estimator θ := by
    intro θ
    rw [← densitySquaredRisk_congr_ae
      ρ density target hd₀ae θ]
    have hh := hmidle θ
    rw [hriskEq θ mid, hriskEq θ d₀] at hh
    simpa only [midEstimator] using hh
  have hdomstrict :
      densitySquaredRisk ρ density target midEstimator
          universalHilbertTheta
        <
      densitySquaredRisk ρ density target
          estimator universalHilbertTheta := by
    rw [← densitySquaredRisk_congr_ae
      ρ density target hd₀ae universalHilbertTheta]
    have hh :
        weakLpSquaredRisk
            (universalHilbertModelMeasure
              ν₁ ν₂ universalHilbertTheta)
            (universalHilbertTheta : ℝ) mid
          <
        weakLpSquaredRisk
            (universalHilbertModelMeasure
              ν₁ ν₂ universalHilbertTheta)
            (universalHilbertTheta : ℝ) d₀ := by
      simpa only [μ, universalHilbertProbabilityMeasure] using
        hmidAnchor
    rw [hriskEq universalHilbertTheta mid,
      hriskEq universalHilbertTheta d₀] at hh
    simpa only [midEstimator] using hh
  exact hadmissible.2
    ⟨midEstimator, hmidMeas, hdomle,
      ⟨universalHilbertTheta, hdomstrict⟩⟩

/-- The clipped weak `L²` representative of a measurably admissible rule
in the canonical universal reduced experiment. -/
def universalHilbertActionOfMeasurablyAdmissible
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    [IsFiniteMeasure
      (universalHilbertProbabilityMeasure ν₁ ν₂)]
    {estimator : UniversalReducedObservation → ℝ}
    (hadmissible :
      IsMeasurablyAdmissibleDensitySquared
        (universalHilbertDominatingMeasure ν₁ ν₂)
        (universalReducedLikelihood
          ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2))
        (fun θ : UniversalInteriorTheta => (θ : ℝ))
        estimator) :
    WeakHilbertAction
      (universalHilbertProbabilityMeasure ν₁ ν₂) :=
  weakHilbertActionOfMeasurable
    estimator hadmissible.1
    ((universalHilbertProbabilityMeasure_absolutelyContinuous ν₁ ν₂).ae_le
      (ae_mem_Icc_of_canonicalUniversalReduced_measurablyAdmissible
        hν₁ hν₂ hadmissible))

/-- The admissible rule's Hilbert representative agrees with the original
measurable rule under the canonical dominating measure. -/
theorem universalHilbertActionOfMeasurablyAdmissible_ae_eq
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    [IsFiniteMeasure
      (universalHilbertProbabilityMeasure ν₁ ν₂)]
    {estimator : UniversalReducedObservation → ℝ}
    (hadmissible :
      IsMeasurablyAdmissibleDensitySquared
        (universalHilbertDominatingMeasure ν₁ ν₂)
        (universalReducedLikelihood
          ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2))
        (fun θ : UniversalInteriorTheta => (θ : ℝ))
        estimator) :
    (fun x =>
      ((toWeakSpace ℝ
          (Lp ℝ 2
            (universalHilbertProbabilityMeasure ν₁ ν₂))).symm
        (universalHilbertActionOfMeasurablyAdmissible
          hν₁ hν₂ hadmissible :
          WeakSpace ℝ
            (Lp ℝ 2
              (universalHilbertProbabilityMeasure ν₁ ν₂)))) x)
      =ᵐ[universalHilbertDominatingMeasure ν₁ ν₂]
    estimator := by
  apply
    (universalHilbertDominatingMeasure_absolutelyContinuous
      hν₁ hν₂).ae_le
  exact
    weakHilbertActionOfMeasurable_ae_eq
      estimator hadmissible.1
      ((universalHilbertProbabilityMeasure_absolutelyContinuous
        ν₁ ν₂).ae_le
        (ae_mem_Icc_of_canonicalUniversalReduced_measurablyAdmissible
          hν₁ hν₂ hadmissible))

/-- Every measurably admissible rule belongs to the weak closure of the
anchor-risk-bounded positive finite-prior Bayes witness set. -/
theorem
    universalHilbertActionOfMeasurablyAdmissible_mem_bayesWitnessClosure
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    [IsFiniteMeasure
      (universalHilbertProbabilityMeasure ν₁ ν₂)]
    {estimator : UniversalReducedObservation → ℝ}
    (hadmissible :
      IsMeasurablyAdmissibleDensitySquared
        (universalHilbertDominatingMeasure ν₁ ν₂)
        (universalReducedLikelihood
          ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2))
        (fun θ : UniversalInteriorTheta => (θ : ℝ))
        estimator) :
    let d₀ :=
      universalHilbertActionOfMeasurablyAdmissible
        hν₁ hν₂ hadmissible
    (d₀ :
        WeakSpace ℝ
          (Lp ℝ 2
            (universalHilbertProbabilityMeasure ν₁ ν₂)))
      ∈
    closure
      (universalHilbertFiniteBayesWitnessSet
        ν₁ ν₂
        (d₀ :
          WeakSpace ℝ
            (Lp ℝ 2
              (universalHilbertProbabilityMeasure ν₁ ν₂)))) := by
  let d₀ :=
    universalHilbertActionOfMeasurablyAdmissible
      hν₁ hν₂ hadmissible
  obtain ⟨dstar, hdstarClosure, hle⟩ :=
    exists_universalHilbertBayesClosureDominator
      hν₁ hν₂
      (d₀ :
        WeakSpace ℝ
          (Lp ℝ 2
            (universalHilbertProbabilityMeasure ν₁ ν₂)))
      d₀.property
  have hdstar :
      dstar ∈ weakHilbertActionSet
        (universalHilbertProbabilityMeasure ν₁ ν₂) :=
    (closure_minimal
      (universalHilbertFiniteBayesWitnessSet_subset_action
        ν₁ ν₂
        (d₀ :
          WeakSpace ℝ
            (Lp ℝ 2
              (universalHilbertProbabilityMeasure ν₁ ν₂))))
      (isClosed_weakHilbertActionSet
        (universalHilbertProbabilityMeasure ν₁ ν₂)))
      hdstarClosure
  have heq :
      dstar =
        (d₀ :
          WeakSpace ℝ
            (Lp ℝ 2
              (universalHilbertProbabilityMeasure ν₁ ν₂))) :=
    universalHilbert_dominator_eq_of_measurablyAdmissible
      hν₁ hν₂ hdstar d₀.property
      (universalHilbertActionOfMeasurablyAdmissible_ae_eq
        hν₁ hν₂ hadmissible)
      hle hadmissible
  rwa [heq] at hdstarClosure

end

end GraybillDeal
