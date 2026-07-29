import GraybillDeal.UniversalFiniteSeparation
import GraybillDeal.UniversalInteriorDecision
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Measurability-correct decision interface for the complete-class theorem

The printed Lehmann--Casella theorem is a theorem about statistical
procedures, hence about measurable estimators.  The early project
definition `IsAdmissibleDensitySquared` deliberately quantified over all
real-valued functions.  That is a stronger notion, but it is not the exact
interface of the cited theorem.

This file records the exact measurable interface and proves the safe bridge:
an estimator which is admissible against *all* functions and is measurable
is admissible against measurable procedures.  Thus the old, stronger
notion can still be used in the final contradiction without silently
applying the complete-class theorem to nonmeasurable procedures.

It also verifies the elementary regularity conditions for the universal
reduced Graybill--Deal experiment: measurability and positivity of its
likelihood, measurability of its baseline, continuity and strict convexity
of squared loss, and coercivity on the open unit parameter interval.
-/

namespace GraybillDeal

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

noncomputable section

variable {Θ X : Type*}

/-- Domination by a measurable statistical procedure. -/
def MeasurableDensitySquaredRiskDominates
    [MeasurableSpace X]
    (m : Measure X) (density : Θ → X → ℝ)
    (target : Θ → ℝ)
    (candidate baseline : X → ℝ) : Prop :=
  Measurable candidate ∧
    DensitySquaredRiskDominates
      m density target candidate baseline

/-- Admissibility in the class of measurable real-valued procedures.

The estimator itself is explicitly required to be measurable. -/
def IsMeasurablyAdmissibleDensitySquared
    [MeasurableSpace X]
    (m : Measure X) (density : Θ → X → ℝ)
    (target : Θ → ℝ) (estimator : X → ℝ) : Prop :=
  Measurable estimator ∧
    ¬ ∃ candidate : X → ℝ,
      MeasurableDensitySquaredRiskDominates
        m density target candidate estimator

theorem isMeasurablyAdmissible_of_isAdmissibleDensitySquared
    [MeasurableSpace X]
    {m : Measure X} {density : Θ → X → ℝ}
    {target : Θ → ℝ} {estimator : X → ℝ}
    (hmeas : Measurable estimator)
    (hadmissible :
      IsAdmissibleDensitySquared m density target estimator) :
    IsMeasurablyAdmissibleDensitySquared
      m density target estimator := by
  refine ⟨hmeas, ?_⟩
  rintro ⟨candidate, _hcandidate, hdom⟩
  exact hadmissible ⟨candidate, hdom⟩

/-- The exact finite-Bayes conclusion of the printed complete-class
theorem, now restricted to measurable procedures.  This is still an
ordinary proposition, not an axiom asserting the theorem. -/
def MeasurablePositiveFiniteBayesCompleteClassProperty
    [MeasurableSpace X]
    (m : Measure X) (density : Θ → X → ℝ)
    (target : Θ → ℝ) : Prop :=
  ∀ estimator : X → ℝ,
    IsMeasurablyAdmissibleDensitySquared
        m density target estimator →
      HasPositiveFiniteBayesApproximation
        m density target estimator

theorem hasPositiveFiniteBayesApproximation_of_strong_admissible
    [MeasurableSpace X]
    {m : Measure X} {density : Θ → X → ℝ}
    {target : Θ → ℝ} {estimator : X → ℝ}
    (hcomplete :
      MeasurablePositiveFiniteBayesCompleteClassProperty
        m density target)
    (hmeas : Measurable estimator)
    (hadmissible :
      IsAdmissibleDensitySquared m density target estimator) :
    HasPositiveFiniteBayesApproximation
      m density target estimator :=
  hcomplete estimator
    (isMeasurablyAdmissible_of_isAdmissibleDensitySquared
      hmeas hadmissible)

/-- Squared loss for the reduced unit-interval parameter. -/
def universalInteriorSquaredLoss
    (θ : UniversalInteriorTheta) (d : ℝ) : ℝ :=
  (d - (θ : ℝ)) ^ 2

theorem continuous_universalInteriorSquaredLoss :
    Continuous
      (fun z : UniversalInteriorTheta × ℝ =>
        universalInteriorSquaredLoss z.1 z.2) := by
  unfold universalInteriorSquaredLoss
  fun_prop

/-- Exact positive gap proving strict convexity of squared loss. -/
theorem universalInteriorSquaredLoss_convex_gap
    (θ : UniversalInteriorTheta) (d₁ d₂ t : ℝ) :
    t * universalInteriorSquaredLoss θ d₁
        + (1 - t) * universalInteriorSquaredLoss θ d₂
        - universalInteriorSquaredLoss θ
            (t * d₁ + (1 - t) * d₂)
      =
    t * (1 - t) * (d₁ - d₂) ^ 2 := by
  unfold universalInteriorSquaredLoss
  ring

theorem universalInteriorSquaredLoss_strictConvex
    (θ : UniversalInteriorTheta)
    {d₁ d₂ t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hd : d₁ ≠ d₂) :
    universalInteriorSquaredLoss θ
        (t * d₁ + (1 - t) * d₂)
      <
    t * universalInteriorSquaredLoss θ d₁
      + (1 - t) * universalInteriorSquaredLoss θ d₂ := by
  have hsq : 0 < (d₁ - d₂) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hd)
  have hgap : 0 < t * (1 - t) * (d₁ - d₂) ^ 2 := by positivity
  rw [← universalInteriorSquaredLoss_convex_gap θ d₁ d₂ t] at hgap
  linarith

/-- Elementary coercivity bound, uniform over `θ ∈ (0,1)`.

For every requested loss level `M`, actions with
`|d| ≥ max M 0 + 2` have squared loss at least `M`. -/
theorem universalInteriorSquaredLoss_coercive
    (θ : UniversalInteriorTheta) (M : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ d : ℝ, R ≤ |d| →
        M ≤ universalInteriorSquaredLoss θ d := by
  refine ⟨max M 0 + 2, by positivity, ?_⟩
  intro d hd
  have hθabs : |(θ : ℝ)| < 1 := by
    rw [abs_of_pos θ.property.1]
    exact θ.property.2
  have hreverse : |d| - |(θ : ℝ)| ≤ |d - (θ : ℝ)| := by
    exact (abs_sub_abs_le_abs_sub d (θ : ℝ))
  have hlower : max M 0 + 1 < |d - (θ : ℝ)| := by
    linarith
  have hM : M ≤ max M 0 := le_max_left _ _
  have hmax_nonneg : 0 ≤ max M 0 := le_max_right _ _
  have habs_nonneg : 0 ≤ |d - (θ : ℝ)| := abs_nonneg _
  unfold universalInteriorSquaredLoss
  rw [← sq_abs]
  nlinarith [sq_nonneg (max M 0)]

theorem continuous_universalReducedBaseline :
    Continuous universalReducedBaseline := by
  unfold universalReducedBaseline UniversalReducedObservation.r
  fun_prop

theorem measurable_universalReducedBaseline :
    Measurable universalReducedBaseline :=
  continuous_universalReducedBaseline.measurable

theorem continuous_universalReducedLikelihood_observation
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta) :
    Continuous (universalReducedLikelihood a b θ) := by
  unfold universalReducedLikelihood universalKernel
  apply continuous_const.mul
  have hB :
      Continuous
        (fun x : UniversalReducedObservation =>
          universalB a b x.r x.q
            (universalInteriorThetaInclusion θ)) := by
    unfold universalB UniversalReducedObservation.r
      UniversalReducedObservation.q
    fun_prop
  exact hB.rpow_const fun x =>
    Or.inl (ne_of_gt
      (universalB_pos ha hb x.r_pos x.r_lt_one x.q_nonneg _))

theorem measurable_universalReducedLikelihood_observation
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta) :
    Measurable (universalReducedLikelihood a b θ) :=
  (continuous_universalReducedLikelihood_observation ha hb θ).measurable

/-- The dominated-model regularity assumptions used by the specialized
Lehmann--Casella statement.

`sigmaFinite` is stored explicitly so a theorem consuming this structure
can install it as a local typeclass instance. -/
structure UniversalReducedDominatedRegularity
    (ρ : Measure UniversalReducedObservation)
    (a b : ℝ) : Prop where
  sigmaFinite : SigmaFinite ρ
  likelihood_measurable :
    ∀ θ : UniversalInteriorTheta,
      Measurable (universalReducedLikelihood a b θ)
  likelihood_pos :
    ∀ θ : UniversalInteriorTheta,
      ∀ x : UniversalReducedObservation,
        0 < universalReducedLikelihood a b θ x
  baseline_measurable : Measurable universalReducedBaseline

theorem universalReducedDominatedRegularity
    (ρ : Measure UniversalReducedObservation)
    [SigmaFinite ρ]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    UniversalReducedDominatedRegularity ρ a b where
  sigmaFinite := inferInstance
  likelihood_measurable :=
    measurable_universalReducedLikelihood_observation ha hb
  likelihood_pos :=
    universalReducedLikelihood_pos ha hb
  baseline_measurable :=
    measurable_universalReducedBaseline

/-- Measurability-correct complete-class property specialized to the
universal reduced experiment. -/
abbrev UniversalMeasurableFiniteBayesCompleteClassProperty
    (ρ : Measure UniversalReducedObservation)
    (a b : ℝ) : Prop :=
  MeasurablePositiveFiniteBayesCompleteClassProperty
    ρ
    (universalReducedLikelihood a b)
    (fun θ : UniversalInteriorTheta => (θ : ℝ))

end

end GraybillDeal
