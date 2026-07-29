import GraybillDeal.UniversalReducedDominator
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Positive scaling of dominated squared risks

The raw `D²`-weighted reduced law is naturally an unnormalised finite
measure.  Its total mass is the variance of the sample-mean difference.
Multiplying the dominating measure by any finite positive constant
multiplies every risk by that constant, so weak and strict domination are
unchanged.
-/

namespace GraybillDeal

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {Θ X : Type*} [MeasurableSpace X]

theorem densitySquaredRisk_smul_measure
    (c : ℝ≥0∞)
    (m : Measure X) (density : Θ → X → ℝ)
    (target : Θ → ℝ) (estimator : X → ℝ) (θ : Θ) :
    densitySquaredRisk (c • m) density target estimator θ
      =
    c * densitySquaredRisk m density target estimator θ := by
  unfold densitySquaredRisk
  rw [lintegral_smul_measure]
  rfl

/-- Domination is preserved after multiplying the dominating measure by
a finite nonzero constant. -/
theorem DensitySquaredRiskDominates.smul_measure
    {m : Measure X} {density : Θ → X → ℝ}
    {target : Θ → ℝ} {candidate baseline : X → ℝ}
    (hdom :
      DensitySquaredRiskDominates
        m density target candidate baseline)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ∞) :
    DensitySquaredRiskDominates
      (c • m) density target candidate baseline := by
  constructor
  · intro θ
    rw [densitySquaredRisk_smul_measure,
      densitySquaredRisk_smul_measure]
    exact mul_le_mul_left' (hdom.1 θ) c
  · obtain ⟨θ, hθ⟩ := hdom.2
    refine ⟨θ, ?_⟩
    rw [densitySquaredRisk_smul_measure,
      densitySquaredRisk_smul_measure,
      ENNReal.mul_lt_mul_iff_right hc0 hctop]
    exact hθ

theorem MeasurableDensitySquaredRiskDominates.smul_measure
    {m : Measure X} {density : Θ → X → ℝ}
    {target : Θ → ℝ} {candidate baseline : X → ℝ}
    (hdom :
      MeasurableDensitySquaredRiskDominates
        m density target candidate baseline)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ∞) :
    MeasurableDensitySquaredRiskDominates
      (c • m) density target candidate baseline :=
  ⟨hdom.1, hdom.2.smul_measure c hc0 hctop⟩

theorem universalReducedObservationReference_smul
    (c : ℝ≥0∞) (reference : Measure UniversalReducedObservation)
    (a b : ℝ) :
    universalReducedObservationReference (c • reference) a b
      =
    c • universalReducedObservationReference reference a b := by
  unfold universalReducedObservationReference
  exact withDensity_smul_measure c _

/-- The canonical universal reduced dominator remains a dominator for
every finite positive rescaling of the Lebesgue reference measure. -/
theorem exists_scaled_canonicalUniversalReduced_dominator_of_completeClass
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcomplete :
      UniversalMeasurableFiniteBayesCompleteClassProperty
        (universalReducedObservationReference
          universalReducedLebesgueMeasure a b)
        a b)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ∞) :
    ∃ candidate : UniversalReducedObservation → ℝ,
      MeasurableDensitySquaredRiskDominates
        (universalReducedObservationReference
          (c • universalReducedLebesgueMeasure) a b)
        (universalReducedLikelihood a b)
        (fun θ => (θ : ℝ))
        candidate
        universalReducedBaseline := by
  obtain ⟨candidate, hcandidate⟩ :=
    exists_canonicalUniversalReduced_dominator_of_completeClass
      ha hb hcomplete
  refine ⟨candidate, ?_⟩
  rw [universalReducedObservationReference_smul]
  exact hcandidate.smul_measure c hc0 hctop

end

end GraybillDeal
