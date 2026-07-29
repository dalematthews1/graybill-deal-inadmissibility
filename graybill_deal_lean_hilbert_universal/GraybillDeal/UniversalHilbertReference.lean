import GraybillDeal.UniversalReducedLikelihoodNormalization
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder

/-!
# Hilbert reference measure for the universal reduced experiment

The specialized complete-class proof uses one fixed interior model measure
as its Hilbert-space reference.  We take `θ₀ = 1 / 2`.  The normalization
theorem for the canonical universal likelihood makes this a probability
measure, while strict positivity of the likelihood shows that it has
exactly the same null sets as the canonical sigma-finite reference measure.

This file deliberately contains only the reference-measure and bounded-rule
bookkeeping.  Weak compactness and risk lower semicontinuity are kept in
separate modules.
-/

namespace GraybillDeal

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The distinguished interior parameter used to put procedures in one
fixed `L²` space. -/
def universalHilbertTheta : UniversalInteriorTheta :=
  ⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩

@[simp]
theorem universalHilbertTheta_coe :
    (universalHilbertTheta : ℝ) = (1 : ℝ) / 2 :=
  rfl

/-- The canonical sigma-finite reference measure for residual degrees of
freedom `ν₁,ν₂`. -/
def universalHilbertDominatingMeasure (ν₁ ν₂ : ℕ) :
    Measure UniversalReducedObservation :=
  universalReducedObservationReference
    universalReducedLebesgueMeasure
    ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2)

/-- The normalized reduced model measure at `θ₀ = 1/2`. -/
def universalHilbertModelMeasure
    (ν₁ ν₂ : ℕ) (θ : UniversalInteriorTheta) :
    Measure UniversalReducedObservation :=
  (universalHilbertDominatingMeasure ν₁ ν₂).withDensity
    (fun x =>
      ENNReal.ofReal
        (universalReducedLikelihood
          ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2)
          θ x))

/-- The normalized reduced model measure at `θ₀ = 1/2`. -/
def universalHilbertProbabilityMeasure (ν₁ ν₂ : ℕ) :
    Measure UniversalReducedObservation :=
  universalHilbertModelMeasure ν₁ ν₂ universalHilbertTheta

/-- Every interior universal model measure is a probability measure. -/
theorem isProbabilityMeasure_universalHilbertModelMeasure
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (θ : UniversalInteriorTheta) :
    IsProbabilityMeasure
      (universalHilbertModelMeasure ν₁ ν₂ θ) := by
  simpa only
      [universalHilbertModelMeasure,
        universalHilbertDominatingMeasure] using
    (isProbabilityMeasure_universalReducedLikelihood_withDensity
      hν₁ hν₂ θ)

/-- The distinguished model measure is a probability measure. -/
theorem isProbabilityMeasure_universalHilbertProbabilityMeasure
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂) :
    IsProbabilityMeasure
      (universalHilbertProbabilityMeasure ν₁ ν₂) := by
  simpa only [universalHilbertProbabilityMeasure] using
    (isProbabilityMeasure_universalHilbertModelMeasure
      hν₁ hν₂ universalHilbertTheta)

/-- The Hilbert probability measure is absolutely continuous with respect
to the canonical dominating measure. -/
theorem universalHilbertProbabilityMeasure_absolutelyContinuous
    (ν₁ ν₂ : ℕ) :
    universalHilbertProbabilityMeasure ν₁ ν₂ ≪
      universalHilbertDominatingMeasure ν₁ ν₂ := by
  unfold universalHilbertProbabilityMeasure universalHilbertModelMeasure
  exact withDensity_absolutelyContinuous _ _

/-- Strict positivity of the distinguished likelihood gives the reverse
absolute-continuity relation. -/
theorem universalHilbertDominatingMeasure_absolutelyContinuous
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂) :
    universalHilbertDominatingMeasure ν₁ ν₂ ≪
      universalHilbertProbabilityMeasure ν₁ ν₂ := by
  have ha : 0 < (ν₁ : ℝ) / 2 := by positivity
  have hb : 0 < (ν₂ : ℝ) / 2 := by positivity
  unfold universalHilbertProbabilityMeasure universalHilbertModelMeasure
  apply withDensity_absolutelyContinuous'
  · exact
      ((measurable_universalReducedLikelihood_observation
        ha hb universalHilbertTheta).ennreal_ofReal).aemeasurable
  · filter_upwards [] with x
    exact ne_of_gt
      ((ENNReal.ofReal_pos).2
        (universalReducedLikelihood_pos
          ha hb universalHilbertTheta x))

/-- Every model measure is absolutely continuous with respect to the
distinguished Hilbert probability measure. -/
theorem universalHilbertModelMeasure_absolutelyContinuous_probability
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (θ : UniversalInteriorTheta) :
    universalHilbertModelMeasure ν₁ ν₂ θ ≪
      universalHilbertProbabilityMeasure ν₁ ν₂ :=
  (withDensity_absolutelyContinuous
      (universalHilbertDominatingMeasure ν₁ ν₂)
      (fun x =>
        ENNReal.ofReal
          (universalReducedLikelihood
            ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2) θ x))).trans
    (universalHilbertDominatingMeasure_absolutelyContinuous
      hν₁ hν₂)

/-- Almost-everywhere statements are identical for the canonical
dominating measure and the distinguished Hilbert probability measure. -/
theorem ae_universalHilbertProbabilityMeasure_iff
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    {p : UniversalReducedObservation → Prop} :
    (∀ᵐ x ∂universalHilbertProbabilityMeasure ν₁ ν₂, p x) ↔
      ∀ᵐ x ∂universalHilbertDominatingMeasure ν₁ ν₂, p x := by
  constructor
  · intro hp
    exact
      (universalHilbertDominatingMeasure_absolutelyContinuous
        hν₁ hν₂).ae_le hp
  · intro hρ
    exact
      (universalHilbertProbabilityMeasure_absolutelyContinuous
        ν₁ ν₂).ae_le hρ

/-- A measurable rule which is canonically almost everywhere in `[0,1]`
defines an element of the distinguished `L²` space. -/
theorem memLp_two_universalHilbertProbabilityMeasure_of_ae_mem_Icc
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    {estimator : UniversalReducedObservation → ℝ}
    (hestimator : Measurable estimator)
    (hbounded :
      ∀ᵐ x ∂universalHilbertDominatingMeasure ν₁ ν₂,
        estimator x ∈ Icc (0 : ℝ) 1) :
    MemLp estimator 2
      (universalHilbertProbabilityMeasure ν₁ ν₂) := by
  letI :
      IsProbabilityMeasure
        (universalHilbertProbabilityMeasure ν₁ ν₂) :=
    isProbabilityMeasure_universalHilbertProbabilityMeasure hν₁ hν₂
  apply memLp_of_bounded
    ((universalHilbertProbabilityMeasure_absolutelyContinuous
      ν₁ ν₂).ae_le hbounded)
    hestimator.aestronglyMeasurable
    2

/-- The `L²` representative of a measurable canonically clipped rule. -/
def universalHilbertRule
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (estimator : UniversalReducedObservation → ℝ)
    (hestimator : Measurable estimator)
    (hbounded :
      ∀ᵐ x ∂universalHilbertDominatingMeasure ν₁ ν₂,
        estimator x ∈ Icc (0 : ℝ) 1) :
    Lp ℝ 2 (universalHilbertProbabilityMeasure ν₁ ν₂) :=
  (memLp_two_universalHilbertProbabilityMeasure_of_ae_mem_Icc
    hν₁ hν₂ hestimator hbounded).toLp estimator

/-- The `L²` representative agrees almost everywhere with the original
rule under the Hilbert probability measure. -/
theorem universalHilbertRule_ae_eq
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (estimator : UniversalReducedObservation → ℝ)
    (hestimator : Measurable estimator)
    (hbounded :
      ∀ᵐ x ∂universalHilbertDominatingMeasure ν₁ ν₂,
        estimator x ∈ Icc (0 : ℝ) 1) :
    universalHilbertRule hν₁ hν₂ estimator hestimator hbounded
      =ᵐ[universalHilbertProbabilityMeasure ν₁ ν₂]
    estimator :=
  MemLp.coeFn_toLp
    (memLp_two_universalHilbertProbabilityMeasure_of_ae_mem_Icc
      hν₁ hν₂ hestimator hbounded)

end

end GraybillDeal
