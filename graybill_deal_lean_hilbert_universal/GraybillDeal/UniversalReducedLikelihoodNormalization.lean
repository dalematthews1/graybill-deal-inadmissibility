import GraybillDeal.UniversalConditionalRawTheorem
import GraybillDeal.UniversalCompactAction
import GraybillDeal.UniversalRawDensityIdentity

/-!
# Normalization of the canonical universal reduced likelihood

The universal reduced likelihood was obtained by absorbing the
observation-only factor in the exact risk-tilted reduced density into the
canonical reference measure.  This file proves that the resulting
likelihood is normalized.

For arbitrary positive residual degrees of freedom, every interior reduced
parameter is realized by positive raw variances.  The exact Gamma
pushforward theorem therefore identifies the rebased likelihood measure
with the measurable image of a product of three probability measures.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- The exact risk-tilted component measure is a probability measure for
all positive residual degrees of freedom. -/
theorem
    isProbabilityMeasure_universalRawRiskTiltedIndependentComponentMeasure
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂) :
    IsProbabilityMeasure
      (universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂) := by
  letI : IsProbabilityMeasure (gammaMeasure (3 / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  letI :
      IsProbabilityMeasure
        (gammaMeasure ((ν₁ : ℝ) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  letI :
      IsProbabilityMeasure
        (gammaMeasure ((ν₂ : ℝ) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  unfold universalRawRiskTiltedIndependentComponentMeasure
  infer_instance

/-- For every positive pair of residual degrees of freedom and every
interior oracle parameter, the canonical rebased likelihood defines a
probability measure. -/
theorem
    isProbabilityMeasure_universalReducedLikelihood_withDensity
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (θ : UniversalInteriorTheta) :
    IsProbabilityMeasure
      ((universalReducedObservationReference
          universalReducedLebesgueMeasure
          ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2)).withDensity
        (fun x =>
          ENNReal.ofReal
            (universalReducedLikelihood
              ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2) θ x))) := by
  let v₁ : NNReal := universalRawVariance1Realizing ν₁ θ
  let v₂ : NNReal := universalRawVariance2Realizing ν₂ θ
  have hv₁ : 0 < v₁ :=
    universalRawVariance1Realizing_pos ν₁ θ
  have hv₂ : 0 < v₂ :=
    universalRawVariance2Realizing_pos ν₂ θ
  have ha : 0 < (ν₁ : ℝ) / 2 := by positivity
  have hb : 0 < (ν₂ : ℝ) / 2 := by positivity
  have hθ :
      universalRawOracleInteriorTheta
          ν₁ ν₂ v₁ v₂ hv₁ hv₂
        =
      θ := by
    apply Subtype.ext
    exact universalRawOracleTheta_realizing ν₁ ν₂ θ
  let μ : Measure (ℝ × ℝ × ℝ) :=
    universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂
  let F : (ℝ × ℝ × ℝ) → UniversalReducedObservation :=
    universalRawComponentsReducedObservation ν₁ ν₂ v₁ v₂
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact
      isProbabilityMeasure_universalRawRiskTiltedIndependentComponentMeasure
        hν₁ hν₂
  letI : IsProbabilityMeasure (Measure.map F μ) :=
    Measure.isProbabilityMeasure_map
      (measurable_universalRawComponentsReducedObservation
        ν₁ ν₂ v₁ v₂).aemeasurable
  have hDensity :
      HasUniversalReducedDensity
        universalReducedLebesgueMeasure
        (Measure.map F μ)
        ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2) θ := by
    have hpush :=
      universalRiskTiltedComponentReducedDensityIdentity
        hν₁ hν₂ hv₁ hv₂
    unfold UniversalRiskTiltedComponentReducedDensityIdentity at hpush
    unfold HasUniversalReducedDensity
    simpa only [μ, F, hθ] using hpush
  have hRebased :
      Measure.map F μ
        =
      (universalReducedObservationReference
          universalReducedLebesgueMeasure
          ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2)).withDensity
        (fun x =>
          ENNReal.ofReal
            (universalReducedLikelihood
              ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2) θ x)) :=
    (hasUniversalReducedDensity_iff_rebasedLikelihood
      ha hb θ).1 hDensity
  rw [← hRebased]
  infer_instance

/-- Integral form of likelihood normalization. -/
theorem universalReducedLikelihood_lintegral_eq_one
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (θ : UniversalInteriorTheta) :
    (∫⁻ x,
        ENNReal.ofReal
          (universalReducedLikelihood
            ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2) θ x)
      ∂universalReducedObservationReference
        universalReducedLebesgueMeasure
        ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2))
      =
    1 := by
  letI :
      IsProbabilityMeasure
        ((universalReducedObservationReference
            universalReducedLebesgueMeasure
            ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2)).withDensity
          (fun x =>
            ENNReal.ofReal
              (universalReducedLikelihood
                ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2) θ x))) :=
    isProbabilityMeasure_universalReducedLikelihood_withDensity
      hν₁ hν₂ θ
  have hmass :
      ((universalReducedObservationReference
          universalReducedLebesgueMeasure
          ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2)).withDensity
        (fun x =>
          ENNReal.ofReal
            (universalReducedLikelihood
              ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2) θ x)))
        Set.univ
        =
      1 :=
    IsProbabilityMeasure.measure_univ
  rw [withDensity_apply _ MeasurableSet.univ] at hmass
  simpa only [Measure.restrict_univ] using hmass

/-- Every measurably admissible rule in the canonical rebased experiment
takes values in the compact action interval `[0,1]` almost everywhere.

The finite-risk premise needed for strict clipping is discharged by the
normalization theorem above. -/
theorem
    ae_mem_Icc_of_canonicalUniversalReduced_measurablyAdmissible
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    {estimator : UniversalReducedObservation → ℝ}
    (hadmissible :
      IsMeasurablyAdmissibleDensitySquared
        (universalReducedObservationReference
          universalReducedLebesgueMeasure
          ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2))
        (universalReducedLikelihood
          ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2))
        (fun θ : UniversalInteriorTheta => (θ : ℝ))
        estimator) :
    ∀ᵐ x
        ∂universalReducedObservationReference
          universalReducedLebesgueMeasure
          ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2),
      estimator x ∈ Set.Icc (0 : ℝ) 1 := by
  have ha : 0 < (ν₁ : ℝ) / 2 := by positivity
  have hb : 0 < (ν₂ : ℝ) / 2 := by positivity
  letI : Nonempty UniversalInteriorTheta :=
    Set.nonempty_Ioo_subtype (by norm_num)
  exact
    ae_mem_Icc_of_measurablyAdmissible_of_normalized
      (universalReducedObservationReference
        universalReducedLebesgueMeasure
        ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2))
      (fun θ =>
        measurable_universalReducedLikelihood_observation ha hb θ)
      (fun θ x =>
        universalReducedLikelihood_pos ha hb θ x)
      (fun θ =>
        universalReducedLikelihood_lintegral_eq_one hν₁ hν₂ θ)
      (fun θ : UniversalInteriorTheta => (θ : ℝ))
      (fun θ => ⟨θ.property.1, θ.property.2⟩)
      hadmissible

end

end GraybillDeal
