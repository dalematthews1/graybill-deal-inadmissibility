import GraybillDeal.UniversalDecision
import GraybillDeal.UniversalReducedDensity
import GraybillDeal.UniversalRawRiskTransport
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# From dominated `ENNReal` risk to ordinary reduced weighted risk

The complete-class layer deliberately uses `ℝ≥0∞` risks, so that a
nonintegrable procedure is assigned infinite risk rather than the Bochner
integral's default value zero.  The raw normal-sample transport, on the
other hand, is stated using ordinary real integrals under explicit
integrability hypotheses.

This file is the conversion layer between those two representations.  It
does not assert the remaining raw change-of-variables theorem.  Instead it
proves:

* exact rebasing through `Measure.withDensity`;
* finite `ℝ≥0∞` risk implies integrability of the squared loss under the
  corresponding risk-weighted law;
* finite weak and strict `ℝ≥0∞` comparisons give weak and strict
  comparisons of ordinary real integrals;
* an optional abstract weighted-pushforward interface turns those reduced
  real integrals into the weighted raw integrals consumed by
  `UniversalRawRiskTransport`.
-/

namespace GraybillDeal

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {Θ X Ω : Type*}
  [MeasurableSpace X] [MeasurableSpace Ω]

/-- Ordinary real squared-error risk under a measure.  Unlike
`densitySquaredRisk`, this representation is intended only after
integrability has been established. -/
def measureSquaredRisk
    (Q : Measure X) (target : Θ → ℝ)
    (estimator : X → ℝ) (θ : Θ) : ℝ :=
  ∫ x, (estimator x - target θ) ^ 2 ∂Q

theorem measurable_squaredError
    {target : Θ → ℝ} {estimator : X → ℝ}
    (hestimator : Measurable estimator) (θ : Θ) :
    Measurable (fun x => (estimator x - target θ) ^ 2) := by
  fun_prop

theorem densitySquaredRisk_eq_lintegral_of_eq_withDensity
    {m Q : Measure X} {density : Θ → X → ℝ}
    {target : Θ → ℝ} {estimator : X → ℝ} {θ : Θ}
    (hdensity : Measurable (density θ))
    (hestimator : Measurable estimator)
    (hQ :
      Q = m.withDensity (fun x => ENNReal.ofReal (density θ x))) :
    densitySquaredRisk m density target estimator θ
      =
    ∫⁻ x, ENNReal.ofReal ((estimator x - target θ) ^ 2) ∂Q := by
  rw [hQ,
    lintegral_withDensity_eq_lintegral_mul
      m hdensity.ennreal_ofReal
      (measurable_squaredError hestimator θ).ennreal_ofReal]
  rfl

theorem integrable_squaredError_of_densitySquaredRisk_ne_top
    {m Q : Measure X} {density : Θ → X → ℝ}
    {target : Θ → ℝ} {estimator : X → ℝ} {θ : Θ}
    (hdensity : Measurable (density θ))
    (hestimator : Measurable estimator)
    (hQ :
      Q = m.withDensity (fun x => ENNReal.ofReal (density θ x)))
    (hfinite :
      densitySquaredRisk m density target estimator θ ≠ ⊤) :
    Integrable (fun x => (estimator x - target θ) ^ 2) Q := by
  have hlintegral :
      (∫⁻ x, ENNReal.ofReal ((estimator x - target θ) ^ 2) ∂Q)
        < ⊤ := by
    rw [← densitySquaredRisk_eq_lintegral_of_eq_withDensity
      hdensity hestimator hQ]
    exact lt_top_iff_ne_top.mpr hfinite
  refine ⟨(measurable_squaredError hestimator θ).aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => sq_nonneg _)).mpr hlintegral

theorem ofReal_measureSquaredRisk_eq_densitySquaredRisk
    {m Q : Measure X} {density : Θ → X → ℝ}
    {target : Θ → ℝ} {estimator : X → ℝ} {θ : Θ}
    (hdensity : Measurable (density θ))
    (hestimator : Measurable estimator)
    (hQ :
      Q = m.withDensity (fun x => ENNReal.ofReal (density θ x)))
    (hfinite :
      densitySquaredRisk m density target estimator θ ≠ ⊤) :
    ENNReal.ofReal (measureSquaredRisk Q target estimator θ)
      =
    densitySquaredRisk m density target estimator θ := by
  have hint :=
    integrable_squaredError_of_densitySquaredRisk_ne_top
      hdensity hestimator hQ hfinite
  rw [measureSquaredRisk,
    ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  exact
    (densitySquaredRisk_eq_lintegral_of_eq_withDensity
      hdensity hestimator hQ).symm

theorem densitySquaredRisk_ne_top_of_integrable_squaredError
    {m Q : Measure X} {density : Θ → X → ℝ}
    {target : Θ → ℝ} {estimator : X → ℝ} {θ : Θ}
    (hdensity : Measurable (density θ))
    (hestimator : Measurable estimator)
    (hQ :
      Q = m.withDensity (fun x => ENNReal.ofReal (density θ x)))
    (hint : Integrable (fun x => (estimator x - target θ) ^ 2) Q) :
    densitySquaredRisk m density target estimator θ ≠ ⊤ := by
  rw [densitySquaredRisk_eq_lintegral_of_eq_withDensity
    hdensity hestimator hQ]
  exact lt_top_iff_ne_top.mp
    ((hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun x => sq_nonneg _)).mp
        hint.hasFiniteIntegral)

theorem measureSquaredRisk_eq_densitySquaredRisk_toReal
    {m Q : Measure X} {density : Θ → X → ℝ}
    {target : Θ → ℝ} {estimator : X → ℝ} {θ : Θ}
    (hdensity : Measurable (density θ))
    (hestimator : Measurable estimator)
    (hQ :
      Q = m.withDensity (fun x => ENNReal.ofReal (density θ x)))
    (hfinite :
      densitySquaredRisk m density target estimator θ ≠ ⊤) :
    measureSquaredRisk Q target estimator θ
      =
    (densitySquaredRisk m density target estimator θ).toReal := by
  have hnonneg :
      0 ≤ measureSquaredRisk Q target estimator θ := by
    exact integral_nonneg fun x => sq_nonneg _
  rw [← ENNReal.toReal_ofReal hnonneg]
  congr 1
  exact ofReal_measureSquaredRisk_eq_densitySquaredRisk
    hdensity hestimator hQ hfinite

/-- A finite weak comparison of dominated risks is the same weak
comparison of the corresponding ordinary real risks. -/
theorem measureSquaredRisk_le_of_densitySquaredRisk_le
    {m Q : Measure X} {density : Θ → X → ℝ}
    {target : Θ → ℝ} {candidate baseline : X → ℝ} {θ : Θ}
    (hdensity : Measurable (density θ))
    (hcandidate : Measurable candidate)
    (hbaseline : Measurable baseline)
    (hQ :
      Q = m.withDensity (fun x => ENNReal.ofReal (density θ x)))
    (hbaselineFinite :
      densitySquaredRisk m density target baseline θ ≠ ⊤)
    (hle :
      densitySquaredRisk m density target candidate θ
        ≤ densitySquaredRisk m density target baseline θ) :
    measureSquaredRisk Q target candidate θ
      ≤ measureSquaredRisk Q target baseline θ := by
  have hcandidateFinite :
      densitySquaredRisk m density target candidate θ ≠ ⊤ :=
    ne_top_of_le_ne_top hbaselineFinite hle
  rw [measureSquaredRisk_eq_densitySquaredRisk_toReal
      hdensity hcandidate hQ hcandidateFinite,
    measureSquaredRisk_eq_densitySquaredRisk_toReal
      hdensity hbaseline hQ hbaselineFinite]
  exact ENNReal.toReal_mono hbaselineFinite hle

/-- A finite strict comparison of dominated risks is the same strict
comparison of the corresponding ordinary real risks. -/
theorem measureSquaredRisk_lt_of_densitySquaredRisk_lt
    {m Q : Measure X} {density : Θ → X → ℝ}
    {target : Θ → ℝ} {candidate baseline : X → ℝ} {θ : Θ}
    (hdensity : Measurable (density θ))
    (hcandidate : Measurable candidate)
    (hbaseline : Measurable baseline)
    (hQ :
      Q = m.withDensity (fun x => ENNReal.ofReal (density θ x)))
    (hbaselineFinite :
      densitySquaredRisk m density target baseline θ ≠ ⊤)
    (hlt :
      densitySquaredRisk m density target candidate θ
        < densitySquaredRisk m density target baseline θ) :
    measureSquaredRisk Q target candidate θ
      < measureSquaredRisk Q target baseline θ := by
  have hcandidateFinite :
      densitySquaredRisk m density target candidate θ ≠ ⊤ :=
    ne_top_of_le_ne_top hbaselineFinite hlt.le
  rw [measureSquaredRisk_eq_densitySquaredRisk_toReal
      hdensity hcandidate hQ hcandidateFinite,
    measureSquaredRisk_eq_densitySquaredRisk_toReal
      hdensity hbaseline hQ hbaselineFinite]
  exact ENNReal.toReal_strict_mono hbaselineFinite hlt

/-! ## Specialization to the universal reduced density -/

theorem HasUniversalReducedDensity.densitySquaredRisk_eq_lintegral
    {reference Q : Measure UniversalReducedObservation}
    {a b : ℝ} {θ : UniversalInteriorTheta}
    (hQ : HasUniversalReducedDensity reference Q a b θ)
    (estimator : UniversalReducedObservation → ℝ)
    (hestimator : Measurable estimator) :
    densitySquaredRisk reference
        (universalFullReducedDensity a b)
        (fun η : UniversalInteriorTheta => (η : ℝ))
        estimator θ
      =
    ∫⁻ x, ENNReal.ofReal ((estimator x - (θ : ℝ)) ^ 2) ∂Q := by
  exact densitySquaredRisk_eq_lintegral_of_eq_withDensity
    (measurable_universalFullReducedDensity a b θ)
    hestimator hQ.eq_withDensity

theorem HasUniversalReducedDensity.integrable_squaredError_of_finite
    {reference Q : Measure UniversalReducedObservation}
    {a b : ℝ} {θ : UniversalInteriorTheta}
    (hQ : HasUniversalReducedDensity reference Q a b θ)
    {estimator : UniversalReducedObservation → ℝ}
    (hestimator : Measurable estimator)
    (hfinite :
      densitySquaredRisk reference
        (universalFullReducedDensity a b)
        (fun η : UniversalInteriorTheta => (η : ℝ))
        estimator θ ≠ ⊤) :
    Integrable (fun x => (estimator x - (θ : ℝ)) ^ 2) Q := by
  exact integrable_squaredError_of_densitySquaredRisk_ne_top
    (measurable_universalFullReducedDensity a b θ)
    hestimator hQ.eq_withDensity hfinite

theorem HasUniversalReducedDensity.measureSquaredRisk_le
    {reference Q : Measure UniversalReducedObservation}
    {a b : ℝ} {θ : UniversalInteriorTheta}
    (hQ : HasUniversalReducedDensity reference Q a b θ)
    {candidate baseline : UniversalReducedObservation → ℝ}
    (hcandidate : Measurable candidate)
    (hbaseline : Measurable baseline)
    (hbaselineFinite :
      densitySquaredRisk reference
        (universalFullReducedDensity a b)
        (fun η : UniversalInteriorTheta => (η : ℝ))
        baseline θ ≠ ⊤)
    (hle :
      densitySquaredRisk reference
          (universalFullReducedDensity a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          candidate θ
        ≤
      densitySquaredRisk reference
          (universalFullReducedDensity a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          baseline θ) :
    measureSquaredRisk Q
        (fun η : UniversalInteriorTheta => (η : ℝ))
        candidate θ
      ≤
    measureSquaredRisk Q
        (fun η : UniversalInteriorTheta => (η : ℝ))
        baseline θ := by
  exact measureSquaredRisk_le_of_densitySquaredRisk_le
    (measurable_universalFullReducedDensity a b θ)
    hcandidate hbaseline hQ.eq_withDensity hbaselineFinite hle

theorem HasUniversalReducedDensity.measureSquaredRisk_lt
    {reference Q : Measure UniversalReducedObservation}
    {a b : ℝ} {θ : UniversalInteriorTheta}
    (hQ : HasUniversalReducedDensity reference Q a b θ)
    {candidate baseline : UniversalReducedObservation → ℝ}
    (hcandidate : Measurable candidate)
    (hbaseline : Measurable baseline)
    (hbaselineFinite :
      densitySquaredRisk reference
        (universalFullReducedDensity a b)
        (fun η : UniversalInteriorTheta => (η : ℝ))
        baseline θ ≠ ⊤)
    (hlt :
      densitySquaredRisk reference
          (universalFullReducedDensity a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          candidate θ
        <
      densitySquaredRisk reference
          (universalFullReducedDensity a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          baseline θ) :
    measureSquaredRisk Q
        (fun η : UniversalInteriorTheta => (η : ℝ))
        candidate θ
      <
    measureSquaredRisk Q
        (fun η : UniversalInteriorTheta => (η : ℝ))
        baseline θ := by
  exact measureSquaredRisk_lt_of_densitySquaredRisk_lt
    (measurable_universalFullReducedDensity a b θ)
    hcandidate hbaseline hQ.eq_withDensity hbaselineFinite hlt

/-! ### The likelihood-rebased form used by the complete-class theorem -/

theorem HasUniversalReducedDensity.rebased_densitySquaredRisk_eq_lintegral
    {reference Q : Measure UniversalReducedObservation}
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (hQ : HasUniversalReducedDensity reference Q a b θ)
    (estimator : UniversalReducedObservation → ℝ)
    (hestimator : Measurable estimator) :
    densitySquaredRisk
        (universalReducedObservationReference reference a b)
        (universalReducedLikelihood a b)
        (fun η : UniversalInteriorTheta => (η : ℝ))
        estimator θ
      =
    ∫⁻ x, ENNReal.ofReal ((estimator x - (θ : ℝ)) ^ 2) ∂Q := by
  apply densitySquaredRisk_eq_lintegral_of_eq_withDensity
    (measurable_universalReducedLikelihood_explicit a b θ)
  · exact hestimator
  · exact (hasUniversalReducedDensity_iff_rebasedLikelihood
      ha hb θ).mp hQ

theorem HasUniversalReducedDensity.rebased_integrable_squaredError_of_finite
    {reference Q : Measure UniversalReducedObservation}
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (hQ : HasUniversalReducedDensity reference Q a b θ)
    {estimator : UniversalReducedObservation → ℝ}
    (hestimator : Measurable estimator)
    (hfinite :
      densitySquaredRisk
        (universalReducedObservationReference reference a b)
        (universalReducedLikelihood a b)
        (fun η : UniversalInteriorTheta => (η : ℝ))
        estimator θ ≠ ⊤) :
    Integrable (fun x => (estimator x - (θ : ℝ)) ^ 2) Q := by
  exact integrable_squaredError_of_densitySquaredRisk_ne_top
    (measurable_universalReducedLikelihood_explicit a b θ)
    hestimator
    ((hasUniversalReducedDensity_iff_rebasedLikelihood
      ha hb θ).mp hQ)
    hfinite

/-- The Graybill--Deal reduced baseline has integrable squared loss under
every finite reduced law: both the baseline `r` and the target `θ` lie in
the open unit interval, so the squared error is bounded by one. -/
theorem integrable_universalReducedBaseline_squaredError
    (Q : Measure UniversalReducedObservation) [IsFiniteMeasure Q]
    (θ : UniversalInteriorTheta) :
    Integrable
      (fun x : UniversalReducedObservation =>
        (universalReducedBaseline x - (θ : ℝ)) ^ 2) Q := by
  have hmeas :
      Measurable
        (fun x : UniversalReducedObservation =>
          (universalReducedBaseline x - (θ : ℝ)) ^ 2) := by
    unfold universalReducedBaseline UniversalReducedObservation.r
    fun_prop
  apply Integrable.of_bound hmeas.aestronglyMeasurable 1
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have habs :
      |universalReducedBaseline x - (θ : ℝ)| < 1 := by
    apply abs_lt.mpr
    unfold universalReducedBaseline
    constructor
    · linarith [x.r_pos, θ.property.2]
    · linarith [x.r_lt_one, θ.property.1]
  have hsquare :
      (universalReducedBaseline x - (θ : ℝ)) ^ 2
        < (1 : ℝ) ^ 2 := by
    exact sq_lt_sq.mpr (by simpa using habs)
  norm_num at hsquare ⊢
  exact hsquare.le

/-- Consequently, the rebased dominated risk of the baseline is finite
whenever the concrete risk-weighted reduced law is finite. -/
theorem HasUniversalReducedDensity.rebased_baselineRisk_ne_top
    {reference Q : Measure UniversalReducedObservation}
    [IsFiniteMeasure Q]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (hQ : HasUniversalReducedDensity reference Q a b θ) :
    densitySquaredRisk
        (universalReducedObservationReference reference a b)
        (universalReducedLikelihood a b)
        (fun η : UniversalInteriorTheta => (η : ℝ))
        universalReducedBaseline θ ≠ ⊤ := by
  have hbaseline :
      Measurable universalReducedBaseline := by
    unfold universalReducedBaseline UniversalReducedObservation.r
    fun_prop
  exact densitySquaredRisk_ne_top_of_integrable_squaredError
    (measurable_universalReducedLikelihood_explicit a b θ)
    hbaseline
    ((hasUniversalReducedDensity_iff_rebasedLikelihood
      ha hb θ).mp hQ)
    (integrable_universalReducedBaseline_squaredError Q θ)

theorem HasUniversalReducedDensity.rebased_measureSquaredRisk_le
    {reference Q : Measure UniversalReducedObservation}
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (hQ : HasUniversalReducedDensity reference Q a b θ)
    {candidate baseline : UniversalReducedObservation → ℝ}
    (hcandidate : Measurable candidate)
    (hbaseline : Measurable baseline)
    (hbaselineFinite :
      densitySquaredRisk
        (universalReducedObservationReference reference a b)
        (universalReducedLikelihood a b)
        (fun η : UniversalInteriorTheta => (η : ℝ))
        baseline θ ≠ ⊤)
    (hle :
      densitySquaredRisk
          (universalReducedObservationReference reference a b)
          (universalReducedLikelihood a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          candidate θ
        ≤
      densitySquaredRisk
          (universalReducedObservationReference reference a b)
          (universalReducedLikelihood a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          baseline θ) :
    measureSquaredRisk Q
        (fun η : UniversalInteriorTheta => (η : ℝ))
        candidate θ
      ≤
    measureSquaredRisk Q
        (fun η : UniversalInteriorTheta => (η : ℝ))
        baseline θ := by
  exact measureSquaredRisk_le_of_densitySquaredRisk_le
    (measurable_universalReducedLikelihood_explicit a b θ)
    hcandidate hbaseline
    ((hasUniversalReducedDensity_iff_rebasedLikelihood
      ha hb θ).mp hQ)
    hbaselineFinite hle

theorem HasUniversalReducedDensity.rebased_measureSquaredRisk_lt
    {reference Q : Measure UniversalReducedObservation}
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (hQ : HasUniversalReducedDensity reference Q a b θ)
    {candidate baseline : UniversalReducedObservation → ℝ}
    (hcandidate : Measurable candidate)
    (hbaseline : Measurable baseline)
    (hbaselineFinite :
      densitySquaredRisk
        (universalReducedObservationReference reference a b)
        (universalReducedLikelihood a b)
        (fun η : UniversalInteriorTheta => (η : ℝ))
        baseline θ ≠ ⊤)
    (hlt :
      densitySquaredRisk
          (universalReducedObservationReference reference a b)
          (universalReducedLikelihood a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          candidate θ
        <
      densitySquaredRisk
          (universalReducedObservationReference reference a b)
          (universalReducedLikelihood a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          baseline θ) :
    measureSquaredRisk Q
        (fun η : UniversalInteriorTheta => (η : ℝ))
        candidate θ
      <
    measureSquaredRisk Q
        (fun η : UniversalInteriorTheta => (η : ℝ))
        baseline θ := by
  exact measureSquaredRisk_lt_of_densitySquaredRisk_lt
    (measurable_universalReducedLikelihood_explicit a b θ)
    hcandidate hbaseline
    ((hasUniversalReducedDensity_iff_rebasedLikelihood
      ha hb θ).mp hQ)
    hbaselineFinite hlt

theorem HasUniversalReducedDensity.rebased_measureSquaredRisk_le_of_finiteLaw
    {reference Q : Measure UniversalReducedObservation}
    [IsFiniteMeasure Q]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (hQ : HasUniversalReducedDensity reference Q a b θ)
    {candidate : UniversalReducedObservation → ℝ}
    (hcandidate : Measurable candidate)
    (hle :
      densitySquaredRisk
          (universalReducedObservationReference reference a b)
          (universalReducedLikelihood a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          candidate θ
        ≤
      densitySquaredRisk
          (universalReducedObservationReference reference a b)
          (universalReducedLikelihood a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          universalReducedBaseline θ) :
    measureSquaredRisk Q
        (fun η : UniversalInteriorTheta => (η : ℝ))
        candidate θ
      ≤
    measureSquaredRisk Q
        (fun η : UniversalInteriorTheta => (η : ℝ))
        universalReducedBaseline θ := by
  have hbaseline :
      Measurable universalReducedBaseline := by
    unfold universalReducedBaseline UniversalReducedObservation.r
    fun_prop
  exact hQ.rebased_measureSquaredRisk_le ha hb θ
    hcandidate hbaseline
    (hQ.rebased_baselineRisk_ne_top ha hb θ) hle

theorem HasUniversalReducedDensity.rebased_measureSquaredRisk_lt_of_finiteLaw
    {reference Q : Measure UniversalReducedObservation}
    [IsFiniteMeasure Q]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (hQ : HasUniversalReducedDensity reference Q a b θ)
    {candidate : UniversalReducedObservation → ℝ}
    (hcandidate : Measurable candidate)
    (hlt :
      densitySquaredRisk
          (universalReducedObservationReference reference a b)
          (universalReducedLikelihood a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          candidate θ
        <
      densitySquaredRisk
          (universalReducedObservationReference reference a b)
          (universalReducedLikelihood a b)
          (fun η : UniversalInteriorTheta => (η : ℝ))
          universalReducedBaseline θ) :
    measureSquaredRisk Q
        (fun η : UniversalInteriorTheta => (η : ℝ))
        candidate θ
      <
    measureSquaredRisk Q
        (fun η : UniversalInteriorTheta => (η : ℝ))
        universalReducedBaseline θ := by
  have hbaseline :
      Measurable universalReducedBaseline := by
    unfold universalReducedBaseline UniversalReducedObservation.r
    fun_prop
  exact hQ.rebased_measureSquaredRisk_lt ha hb θ
    hcandidate hbaseline
    (hQ.rebased_baselineRisk_ne_top ha hb θ) hlt

/-! ## Abstract weighted-pushforward bridge

This is the exact ordinary proposition that the future raw
change-of-variables theorem must establish. -/

/-- `Q` is the pushforward of the raw law after weighting by `D²`. -/
def HasWeightedReducedLaw
    (P : Measure Ω) (D : Ω → ℝ) (Z : Ω → X)
    (Q : Measure X) : Prop :=
  Q =
    Measure.map Z
      (P.withDensity (fun ω => ENNReal.ofReal (D ω ^ 2)))

/-- A square-integrable weight makes the unnormalized weighted
pushforward a finite measure.  Thus the finite-law hypothesis used above
is not an extra normalization assumption. -/
theorem HasWeightedReducedLaw.isFiniteMeasure
    {P : Measure Ω} {D : Ω → ℝ} {Z : Ω → X}
    {Q : Measure X}
    (hQ : HasWeightedReducedLaw P D Z Q)
    (hDsq : Integrable (fun ω => D ω ^ 2) P) :
    IsFiniteMeasure Q := by
  rw [hQ]
  have hdensity_ne_top :
      (∫⁻ ω, ENNReal.ofReal (D ω ^ 2) ∂P) ≠ ⊤ := by
    exact lt_top_iff_ne_top.mp
      ((hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall fun ω => sq_nonneg _)).mp
          hDsq.hasFiniteIntegral)
  letI : IsFiniteMeasure
      (P.withDensity (fun ω => ENNReal.ofReal (D ω ^ 2))) :=
    isFiniteMeasure_withDensity hdensity_ne_top
  exact Measure.isFiniteMeasure_map _ _

theorem HasWeightedReducedLaw.lintegral_eq
    {P : Measure Ω} {D : Ω → ℝ} {Z : Ω → X}
    {Q : Measure X}
    (hQ : HasWeightedReducedLaw P D Z Q)
    (hD : Measurable D) (hZ : Measurable Z)
    {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂Q
      =
    ∫⁻ ω, ENNReal.ofReal (D ω ^ 2) * g (Z ω) ∂P := by
  rw [hQ, lintegral_map hg hZ,
    show (fun ω => g (Z ω)) = g ∘ Z by rfl]
  rw [lintegral_withDensity_eq_lintegral_mul
      P (hD.pow_const 2).ennreal_ofReal (hg.comp hZ)]
  rfl

/-- Integrability under the risk-weighted reduced law gives exactly the
weighted raw integrability needed by the oracle risk decomposition. -/
theorem HasWeightedReducedLaw.integrable_weighted_comp
    {P : Measure Ω} {D : Ω → ℝ} {Z : Ω → X}
    {Q : Measure X}
    (hQ : HasWeightedReducedLaw P D Z Q)
    (hD : Measurable D) (hZ : Measurable Z)
    {g : X → ℝ} (hg : Measurable g)
    (hg_integrable : Integrable g Q) :
    Integrable (fun ω => D ω ^ 2 * g (Z ω)) P := by
  have hg_map :
      AEStronglyMeasurable g
        (Measure.map Z
          (P.withDensity (fun ω => ENNReal.ofReal (D ω ^ 2)))) :=
    hg.aestronglyMeasurable
  have hcomp :
      Integrable (g ∘ Z)
        (P.withDensity (fun ω => ENNReal.ofReal (D ω ^ 2))) := by
    apply (integrable_map_measure hg_map hZ.aemeasurable).mp
    have hg_integrable' := hg_integrable
    rw [hQ] at hg_integrable'
    exact hg_integrable'
  have hweighted :
      Integrable
        (fun ω =>
          Real.toNNReal (D ω ^ 2) • (g ∘ Z) ω) P := by
    apply (integrable_withDensity_iff_integrable_smul
      (by fun_prop : Measurable
        (fun ω => Real.toNNReal (D ω ^ 2)))).mp
    exact hcomp
  apply hweighted.congr
  filter_upwards [] with ω
  rw [NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (sq_nonneg (D ω))]
  rfl

theorem HasWeightedReducedLaw.integral_eq
    {P : Measure Ω} {D : Ω → ℝ} {Z : Ω → X}
    {Q : Measure X}
    (hQ : HasWeightedReducedLaw P D Z Q)
    (hD : Measurable D) (hZ : Measurable Z)
    {g : X → ℝ} (hg : Measurable g) :
    ∫ x, g x ∂Q = ∫ ω, D ω ^ 2 * g (Z ω) ∂P := by
  rw [hQ]
  have hg_map :
      AEStronglyMeasurable g
        (Measure.map Z
          (P.withDensity (fun ω => ENNReal.ofReal (D ω ^ 2)))) :=
    hg.aestronglyMeasurable
  rw [integral_map hZ.aemeasurable hg_map]
  change
    (∫ x, (g ∘ Z) x
      ∂P.withDensity
        (fun ω => (↑(Real.toNNReal (D ω ^ 2)) : ℝ≥0∞)))
      =
    ∫ ω, D ω ^ 2 * g (Z ω) ∂P
  rw [integral_withDensity_eq_integral_smul
    (by fun_prop : Measurable
      (fun ω => Real.toNNReal (D ω ^ 2))) (g ∘ Z)]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (sq_nonneg (D ω))]
  rfl

/-! ## The literal raw reduced-risk integrals -/

/-- Restrict a rule on the ambient pair of coordinates to the open
reduced observation space. -/
def universalReducedRuleOnObservation
    (δ : ℝ × ℝ → ℝ) (x : UniversalReducedObservation) : ℝ :=
  δ x.1

theorem measurable_universalReducedRuleOnObservation
    {δ : ℝ × ℝ → ℝ} (hδ : Measurable δ) :
    Measurable (universalReducedRuleOnObservation δ) := by
  unfold universalReducedRuleOnObservation
  exact hδ.comp measurable_subtype_coe

theorem universalReducedRuleOnObservation_first
    (x : UniversalReducedObservation) :
    universalReducedRuleOnObservation (fun z : ℝ × ℝ => z.1) x
      =
    universalReducedBaseline x := by
  rfl

/-- Conditional on the weighted-pushforward law and the a.e. coordinate
identification, reduced-law integrability supplies the candidate
quadratic integrability assumption of `UniversalRawRiskTransport`. -/
theorem HasWeightedReducedLaw.integrable_universalRawReduced_quadratic
    {ν₁ ν₂ : ℕ}
    {Xraw : Fin (ν₁ + 1) → Ω → ℝ}
    {Yraw : Fin (ν₂ + 1) → Ω → ℝ}
    {P : Measure Ω} {Q : Measure UniversalReducedObservation}
    {Z : Ω → UniversalReducedObservation}
    (hQ :
      HasWeightedReducedLaw P
        (meanDifferenceU ν₁ ν₂ Xraw Yraw) Z Q)
    (hX : ∀ i, Measurable (Xraw i))
    (hY : ∀ j, Measurable (Yraw j))
    (hZ : Measurable Z)
    (hcoords :
      ∀ᵐ ω ∂P,
        (Z ω : ℝ × ℝ) =
          universalRawReducedCoordinates ν₁ ν₂ Xraw Yraw ω)
    {δ : ℝ × ℝ → ℝ} (hδ : Measurable δ)
    (θ : ℝ)
    (hint :
      Integrable
        (fun x : UniversalReducedObservation =>
          (universalReducedRuleOnObservation δ x - θ) ^ 2) Q) :
    Integrable
      (fun ω =>
        meanDifferenceU ν₁ ν₂ Xraw Yraw ω ^ 2
          * (universalRawReducedWeight δ ν₁ ν₂ Xraw Yraw ω - θ) ^ 2) P := by
  have hgmeas :
      Measurable
        (fun x : UniversalReducedObservation =>
          (universalReducedRuleOnObservation δ x - θ) ^ 2) :=
    ((measurable_universalReducedRuleOnObservation hδ).sub
      measurable_const).pow_const 2
  have hweighted :=
    hQ.integrable_weighted_comp
      (measurable_meanDifferenceU hX hY) hZ
      hgmeas
      hint
  apply hweighted.congr
  filter_upwards [hcoords] with ω hω
  unfold universalReducedRuleOnObservation
    universalRawReducedWeight
  rw [hω]

/-- The same conversion for the Graybill--Deal baseline rule. -/
theorem HasWeightedReducedLaw.integrable_universalRawGraybillDeal_quadratic
    {ν₁ ν₂ : ℕ}
    {Xraw : Fin (ν₁ + 1) → Ω → ℝ}
    {Yraw : Fin (ν₂ + 1) → Ω → ℝ}
    {P : Measure Ω} {Q : Measure UniversalReducedObservation}
    {Z : Ω → UniversalReducedObservation}
    (hQ :
      HasWeightedReducedLaw P
        (meanDifferenceU ν₁ ν₂ Xraw Yraw) Z Q)
    (hX : ∀ i, Measurable (Xraw i))
    (hY : ∀ j, Measurable (Yraw j))
    (hZ : Measurable Z)
    (hcoords :
      ∀ᵐ ω ∂P,
        (Z ω : ℝ × ℝ) =
          universalRawReducedCoordinates ν₁ ν₂ Xraw Yraw ω)
    (θ : ℝ)
    (hint :
      Integrable
        (fun x : UniversalReducedObservation =>
          (universalReducedBaseline x - θ) ^ 2) Q) :
    Integrable
      (fun ω =>
        meanDifferenceU ν₁ ν₂ Xraw Yraw ω ^ 2
          * (universalRawGraybillDealWeight ν₁ ν₂ Xraw Yraw ω - θ) ^ 2) P := by
  have hbaseline :
      Measurable universalReducedBaseline := by
    unfold universalReducedBaseline UniversalReducedObservation.r
    fun_prop
  have hweighted :=
    hQ.integrable_weighted_comp
      (measurable_meanDifferenceU hX hY) hZ
      (by fun_prop : Measurable
        (fun x : UniversalReducedObservation =>
          (universalReducedBaseline x - θ) ^ 2))
      hint
  apply hweighted.congr
  filter_upwards [hcoords] with ω hω
  change
    meanDifferenceU ν₁ ν₂ Xraw Yraw ω ^ 2
        * (((Z ω : ℝ × ℝ).1) - θ) ^ 2
      =
    meanDifferenceU ν₁ ν₂ Xraw Yraw ω ^ 2
        * (universalRawGraybillDealWeight
          ν₁ ν₂ Xraw Yraw ω - θ) ^ 2
  rw [hω]
  rfl

theorem HasWeightedReducedLaw.measureSquaredRisk_eq_universalRawReduced
    {ν₁ ν₂ : ℕ}
    {Xraw : Fin (ν₁ + 1) → Ω → ℝ}
    {Yraw : Fin (ν₂ + 1) → Ω → ℝ}
    {P : Measure Ω} {Q : Measure UniversalReducedObservation}
    {Z : Ω → UniversalReducedObservation}
    (hQ :
      HasWeightedReducedLaw P
        (meanDifferenceU ν₁ ν₂ Xraw Yraw) Z Q)
    (hX : ∀ i, Measurable (Xraw i))
    (hY : ∀ j, Measurable (Yraw j))
    (hZ : Measurable Z)
    (hcoords :
      ∀ᵐ ω ∂P,
        (Z ω : ℝ × ℝ) =
          universalRawReducedCoordinates ν₁ ν₂ Xraw Yraw ω)
    {δ : ℝ × ℝ → ℝ} (hδ : Measurable δ)
    (θ : UniversalInteriorTheta) :
    measureSquaredRisk Q
        (fun η : UniversalInteriorTheta => (η : ℝ))
        (universalReducedRuleOnObservation δ) θ
      =
    universalRawReducedSquaredRisk (θ : ℝ)
      δ ν₁ ν₂ Xraw Yraw P := by
  unfold measureSquaredRisk universalRawReducedSquaredRisk
  have hgmeas :
      Measurable
        (fun x : UniversalReducedObservation =>
          (universalReducedRuleOnObservation δ x - (θ : ℝ)) ^ 2) :=
    ((measurable_universalReducedRuleOnObservation hδ).sub
      measurable_const).pow_const 2
  have heq := hQ.integral_eq
    (measurable_meanDifferenceU hX hY) hZ
    (g := fun x : UniversalReducedObservation =>
      (universalReducedRuleOnObservation δ x - (θ : ℝ)) ^ 2)
    hgmeas
  rw [heq]
  apply integral_congr_ae
  filter_upwards [hcoords] with ω hω
  unfold universalReducedRuleOnObservation
    universalRawReducedWeight
  rw [hω]

theorem HasWeightedReducedLaw.measureSquaredRisk_eq_universalRawGraybillDeal
    {ν₁ ν₂ : ℕ}
    {Xraw : Fin (ν₁ + 1) → Ω → ℝ}
    {Yraw : Fin (ν₂ + 1) → Ω → ℝ}
    {P : Measure Ω} {Q : Measure UniversalReducedObservation}
    {Z : Ω → UniversalReducedObservation}
    (hQ :
      HasWeightedReducedLaw P
        (meanDifferenceU ν₁ ν₂ Xraw Yraw) Z Q)
    (hX : ∀ i, Measurable (Xraw i))
    (hY : ∀ j, Measurable (Yraw j))
    (hZ : Measurable Z)
    (hcoords :
      ∀ᵐ ω ∂P,
        (Z ω : ℝ × ℝ) =
          universalRawReducedCoordinates ν₁ ν₂ Xraw Yraw ω)
    (θ : UniversalInteriorTheta) :
    measureSquaredRisk Q
        (fun η : UniversalInteriorTheta => (η : ℝ))
        universalReducedBaseline θ
      =
    universalRawGraybillDealReducedSquaredRisk (θ : ℝ)
      ν₁ ν₂ Xraw Yraw P := by
  have hbaseline :
      Measurable universalReducedBaseline := by
    unfold universalReducedBaseline UniversalReducedObservation.r
    fun_prop
  unfold measureSquaredRisk
    universalRawGraybillDealReducedSquaredRisk
  have heq := hQ.integral_eq
    (measurable_meanDifferenceU hX hY) hZ
    (g := fun x : UniversalReducedObservation =>
      (universalReducedBaseline x - (θ : ℝ)) ^ 2)
    (by fun_prop)
  rw [heq]
  apply integral_congr_ae
  filter_upwards [hcoords] with ω hω
  change
    meanDifferenceU ν₁ ν₂ Xraw Yraw ω ^ 2
        * (((Z ω : ℝ × ℝ).1) - (θ : ℝ)) ^ 2
      =
    meanDifferenceU ν₁ ν₂ Xraw Yraw ω ^ 2
        * (universalRawGraybillDealWeight
          ν₁ ν₂ Xraw Yraw ω - (θ : ℝ)) ^ 2
  rw [hω]
  rfl

end

end GraybillDeal
