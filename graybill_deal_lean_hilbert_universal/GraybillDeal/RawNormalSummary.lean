import GraybillDeal.BetaGamma
import GraybillDeal.Cochran13
import GraybillDeal.GaussianMeanBridge
import GraybillDeal.NormalSample
import GraybillDeal.RawCoordinates
import GraybillDeal.SummaryTransform

/-!
# Canonical component laws from two raw normal samples

This file assembles every part of the raw-sample probability bridge except
the fixed-size Cochran theorem.  Its sole distributional inputs beyond the
raw normal model are the two marginal laws

`RSS_g / variance_g ~ Gamma(6, 1/2)`.

From those it derives the beta ratio law, the gamma sum law, the gamma law
of the standardized squared mean difference, the internal independence of
both pairs, independence of the mean pair from the residual pair, and the
centered-error moment conditions.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The standardized residual sum of squares of raw sample `g`. -/
def normalRawU13
    (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin 13 → Ω → ℝ) (g : Fin 2) : Ω → ℝ :=
  scaledResidualSumSquares13 (variance g) (X g)

/-- The beta ratio coordinate constructed from the two raw residual sums. -/
def normalRawP13
    (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin 13 → Ω → ℝ) : Ω → ℝ :=
  fun ω =>
    normalRawU13 variance X 0 ω
      / (normalRawU13 variance X 0 ω + normalRawU13 variance X 1 ω)

/-- The gamma sum coordinate constructed from the two raw residual sums. -/
def normalRawL13
    (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin 13 → Ω → ℝ) : Ω → ℝ :=
  fun ω =>
    normalRawU13 variance X 0 ω + normalRawU13 variance X 1 ω

/-- Sum of the two population variances. -/
def normalVarianceSum13 (variance : Fin 2 → NNReal) : ℝ :=
  (variance 0 : ℝ) + variance 1

/--
All canonical law and block-independence conclusions produced by the raw
normal model once the two marginal Cochran laws are available.
-/
structure RawNormalSummaryLaws13
    (μ : ℝ) (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin 13 → Ω → ℝ) (Pmeasure : Measure Ω) : Prop where
  p_law :
    HasLaw (normalRawP13 variance X)
      (betaMeasure 6 6) Pmeasure
  l_law :
    HasLaw (normalRawL13 variance X)
      (gammaMeasure 12 (1 / 2)) Pmeasure
  v_law :
    HasLaw
      (fun ω =>
        standardizedDifference13 (normalVarianceSum13 variance)
          (meanDifference13 X ω))
      (gammaMeasure (1 / 2) (1 / 2)) Pmeasure
  p_l_indep :
    IndepFun (normalRawP13 variance X) (normalRawL13 variance X) Pmeasure
  centered_d_indep :
    IndepFun
      (oracleCenteredError13 μ (oracleVarianceWeight13 variance) X)
      (meanDifference13 X) Pmeasure
  centeredD_pL_indep :
    IndepFun
      (fun ω =>
        (oracleCenteredError13 μ (oracleVarianceWeight13 variance) X ω,
          meanDifference13 X ω))
      (fun ω =>
        (normalRawP13 variance X ω, normalRawL13 variance X ω))
      Pmeasure
  summary_iIndep :
    iIndepFun
      ![
        oracleCenteredError13 μ (oracleVarianceWeight13 variance) X,
        meanDifference13 X,
        normalRawP13 variance X,
        normalRawL13 variance X]
      Pmeasure
  centered_sq :
    Integrable
      (fun ω =>
        oracleCenteredError13 μ (oracleVarianceWeight13 variance) X ω ^ 2)
      Pmeasure
  centered_zero :
    (∫ ω,
      oracleCenteredError13 μ (oracleVarianceWeight13 variance) X ω
        ∂Pmeasure) = 0

/--
Assembly theorem with the fixed-13 Cochran laws kept explicit.

After `Cochran13.lean` proves the two `hU` hypotheses from
`TwoNormalSamples13`, this theorem has no remaining probabilistic
assumptions beyond positivity of the population variances.
-/
theorem rawNormalSummaryLaws13_of_scaledResidual_gamma
    {X : Fin 2 → Fin 13 → Ω → ℝ}
    {Pmeasure : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}
    (h : TwoNormalSamples13 X Pmeasure μ variance)
    (hXmeas : ∀ g i, Measurable (X g i))
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ))
    (hU :
      ∀ g,
        HasLaw (normalRawU13 variance X g)
          (gammaMeasure 6 (1 / 2)) Pmeasure) :
    RawNormalSummaryLaws13 μ variance X Pmeasure := by
  letI : IsProbabilityMeasure Pmeasure := h.indep.isProbabilityMeasure
  have hUindep :
      IndepFun (normalRawU13 variance X 0)
        (normalRawU13 variance X 1) Pmeasure := by
    have hout := h.indepFun_residualSumSquares.comp
      (show Measurable (fun r : ℝ => r / (variance 0 : ℝ)) by fun_prop)
      (show Measurable (fun r : ℝ => r / (variance 1 : ℝ)) by fun_prop)
    apply hout.congr
    · filter_upwards [] with ω
      rfl
    · filter_upwards [] with ω
      rfl
  obtain ⟨hP, hL, hPL⟩ :=
    betaGamma_component_laws_and_indep
      (normalRawU13 variance X 0)
      (normalRawU13 variance X 1) Pmeasure
      (hU 0) (hU 1) hUindep
  have hvarianceSum :
      0 < normalVarianceSum13 variance :=
    add_pos hvariance₀ hvariance₁
  have hD :
      HasLaw (meanDifference13 X)
        (gaussianReal 0
          (normalVarianceSum13 variance / 13).toNNReal) Pmeasure := by
    convert h.hasLaw_meanDifference using 1
    congr 1
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by positivity)]
    simp [normalVarianceSum13]
  have hV :=
    hasLaw_standardizedDifference13_of_gaussian
      (normalVarianceSum13 variance) (meanDifference13 X) Pmeasure
      hvarianceSum hD
  have hcenteredD_U :
      IndepFun
        (fun ω =>
          (oracleCenteredError13 μ (oracleVarianceWeight13 variance) X ω,
            meanDifference13 X ω))
        (fun ω =>
          (normalRawU13 variance X 0 ω, normalRawU13 variance X 1 ω))
        Pmeasure := by
    let meansToCenteredD : (Fin 2 → ℝ) → ℝ × ℝ := fun m =>
      (m 0 + oracleVarianceWeight13 variance * (m 1 - m 0) - μ,
        m 1 - m 0)
    let rssToU : (ℝ × ℝ) → ℝ × ℝ := fun r =>
      (r.1 / (variance 0 : ℝ), r.2 / (variance 1 : ℝ))
    have hblocks :=
      h.indepFun_sampleMeans_residualSumSquares.comp
        (show Measurable meansToCenteredD by
          dsimp only [meansToCenteredD]
          fun_prop)
        (show Measurable rssToU by
          dsimp only [rssToU]
          fun_prop)
    apply hblocks.congr
    · filter_upwards [] with ω
      rfl
    · filter_upwards [] with ω
      rfl
  have hcenteredD_pL :
      IndepFun
        (fun ω =>
          (oracleCenteredError13 μ (oracleVarianceWeight13 variance) X ω,
            meanDifference13 X ω))
        (fun ω =>
          (normalRawP13 variance X ω, normalRawL13 variance X ω))
        Pmeasure := by
    have hratioSum :=
      hcenteredD_U.comp measurable_id measurable_betaGammaRatioSum
    apply hratioSum.congr
    · filter_upwards [] with ω
      rfl
    · filter_upwards [] with ω
      rfl
  have hcenteredMeas :
      Measurable
        (oracleCenteredError13 μ (oracleVarianceWeight13 variance) X) :=
    measurable_oracleCenteredError13 hXmeas _ _
  have hDmeas : Measurable (meanDifference13 X) :=
    measurable_meanDifference13 hXmeas
  have hUmeas :
      ∀ g, Measurable (normalRawU13 variance X g) := by
    intro g
    exact measurable_scaledResidualSumSquares13 (hXmeas g) _
  obtain ⟨_, _, hsummary⟩ :=
    betaGamma_laws_and_iIndepFun_transformedSummary4_of_blocks
      (oracleCenteredError13 μ (oracleVarianceWeight13 variance) X)
      (meanDifference13 X)
      (normalRawU13 variance X 0)
      (normalRawU13 variance X 1)
      Pmeasure
      hcenteredMeas hDmeas (hUmeas 0) (hUmeas 1)
      (hU 0) (hU 1)
      (h.indepFun_oracleCenteredError_meanDifference hvarianceSum)
      hUindep hcenteredD_U
  have hcentered :=
    oracleCentered_integrable_sq_and_integral_zero13
      μ (variance 0) (variance 1)
      (sampleMean13 (X 0)) (sampleMean13 (X 1)) Pmeasure
      (h.hasLaw_sampleMean 0) (h.hasLaw_sampleMean 1)
  refine
    { p_law := ?_
      l_law := ?_
      v_law := hV
      p_l_indep := ?_
      centered_d_indep :=
        h.indepFun_oracleCenteredError_meanDifference hvarianceSum
      centeredD_pL_indep := hcenteredD_pL
      summary_iIndep := ?_
      centered_sq := ?_
      centered_zero := ?_ }
  · apply hP.congr
    filter_upwards [] with ω
    rfl
  · apply hL.congr
    filter_upwards [] with ω
    rfl
  · apply hPL.congr
    · filter_upwards [] with ω
      rfl
    · filter_upwards [] with ω
      rfl
  · apply hsummary.congr
    intro i
    fin_cases i <;>
      filter_upwards [] with ω <;>
        rfl
  · simpa [oracleCenteredError13, meanDifference13,
      oracleVarianceWeight13] using hcentered.1
  · simpa [oracleCenteredError13, meanDifference13,
      oracleVarianceWeight13] using hcentered.2

/--
All canonical component laws and mutual independence, derived directly from
two measurable raw normal samples of size thirteen.

The two calls to `hasLaw_scaledResidualSumSquares13` are the fixed-size
Cochran theorem; the preceding assembly theorem then supplies the beta,
gamma, squared-normal, and independence conclusions.
-/
theorem rawNormalSummaryLaws13_of_normal_samples
    {X : Fin 2 → Fin 13 → Ω → ℝ}
    {Pmeasure : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}
    (h : TwoNormalSamples13 X Pmeasure μ variance)
    (hXmeas : ∀ g i, Measurable (X g i))
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    RawNormalSummaryLaws13 μ variance X Pmeasure := by
  apply rawNormalSummaryLaws13_of_scaledResidual_gamma
    h hXmeas hvariance₀ hvariance₁
  intro g
  fin_cases g
  · exact h.hasLaw_scaledResidualSumSquares13 0 hvariance₀
  · exact h.hasLaw_scaledResidualSumSquares13 1 hvariance₁

end

end GraybillDeal
