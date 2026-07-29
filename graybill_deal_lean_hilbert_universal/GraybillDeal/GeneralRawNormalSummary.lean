import GraybillDeal.GeneralGaussianMeanBridge
import GraybillDeal.GeneralGaussianOracleBridge
import GraybillDeal.GeneralSummaryIndependence
import GraybillDeal.GeneralSummaryTransform

/-!
# Canonical summary laws from two arbitrary-size normal samples

This module assembles the canonical beta, gamma, and squared-normal
coordinates from two raw normal samples with residual degrees of freedom
`ν` (and therefore sample size `ν + 1`).
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The standardized residual sum of squares of raw sample `g`. -/
def normalRawUN
    (ν : ℕ) (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) (g : Fin 2) : Ω → ℝ :=
  scaledResidualSumSquaresN ν (variance g) (X g)

/-- The beta ratio coordinate constructed from the two residual sums. -/
def normalRawPN
    (ν : ℕ) (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) : Ω → ℝ :=
  fun ω =>
    normalRawUN ν variance X 0 ω
      / (normalRawUN ν variance X 0 ω
        + normalRawUN ν variance X 1 ω)

/-- The gamma sum coordinate constructed from the two residual sums. -/
def normalRawLN
    (ν : ℕ) (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) : Ω → ℝ :=
  fun ω =>
    normalRawUN ν variance X 0 ω + normalRawUN ν variance X 1 ω

/-- Sum of the two population variances. -/
def normalVarianceSumN (variance : Fin 2 → NNReal) : ℝ :=
  (variance 0 : ℝ) + variance 1

/-- The standardized squared sample-mean difference. -/
def normalRawVN
    (ν : ℕ) (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) : Ω → ℝ :=
  fun ω =>
    generalStandardizedDifference (ν : ℝ)
      (normalVarianceSumN variance) (meanDifferenceN ν X ω)

/-- The known-variance oracle estimator error, centered at the common mean. -/
def oracleCenteredErrorN
    (ν : ℕ) (μ : ℝ) (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) : Ω → ℝ :=
  fun ω =>
    sampleMeanN ν (X 0) ω
      + oracleVarianceWeightN variance * meanDifferenceN ν X ω - μ

@[fun_prop]
theorem measurable_normalRawUN
    {ν : ℕ} {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
    (hX : ∀ g i, Measurable (X g i)) (g : Fin 2) :
    Measurable (normalRawUN ν variance X g) :=
  measurable_scaledResidualSumSquaresN (hX g) _

@[fun_prop]
theorem measurable_normalRawPN
    {ν : ℕ} {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
    (hX : ∀ g i, Measurable (X g i)) :
    Measurable (normalRawPN ν variance X) := by
  unfold normalRawPN
  fun_prop

@[fun_prop]
theorem measurable_normalRawLN
    {ν : ℕ} {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
    (hX : ∀ g i, Measurable (X g i)) :
    Measurable (normalRawLN ν variance X) := by
  unfold normalRawLN
  fun_prop

@[fun_prop]
theorem measurable_normalRawVN
    {ν : ℕ} {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
    (hX : ∀ g i, Measurable (X g i)) :
    Measurable (normalRawVN ν variance X) := by
  unfold normalRawVN
  fun_prop

@[fun_prop]
theorem measurable_oracleCenteredErrorN
    {ν : ℕ} {μ : ℝ} {variance : Fin 2 → NNReal}
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
    (hX : ∀ g i, Measurable (X g i)) :
    Measurable (oracleCenteredErrorN ν μ variance X) := by
  unfold oracleCenteredErrorN
  fun_prop

/--
All canonical component laws and independence facts assembled from the raw
normal model at residual degrees of freedom `ν`.
-/
structure RawNormalSummaryLawsN
    (ν : ℕ) (μ : ℝ) (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin (ν + 1) → Ω → ℝ)
    (Pmeasure : Measure Ω) : Prop where
  p_law :
    HasLaw (normalRawPN ν variance X)
      (betaMeasure ((ν : ℝ) / 2) ((ν : ℝ) / 2)) Pmeasure
  l_law :
    HasLaw (normalRawLN ν variance X)
      (gammaMeasure (ν : ℝ) (1 / 2)) Pmeasure
  v_law :
    HasLaw (normalRawVN ν variance X)
      (gammaMeasure (1 / 2) (1 / 2)) Pmeasure
  p_l_indep :
    IndepFun (normalRawPN ν variance X)
      (normalRawLN ν variance X) Pmeasure
  p_lv_indep :
    IndepFun (normalRawPN ν variance X)
      (fun ω =>
        (normalRawLN ν variance X ω, normalRawVN ν variance X ω))
      Pmeasure
  v_l_indep :
    IndepFun (normalRawVN ν variance X)
      (normalRawLN ν variance X) Pmeasure
  centered_d_indep :
    IndepFun (oracleCenteredErrorN ν μ variance X)
      (meanDifferenceN ν X) Pmeasure
  centeredD_pL_indep :
    IndepFun
      (fun ω =>
        (oracleCenteredErrorN ν μ variance X ω,
          meanDifferenceN ν X ω))
      (fun ω =>
        (normalRawPN ν variance X ω, normalRawLN ν variance X ω))
      Pmeasure
  centered_d_p_l_indep :
    IndepFun (oracleCenteredErrorN ν μ variance X)
      (fun ω =>
        (meanDifferenceN ν X ω,
          (normalRawPN ν variance X ω,
            normalRawLN ν variance X ω)))
      Pmeasure
  summary_iIndep :
    iIndepFun
      ![
        oracleCenteredErrorN ν μ variance X,
        meanDifferenceN ν X,
        normalRawPN ν variance X,
        normalRawLN ν variance X]
      Pmeasure
  centered_sq :
    Integrable
      (fun ω => oracleCenteredErrorN ν μ variance X ω ^ 2)
      Pmeasure
  centered_zero :
    (∫ ω, oracleCenteredErrorN ν μ variance X ω ∂Pmeasure) = 0

/--
Raw-normal summary assembly with the two generic Cochran laws kept explicit.
-/
theorem rawNormalSummaryLawsN_of_scaledResidual_gamma
    (ν : ℕ) (hν : 9 ≤ ν)
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
    {Pmeasure : Measure Ω} {μ : ℝ}
    {variance : Fin 2 → NNReal}
    (h : TwoNormalSamplesN ν X Pmeasure μ variance)
    (hXmeas : ∀ g i, Measurable (X g i))
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ))
    (hU :
      ∀ g,
        HasLaw (normalRawUN ν variance X g)
          (gammaMeasure ((ν : ℝ) / 2) (1 / 2)) Pmeasure) :
    RawNormalSummaryLawsN ν μ variance X Pmeasure := by
  letI : IsProbabilityMeasure Pmeasure :=
    h.indep.isProbabilityMeasure
  have hUindep :
      IndepFun (normalRawUN ν variance X 0)
        (normalRawUN ν variance X 1) Pmeasure := by
    have hout := h.indepFun_residualSumSquares.comp
      (show Measurable (fun r : ℝ => r / (variance 0 : ℝ)) by
        fun_prop)
      (show Measurable (fun r : ℝ => r / (variance 1 : ℝ)) by
        fun_prop)
    apply hout.congr
    · filter_upwards [] with ω
      rfl
    · filter_upwards [] with ω
      rfl
  have hvarianceSum : 0 < normalVarianceSumN variance :=
    add_pos hvariance₀ hvariance₁
  have hV :
      HasLaw (normalRawVN ν variance X)
        (gammaMeasure (1 / 2) (1 / 2)) Pmeasure := by
    change
      HasLaw
        (fun ω =>
          generalStandardizedDifference (ν : ℝ)
            ((variance 0 : ℝ) + variance 1)
            (meanDifferenceN ν X ω))
        (gammaMeasure (1 / 2) (1 / 2)) Pmeasure
    exact h.hasLaw_generalStandardizedMeanDifference hvarianceSum
  have hCD :
      IndepFun (oracleCenteredErrorN ν μ variance X)
        (meanDifferenceN ν X) Pmeasure := by
    have hout :=
      indepFun_oracleCentered_meanDifferenceN
        ν μ (variance 0) (variance 1)
        (sampleMeanN ν (X 0)) (sampleMeanN ν (X 1)) Pmeasure
        hvarianceSum
        (h.hasLaw_sampleMean 0) (h.hasLaw_sampleMean 1)
        h.indepFun_sampleMeans01
    change
      IndepFun
        (fun ω =>
          sampleMeanN ν (X 0) ω
            + ((variance 0 : ℝ) /
                ((variance 0 : ℝ) + variance 1))
              * (sampleMeanN ν (X 1) ω - sampleMeanN ν (X 0) ω)
            - μ)
        (fun ω =>
          sampleMeanN ν (X 1) ω - sampleMeanN ν (X 0) ω)
        Pmeasure
    exact hout
  have hcenteredD_U :
      IndepFun
        (fun ω =>
          (oracleCenteredErrorN ν μ variance X ω,
            meanDifferenceN ν X ω))
        (fun ω =>
          (normalRawUN ν variance X 0 ω,
            normalRawUN ν variance X 1 ω))
        Pmeasure := by
    let meansToCenteredD : (Fin 2 → ℝ) → ℝ × ℝ := fun m =>
      (m 0 + oracleVarianceWeightN variance * (m 1 - m 0) - μ,
        m 1 - m 0)
    let rssToU : ℝ × ℝ → ℝ × ℝ := fun r =>
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
          (oracleCenteredErrorN ν μ variance X ω,
            meanDifferenceN ν X ω))
        (fun ω =>
          (normalRawPN ν variance X ω,
            normalRawLN ν variance X ω))
        Pmeasure := by
    have hratioSum :=
      hcenteredD_U.comp measurable_id measurable_betaGammaRatioSum
    apply hratioSum.congr
    · filter_upwards [] with ω
      rfl
    · filter_upwards [] with ω
      rfl
  have hcenteredMeas :
      Measurable (oracleCenteredErrorN ν μ variance X) :=
    measurable_oracleCenteredErrorN hXmeas
  have hDmeas : Measurable (meanDifferenceN ν X) :=
    measurable_meanDifferenceN hXmeas
  have hUmeas :
      ∀ g, Measurable (normalRawUN ν variance X g) :=
    fun g => measurable_normalRawUN hXmeas g
  obtain ⟨hP, hL, hsummaryRaw⟩ :=
    betaGamma_laws_and_iIndepFun_generalTransformedSummary4_of_blocks
      ν hν
      (oracleCenteredErrorN ν μ variance X)
      (meanDifferenceN ν X)
      (normalRawUN ν variance X 0)
      (normalRawUN ν variance X 1)
      Pmeasure
      hcenteredMeas hDmeas (hUmeas 0) (hUmeas 1)
      (hU 0) (hU 1) hCD hUindep hcenteredD_U
  have hsummary :
      iIndepFun
        ![
          oracleCenteredErrorN ν μ variance X,
          meanDifferenceN ν X,
          normalRawPN ν variance X,
          normalRawLN ν variance X]
        Pmeasure := by
    apply hsummaryRaw.congr
    intro i
    fin_cases i <;>
      filter_upwards [] with ω <;>
        rfl
  have hPmeas : Measurable (normalRawPN ν variance X) :=
    measurable_normalRawPN hXmeas
  have hLmeas : Measurable (normalRawLN ν variance X) :=
    measurable_normalRawLN hXmeas
  have hPL :
      IndepFun (normalRawPN ν variance X)
        (normalRawLN ν variance X) Pmeasure := by
    simpa using
      hsummary.indepFun
        (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have hP_LV :
      IndepFun (normalRawPN ν variance X)
        (fun ω =>
          (normalRawLN ν variance X ω,
            normalRawVN ν variance X ω)) Pmeasure := by
    simpa [normalRawVN] using
      indepFun_p_l_generalStandardizedDifference_of_iIndepFun_summary4
        (ν : ℝ) (normalVarianceSumN variance)
        (oracleCenteredErrorN ν μ variance X)
        (meanDifferenceN ν X)
        (normalRawPN ν variance X)
        (normalRawLN ν variance X)
        Pmeasure hcenteredMeas hDmeas hPmeas hLmeas hsummary
  have hVL :
      IndepFun (normalRawVN ν variance X)
        (normalRawLN ν variance X) Pmeasure := by
    change
      IndepFun
        (fun ω =>
          generalStandardizedDifference (ν : ℝ)
            (normalVarianceSumN variance) (meanDifferenceN ν X ω))
        (normalRawLN ν variance X) Pmeasure
    exact
      indepFun_generalStandardizedDifference_l_of_iIndepFun_summary4
          (ν : ℝ) (normalVarianceSumN variance)
          (oracleCenteredErrorN ν μ variance X)
          (meanDifferenceN ν X)
          (normalRawPN ν variance X)
          (normalRawLN ν variance X)
          Pmeasure hcenteredMeas hDmeas hPmeas hLmeas hsummary
  have hcentered_nested :
      IndepFun (oracleCenteredErrorN ν μ variance X)
        (fun ω =>
          (meanDifferenceN ν X ω,
            (normalRawPN ν variance X ω,
              normalRawLN ν variance X ω))) Pmeasure :=
    indepFun_centered_d_p_l_of_iIndepFun_generalSummary4
      (oracleCenteredErrorN ν μ variance X)
      (meanDifferenceN ν X)
      (normalRawPN ν variance X)
      (normalRawLN ν variance X)
      Pmeasure hcenteredMeas hDmeas hPmeas hLmeas hsummary
  have hcentered :=
    oracleCentered_integrable_sq_and_integral_zeroN
      ν μ (variance 0) (variance 1)
      (sampleMeanN ν (X 0)) (sampleMeanN ν (X 1)) Pmeasure
      (h.hasLaw_sampleMean 0) (h.hasLaw_sampleMean 1)
  refine
    { p_law := ?_
      l_law := ?_
      v_law := hV
      p_l_indep := hPL
      p_lv_indep := hP_LV
      v_l_indep := hVL
      centered_d_indep := hCD
      centeredD_pL_indep := hcenteredD_pL
      centered_d_p_l_indep := hcentered_nested
      summary_iIndep := hsummary
      centered_sq := ?_
      centered_zero := ?_ }
  · change
      HasLaw
        (fun ω =>
          normalRawUN ν variance X 0 ω
            / (normalRawUN ν variance X 0 ω
              + normalRawUN ν variance X 1 ω))
        (betaMeasure ((ν : ℝ) / 2) ((ν : ℝ) / 2)) Pmeasure
    exact hP
  · change
      HasLaw
        (fun ω =>
          normalRawUN ν variance X 0 ω
            + normalRawUN ν variance X 1 ω)
        (gammaMeasure (ν : ℝ) (1 / 2)) Pmeasure
    exact hL
  · simpa [oracleCenteredErrorN, meanDifferenceN,
      oracleVarianceWeightN] using hcentered.1
  · simpa [oracleCenteredErrorN, meanDifferenceN,
      oracleVarianceWeightN] using hcentered.2

/--
All generic canonical laws and independence facts, derived directly from
two raw normal samples for every `ν ≥ 9`.
-/
theorem rawNormalSummaryLawsN_of_normal_samples
    (ν : ℕ) (hν : 9 ≤ ν)
    {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
    {Pmeasure : Measure Ω} {μ : ℝ}
    {variance : Fin 2 → NNReal}
    (h : TwoNormalSamplesN ν X Pmeasure μ variance)
    (hXmeas : ∀ g i, Measurable (X g i))
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    RawNormalSummaryLawsN ν μ variance X Pmeasure := by
  apply rawNormalSummaryLawsN_of_scaledResidual_gamma
    ν hν h hXmeas hvariance₀ hvariance₁
  intro g
  exact
    h.hasLaw_scaledResidualSumSquares
      (by omega : 0 < ν) g
      (by fin_cases g <;> assumption)

end

end GraybillDeal
