import GraybillDeal.GeneralGaussianMeanBridge
import GraybillDeal.GeneralSummaryIndependence
import GraybillDeal.UnequalBlocks
import GraybillDeal.UnequalSummaryTransform

/-!
# Raw canonical summaries for samples of sizes 13 and 17

This file assembles the probability-law side of the fixed unequal-size
certificate.  The first sample has residual degrees of freedom `12`, the
second has residual degrees of freedom `16`.

With `U₁ = RSS₁/v₁`, `U₂ = RSS₂/v₂`, the canonical summaries are

* `P = U₁/(U₁+U₂) ~ Beta(6,8)`;
* `L = U₁+U₂ ~ Gamma(14,1/2)`;
* `V = D²/(v₁/13+v₂/17) ~ Gamma(1/2,1/2)`;
* `(centered,D,P,L)` are mutually independent.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Standardized first residual sum of squares, with shape six. -/
def normalRawU1_13_17
    (v₁ : NNReal) (X : Fin 13 → Ω → ℝ) : Ω → ℝ :=
  scaledResidualSumSquaresN 12 (v₁ : ℝ) X

/-- Standardized second residual sum of squares, with shape eight. -/
def normalRawU2_13_17
    (v₂ : NNReal) (Y : Fin 17 → Ω → ℝ) : Ω → ℝ :=
  scaledResidualSumSquaresN 16 (v₂ : ℝ) Y

/-- The unequal beta ratio coordinate. -/
def normalRawP13_17
    (v₁ v₂ : NNReal)
    (X : Fin 13 → Ω → ℝ) (Y : Fin 17 → Ω → ℝ) : Ω → ℝ :=
  fun ω =>
    normalRawU1_13_17 v₁ X ω
      / (normalRawU1_13_17 v₁ X ω + normalRawU2_13_17 v₂ Y ω)

/-- The gamma sum coordinate. -/
def normalRawL13_17
    (v₁ v₂ : NNReal)
    (X : Fin 13 → Ω → ℝ) (Y : Fin 17 → Ω → ℝ) : Ω → ℝ :=
  fun ω =>
    normalRawU1_13_17 v₁ X ω + normalRawU2_13_17 v₂ Y ω

/-- Variance of the difference of the two sample means. -/
def normalMeanVarianceSum13_17 (v₁ v₂ : NNReal) : ℝ :=
  (v₁ : ℝ) / 13 + (v₂ : ℝ) / 17

/-- The standardized squared difference of the two sample means. -/
def normalRawV13_17
    (v₁ v₂ : NNReal)
    (X : Fin 13 → Ω → ℝ) (Y : Fin 17 → Ω → ℝ) : Ω → ℝ :=
  fun ω =>
    generalStandardizedDifference 0
      (normalMeanVarianceSum13_17 v₁ v₂)
      (meanDifferenceU 12 16 X Y ω)

/-- The centered known-variance oracle error for the fixed unequal pair. -/
def oracleCenteredError13_17
    (μ : ℝ) (v₁ v₂ : NNReal)
    (X : Fin 13 → Ω → ℝ) (Y : Fin 17 → Ω → ℝ) : Ω → ℝ :=
  oracleCenteredErrorU 12 16 μ
    (oracleVarianceWeightU 12 16 v₁ v₂) X Y

@[fun_prop]
theorem measurable_normalRawU1_13_17
    {v₁ : NNReal} {X : Fin 13 → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) :
    Measurable (normalRawU1_13_17 v₁ X) :=
  measurable_scaledResidualSumSquaresN hX _

@[fun_prop]
theorem measurable_normalRawU2_13_17
    {v₂ : NNReal} {Y : Fin 17 → Ω → ℝ}
    (hY : ∀ i, Measurable (Y i)) :
    Measurable (normalRawU2_13_17 v₂ Y) :=
  measurable_scaledResidualSumSquaresN hY _

@[fun_prop]
theorem measurable_normalRawP13_17
    {v₁ v₂ : NNReal}
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) :
    Measurable (normalRawP13_17 v₁ v₂ X Y) := by
  unfold normalRawP13_17
  fun_prop

@[fun_prop]
theorem measurable_normalRawL13_17
    {v₁ v₂ : NNReal}
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) :
    Measurable (normalRawL13_17 v₁ v₂ X Y) := by
  unfold normalRawL13_17
  fun_prop

@[fun_prop]
theorem measurable_normalRawV13_17
    {v₁ v₂ : NNReal}
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) :
    Measurable (normalRawV13_17 v₁ v₂ X Y) := by
  unfold normalRawV13_17
  fun_prop

@[fun_prop]
theorem measurable_oracleCenteredError13_17
    {μ : ℝ} {v₁ v₂ : NNReal}
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) :
    Measurable (oracleCenteredError13_17 μ v₁ v₂ X Y) := by
  unfold oracleCenteredError13_17
  exact measurable_oracleCenteredErrorU hX hY _ _

/-- All raw-summary laws and independence facts for the fixed unequal pair. -/
structure RawNormalSummaryLaws13_17
    (μ : ℝ) (v₁ v₂ : NNReal)
    (X : Fin 13 → Ω → ℝ) (Y : Fin 17 → Ω → ℝ)
    (Pmeasure : Measure Ω) : Prop where
  p_law :
    HasLaw (normalRawP13_17 v₁ v₂ X Y)
      (betaMeasure 6 8) Pmeasure
  l_law :
    HasLaw (normalRawL13_17 v₁ v₂ X Y)
      (gammaMeasure 14 (1 / 2)) Pmeasure
  v_law :
    HasLaw (normalRawV13_17 v₁ v₂ X Y)
      (gammaMeasure (1 / 2) (1 / 2)) Pmeasure
  p_l_indep :
    IndepFun (normalRawP13_17 v₁ v₂ X Y)
      (normalRawL13_17 v₁ v₂ X Y) Pmeasure
  p_lv_indep :
    IndepFun (normalRawP13_17 v₁ v₂ X Y)
      (fun ω =>
        (normalRawL13_17 v₁ v₂ X Y ω,
          normalRawV13_17 v₁ v₂ X Y ω)) Pmeasure
  v_l_indep :
    IndepFun (normalRawV13_17 v₁ v₂ X Y)
      (normalRawL13_17 v₁ v₂ X Y) Pmeasure
  centered_d_indep :
    IndepFun (oracleCenteredError13_17 μ v₁ v₂ X Y)
      (meanDifferenceU 12 16 X Y) Pmeasure
  centeredD_pL_indep :
    IndepFun
      (fun ω =>
        (oracleCenteredError13_17 μ v₁ v₂ X Y ω,
          meanDifferenceU 12 16 X Y ω))
      (fun ω =>
        (normalRawP13_17 v₁ v₂ X Y ω,
          normalRawL13_17 v₁ v₂ X Y ω))
      Pmeasure
  centered_d_p_l_indep :
    IndepFun (oracleCenteredError13_17 μ v₁ v₂ X Y)
      (fun ω =>
        (meanDifferenceU 12 16 X Y ω,
          (normalRawP13_17 v₁ v₂ X Y ω,
            normalRawL13_17 v₁ v₂ X Y ω)))
      Pmeasure
  summary_iIndep :
    iIndepFun
      ![
        oracleCenteredError13_17 μ v₁ v₂ X Y,
        meanDifferenceU 12 16 X Y,
        normalRawP13_17 v₁ v₂ X Y,
        normalRawL13_17 v₁ v₂ X Y]
      Pmeasure
  centered_sq :
    Integrable
      (fun ω => oracleCenteredError13_17 μ v₁ v₂ X Y ω ^ 2)
      Pmeasure
  centered_zero :
    (∫ ω, oracleCenteredError13_17 μ v₁ v₂ X Y ω ∂Pmeasure) = 0

/--
Assembly of the fixed `(13,17)` summary laws directly from the unequal raw
normal model.
-/
theorem rawNormalSummaryLaws13_17_of_normal_samples
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ}
    {Pmeasure : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (h : TwoNormalSamplesU 12 16 X Y Pmeasure μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i))
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    RawNormalSummaryLaws13_17 μ v₁ v₂ X Y Pmeasure := by
  letI : IsProbabilityMeasure Pmeasure :=
    h.indep.isProbabilityMeasure
  have hU₁ :
      HasLaw (normalRawU1_13_17 v₁ X)
        (gammaMeasure 6 (1 / 2)) Pmeasure := by
    convert h.hasLaw_scaledResidualSumSquaresX (by norm_num) hv₁ using 1 <;>
      norm_num [normalRawU1_13_17]
  have hU₂ :
      HasLaw (normalRawU2_13_17 v₂ Y)
        (gammaMeasure 8 (1 / 2)) Pmeasure := by
    convert h.hasLaw_scaledResidualSumSquaresY (by norm_num) hv₂ using 1 <;>
      norm_num [normalRawU2_13_17]
  have hU₁U₂ :
      IndepFun (normalRawU1_13_17 v₁ X)
        (normalRawU2_13_17 v₂ Y) Pmeasure := by
    simpa [normalRawU1_13_17, normalRawU2_13_17] using
      h.indepFun_scaledResidualSumSquares
  have hvarianceSum : 0 < normalMeanVarianceSum13_17 v₁ v₂ := by
    unfold normalMeanVarianceSum13_17
    positivity
  have hvarianceSum_raw :
      0 < (v₁ : ℝ) / (12 + 1) + (v₂ : ℝ) / (16 + 1) := by
    norm_num
    exact hvarianceSum
  have hCD :
      IndepFun (oracleCenteredError13_17 μ v₁ v₂ X Y)
        (meanDifferenceU 12 16 X Y) Pmeasure := by
    simpa [oracleCenteredError13_17] using
      h.indepFun_oracleCenteredError_meanDifference hvarianceSum_raw
  have hcenteredD_U :
      IndepFun
        (fun ω =>
          (oracleCenteredError13_17 μ v₁ v₂ X Y ω,
            meanDifferenceU 12 16 X Y ω))
        (fun ω =>
          (normalRawU1_13_17 v₁ X ω,
            normalRawU2_13_17 v₂ Y ω))
        Pmeasure := by
    have hout :=
      (h.indepFun_oracleCenteredError_meanDifference_residualSumSquaresPair
        (oracleVarianceWeightU 12 16 v₁ v₂)).comp
        measurable_id
        (show Measurable
            (fun z : ℝ × ℝ =>
              (z.1 / (v₁ : ℝ), z.2 / (v₂ : ℝ))) by fun_prop)
    apply hout.congr
    · filter_upwards [] with ω
      rfl
    · filter_upwards [] with ω
      rfl
  have hcenteredMeas :
      Measurable (oracleCenteredError13_17 μ v₁ v₂ X Y) :=
    measurable_oracleCenteredError13_17 hX hY
  have hDmeas : Measurable (meanDifferenceU 12 16 X Y) :=
    measurable_meanDifferenceU hX hY
  have hU₁meas : Measurable (normalRawU1_13_17 v₁ X) :=
    measurable_normalRawU1_13_17 hX
  have hU₂meas : Measurable (normalRawU2_13_17 v₂ Y) :=
    measurable_normalRawU2_13_17 hY
  obtain ⟨hP, hL, hsummaryRaw⟩ :=
    betaGamma_laws_and_iIndepFun_unequalTransformedSummary4_of_blocks
      (a := 6) (b := 8) (r := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
      (oracleCenteredError13_17 μ v₁ v₂ X Y)
      (meanDifferenceU 12 16 X Y)
      (normalRawU1_13_17 v₁ X)
      (normalRawU2_13_17 v₂ Y)
      Pmeasure hcenteredMeas hDmeas hU₁meas hU₂meas
      hU₁ hU₂ hCD hU₁U₂ hcenteredD_U
  have hsummary :
      iIndepFun
        ![
          oracleCenteredError13_17 μ v₁ v₂ X Y,
          meanDifferenceU 12 16 X Y,
          normalRawP13_17 v₁ v₂ X Y,
          normalRawL13_17 v₁ v₂ X Y]
        Pmeasure := by
    apply hsummaryRaw.congr
    intro i
    fin_cases i <;>
      filter_upwards [] with ω <;>
        rfl
  have hDlaw :
      HasLaw (meanDifferenceU 12 16 X Y)
        (gaussianReal 0
          (normalMeanVarianceSum13_17 v₁ v₂).toNNReal) Pmeasure := by
    convert h.hasLaw_meanDifference using 1
    congr 1
    apply NNReal.eq
    rw [Real.coe_toNNReal _ hvarianceSum.le]
    norm_num [normalMeanVarianceSum13_17]
  have hV :
      HasLaw (normalRawV13_17 v₁ v₂ X Y)
        (gammaMeasure (1 / 2) (1 / 2)) Pmeasure := by
    unfold normalRawV13_17
    have hDlaw' :
        HasLaw (meanDifferenceU 12 16 X Y)
          (gaussianReal 0
            (normalMeanVarianceSum13_17 v₁ v₂
              / (((0 : ℕ) : ℝ) + 1)).toNNReal) Pmeasure := by
      convert hDlaw using 1 <;> norm_num
    have hout :=
      hasLaw_generalStandardizedDifference_of_gaussian
        0 (normalMeanVarianceSum13_17 v₁ v₂)
        (meanDifferenceU 12 16 X Y) Pmeasure
        hvarianceSum hDlaw'
    apply hout.congr
    filter_upwards [] with ω
    norm_num
  have hPmeas : Measurable (normalRawP13_17 v₁ v₂ X Y) :=
    measurable_normalRawP13_17 hX hY
  have hLmeas : Measurable (normalRawL13_17 v₁ v₂ X Y) :=
    measurable_normalRawL13_17 hX hY
  have hPL :
      IndepFun (normalRawP13_17 v₁ v₂ X Y)
        (normalRawL13_17 v₁ v₂ X Y) Pmeasure := by
    simpa using
      hsummary.indepFun
        (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have hP_LV :
      IndepFun (normalRawP13_17 v₁ v₂ X Y)
        (fun ω =>
          (normalRawL13_17 v₁ v₂ X Y ω,
            normalRawV13_17 v₁ v₂ X Y ω)) Pmeasure := by
    simpa [normalRawV13_17] using
      indepFun_p_l_generalStandardizedDifference_of_iIndepFun_summary4
        0 (normalMeanVarianceSum13_17 v₁ v₂)
        (oracleCenteredError13_17 μ v₁ v₂ X Y)
        (meanDifferenceU 12 16 X Y)
        (normalRawP13_17 v₁ v₂ X Y)
        (normalRawL13_17 v₁ v₂ X Y)
        Pmeasure hcenteredMeas hDmeas hPmeas hLmeas hsummary
  have hVL :
      IndepFun (normalRawV13_17 v₁ v₂ X Y)
        (normalRawL13_17 v₁ v₂ X Y) Pmeasure := by
    change
      IndepFun
        (fun ω =>
          generalStandardizedDifference 0
            (normalMeanVarianceSum13_17 v₁ v₂)
            (meanDifferenceU 12 16 X Y ω))
        (normalRawL13_17 v₁ v₂ X Y) Pmeasure
    exact
      indepFun_generalStandardizedDifference_l_of_iIndepFun_summary4
          0 (normalMeanVarianceSum13_17 v₁ v₂)
          (oracleCenteredError13_17 μ v₁ v₂ X Y)
          (meanDifferenceU 12 16 X Y)
          (normalRawP13_17 v₁ v₂ X Y)
          (normalRawL13_17 v₁ v₂ X Y)
          Pmeasure hcenteredMeas hDmeas hPmeas hLmeas hsummary
  have hcentered_nested :
      IndepFun (oracleCenteredError13_17 μ v₁ v₂ X Y)
        (fun ω =>
          (meanDifferenceU 12 16 X Y ω,
            (normalRawP13_17 v₁ v₂ X Y ω,
              normalRawL13_17 v₁ v₂ X Y ω))) Pmeasure :=
    indepFun_centered_d_p_l_of_iIndepFun_generalSummary4
      (oracleCenteredError13_17 μ v₁ v₂ X Y)
      (meanDifferenceU 12 16 X Y)
      (normalRawP13_17 v₁ v₂ X Y)
      (normalRawL13_17 v₁ v₂ X Y)
      Pmeasure hcenteredMeas hDmeas hPmeas hLmeas hsummary
  have hcentered_sq :
      Integrable
        (fun ω => oracleCenteredError13_17 μ v₁ v₂ X Y ω ^ 2)
        Pmeasure := by
    have hmeanX : MemLp (sampleMeanN 12 X) 2 Pmeasure :=
      h.hasGaussianLaw_sampleMeanX.memLp_two
    have hmeanY : MemLp (sampleMeanN 16 Y) 2 Pmeasure :=
      h.hasGaussianLaw_sampleMeanY.memLp_two
    have hC2 :
        MemLp (oracleCenteredError13_17 μ v₁ v₂ X Y) 2 Pmeasure := by
      have hraw :=
        (hmeanX.add
          ((hmeanY.sub hmeanX).const_mul
            (oracleVarianceWeightU 12 16 v₁ v₂))).sub
          (memLp_const (μ := Pmeasure) μ)
      apply hraw.ae_eq
      filter_upwards [] with ω
      rfl
    exact (memLp_two_iff_integrable_sq hC2.1).1 hC2
  have hcentered_zero :
      (∫ ω, oracleCenteredError13_17 μ v₁ v₂ X Y ω ∂Pmeasure) = 0 := by
    have hXint : Integrable (sampleMeanN 12 X) Pmeasure :=
      h.hasGaussianLaw_sampleMeanX.integrable
    have hYint : Integrable (sampleMeanN 16 Y) Pmeasure :=
      h.hasGaussianLaw_sampleMeanY.integrable
    have hDint :
        Integrable (meanDifferenceU 12 16 X Y) Pmeasure := by
      unfold meanDifferenceU
      exact hYint.sub hXint
    unfold oracleCenteredError13_17 oracleCenteredErrorU
    change
      (∫ ω,
        (sampleMeanN 12 X
          + fun ω =>
            oracleVarianceWeightU 12 16 v₁ v₂
              * meanDifferenceU 12 16 X Y ω) ω
          - (fun _ : Ω => μ) ω ∂Pmeasure) = 0
    rw [integral_sub
      (hXint.add
        (hDint.const_mul (oracleVarianceWeightU 12 16 v₁ v₂)))
      (integrable_const μ)]
    change
      (∫ a,
        sampleMeanN 12 X a
          + oracleVarianceWeightU 12 16 v₁ v₂
              * meanDifferenceU 12 16 X Y a ∂Pmeasure)
        - (∫ _ : Ω, μ ∂Pmeasure) = 0
    rw [integral_add hXint
      (hDint.const_mul (oracleVarianceWeightU 12 16 v₁ v₂)),
      integral_const_mul, h.integral_meanDifference,
      h.integral_sampleMeanX]
    simp
  refine
    { p_law := ?_
      l_law := ?_
      v_law := hV
      p_l_indep := hPL
      p_lv_indep := hP_LV
      v_l_indep := hVL
      centered_d_indep := hCD
      centeredD_pL_indep := ?_
      centered_d_p_l_indep := hcentered_nested
      summary_iIndep := hsummary
      centered_sq := hcentered_sq
      centered_zero := hcentered_zero }
  · change
      HasLaw
        (fun ω =>
          normalRawU1_13_17 v₁ X ω
            / (normalRawU1_13_17 v₁ X ω
              + normalRawU2_13_17 v₂ Y ω))
        (betaMeasure 6 8) Pmeasure
    exact hP
  · change
      HasLaw
        (fun ω =>
          normalRawU1_13_17 v₁ X ω
            + normalRawU2_13_17 v₂ Y ω)
        (gammaMeasure 14 (1 / 2)) Pmeasure
    convert hL using 1 <;> norm_num
  · have hout :=
      hcenteredD_U.comp measurable_id measurable_betaGammaRatioSum
    apply hout.congr
    · filter_upwards [] with ω
      rfl
    · filter_upwards [] with ω
      rfl

end

end GraybillDeal
