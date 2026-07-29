import GraybillDeal.UnequalFixedDifferenceFourRealCanonicalSummary
import GraybillDeal.UnequalFixedDifferenceFourAllNRawCoordinates

/-!
# Final raw risk theorem for the full difference-four diagonal

This module instantiates the real-parameter canonical risk theorem from two
independent raw normal samples of sizes

`(n₁,n₂) = (n,n+4)`, `n ≥ 13`,

and transports the canonical estimators to their literal
sample-mean/sample-variance formulas almost everywhere.

The analytic parameter is

`mₙ = (n+1)/2`,

so both odd and even first-sample sizes are covered.  The perturbation
coefficient

`εₙ = unequalFixedDifferenceFourRealEpsilon mₙ`

depends only on the known sample sizes and not on the unknown population
variances.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem sqRisk_congr_ae_unequalFixedDifferenceFourAllN
    {μ : ℝ} {estimator₁ estimator₂ : Ω → ℝ} {P : Measure Ω}
    (h : estimator₁ =ᵐ[P] estimator₂) :
    sqRisk μ estimator₁ P = sqRisk μ estimator₂ P := by
  unfold sqRisk
  apply integral_congr_ae
  filter_upwards [h] with ω hω
  rw [hω]

/--
Canonical strict risk improvement assembled directly from two raw normal
samples of sizes `(n,n+4)`, for every `n ≥ 13`.
-/
theorem
    unequalFixedDifferenceFourAllNCanonicalClippedEstimatorRiskDifference_neg_of_raw_normal
    {n : ℕ} (hn : 13 ≤ n)
    {X :
      Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    {Y :
      Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    {Pmeasure : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (h :
      TwoNormalSamplesU
        (unequalFixedDifferenceFourAllNResidualDF1 n)
        (unequalFixedDifferenceFourAllNResidualDF2 n)
        X Y Pmeasure μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i))
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    sqRisk μ
        (fun ω =>
          μ
            + unequalFixedDifferenceFourAllNOracleCenteredError
                n μ v₁ v₂ X Y ω
            + meanDifferenceU
                (unequalFixedDifferenceFourAllNResidualDF1 n)
                (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω
              * (unequalFixedDifferenceFourRealCanonicalClippedWeight
                    (unequalFixedDifferenceFourSampleM n)
                    (unequalFixedDifferenceFourRealEpsilon
                      (unequalFixedDifferenceFourSampleM n))
                    (oracleVarianceWeightU
                      (unequalFixedDifferenceFourAllNResidualDF1 n)
                      (unequalFixedDifferenceFourAllNResidualDF2 n)
                      v₁ v₂)
                    (unequalFixedDifferenceFourAllNNormalRawP
                      n v₁ v₂ X Y ω)
                    (unequalFixedDifferenceFourAllNNormalRawL
                      n v₁ v₂ X Y ω)
                    (unequalFixedDifferenceFourAllNNormalRawV
                      n v₁ v₂ X Y ω)
                  - oracleVarianceWeightU
                      (unequalFixedDifferenceFourAllNResidualDF1 n)
                      (unequalFixedDifferenceFourAllNResidualDF2 n)
                      v₁ v₂)) Pmeasure
      <
    sqRisk μ
        (fun ω =>
          μ
            + unequalFixedDifferenceFourAllNOracleCenteredError
                n μ v₁ v₂ X Y ω
            + meanDifferenceU
                (unequalFixedDifferenceFourAllNResidualDF1 n)
                (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω
              * (unequalFixedDifferenceFourRealCanonicalR
                    (unequalFixedDifferenceFourSampleM n)
                    (oracleVarianceWeightU
                      (unequalFixedDifferenceFourAllNResidualDF1 n)
                      (unequalFixedDifferenceFourAllNResidualDF2 n)
                      v₁ v₂)
                    (unequalFixedDifferenceFourAllNNormalRawP
                      n v₁ v₂ X Y ω)
                  - oracleVarianceWeightU
                      (unequalFixedDifferenceFourAllNResidualDF1 n)
                      (unequalFixedDifferenceFourAllNResidualDF2 n)
                      v₁ v₂)) Pmeasure := by
  have hlaws :
      UnequalFixedDifferenceFourAllNRawNormalSummaryLaws
        n μ v₁ v₂ X Y Pmeasure :=
    unequalFixedDifferenceFourAllNRawNormalSummaryLaws_of_normal_samples
      hn h hX hY hv₁ hv₂
  have hm :
      7 ≤ unequalFixedDifferenceFourSampleM n :=
    unequalFixedDifferenceFourSampleM_ge_seven hn
  have hτ₁ :
      0 <
        (v₁ : ℝ)
          / (unequalFixedDifferenceFourAllNResidualDF1 n + 1) :=
    div_pos hv₁ (by positivity)
  have hτ₂ :
      0 <
        (v₂ : ℝ)
          / (unequalFixedDifferenceFourAllNResidualDF2 n + 1) :=
    div_pos hv₂ (by positivity)
  have hvarianceSum :
      0 <
        unequalFixedDifferenceFourAllNNormalMeanVarianceSum
          n v₁ v₂ := by
    unfold unequalFixedDifferenceFourAllNNormalMeanVarianceSum
    exact add_pos hτ₁ hτ₂
  have hθ0 :
      0 <
        oracleVarianceWeightU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n)
          v₁ v₂ := by
    unfold oracleVarianceWeightU
    exact div_pos hτ₁ (add_pos hτ₁ hτ₂)
  have hθ1 :
      oracleVarianceWeightU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n)
          v₁ v₂
        < 1 := by
    unfold oracleVarianceWeightU
    rw [div_lt_one (add_pos hτ₁ hτ₂)]
    linarith
  have hV :
      HasLaw
        (fun ω =>
          unequalStandardizedDifference
            (unequalFixedDifferenceFourAllNNormalMeanVarianceSum
              n v₁ v₂)
            (meanDifferenceU
              (unequalFixedDifferenceFourAllNResidualDF1 n)
              (unequalFixedDifferenceFourAllNResidualDF2 n)
              X Y ω))
        (gammaMeasure (1 / 2) (1 / 2)) Pmeasure := by
    apply hlaws.v_law.congr
    filter_upwards [] with ω
    simp only
      [unequalFixedDifferenceFourAllNNormalRawV,
        generalStandardizedDifference,
        unequalStandardizedDifference]
    ring
  have hP_LV :
      IndepFun
        (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y)
        (fun ω =>
          (unequalFixedDifferenceFourAllNNormalRawL
              n v₁ v₂ X Y ω,
            unequalStandardizedDifference
              (unequalFixedDifferenceFourAllNNormalMeanVarianceSum
                n v₁ v₂)
              (meanDifferenceU
                (unequalFixedDifferenceFourAllNResidualDF1 n)
                (unequalFixedDifferenceFourAllNResidualDF2 n)
                X Y ω)))
        Pmeasure := by
    simpa only
      [unequalFixedDifferenceFourAllNNormalRawV,
        generalStandardizedDifference,
        unequalStandardizedDifference,
        Nat.cast_zero, zero_add, one_mul] using
      hlaws.p_lv_indep
  have hVL :
      IndepFun
        (fun ω =>
          unequalStandardizedDifference
            (unequalFixedDifferenceFourAllNNormalMeanVarianceSum
              n v₁ v₂)
            (meanDifferenceU
              (unequalFixedDifferenceFourAllNResidualDF1 n)
              (unequalFixedDifferenceFourAllNResidualDF2 n)
              X Y ω))
        (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y)
        Pmeasure := by
    apply hlaws.v_l_indep.congr
    · filter_upwards [] with ω
      simp only
        [unequalFixedDifferenceFourAllNNormalRawV,
          generalStandardizedDifference,
          unequalStandardizedDifference]
      ring
    · filter_upwards [] with ω
      rfl
  have hrisk :=
    unequalFixedDifferenceFourRealCanonicalClippedEstimatorRiskDifference_neg_of_summary_laws
      hm μ
      (unequalFixedDifferenceFourAllNNormalMeanVarianceSum n v₁ v₂)
      (oracleVarianceWeightU
        (unequalFixedDifferenceFourAllNResidualDF1 n)
        (unequalFixedDifferenceFourAllNResidualDF2 n)
        v₁ v₂)
      (unequalFixedDifferenceFourAllNOracleCenteredError
        n μ v₁ v₂ X Y)
      (meanDifferenceU
        (unequalFixedDifferenceFourAllNResidualDF1 n)
        (unequalFixedDifferenceFourAllNResidualDF2 n) X Y)
      (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y)
      (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y)
      Pmeasure hvarianceSum hθ0 hθ1
      (measurable_unequalFixedDifferenceFourAllNNormalRawP hX hY)
      (measurable_unequalFixedDifferenceFourAllNNormalRawL hX hY)
      (measurable_meanDifferenceU hX hY)
      (measurable_unequalFixedDifferenceFourAllNOracleCenteredError hX hY)
      hlaws.p_law hlaws.l_law hV hP_LV hVL
      hlaws.centered_d_p_l_indep
      hlaws.centered_sq hlaws.centered_zero
  simpa only
    [unequalFixedDifferenceFourAllNNormalRawV,
      generalStandardizedDifference,
      unequalStandardizedDifference,
      Nat.cast_zero, zero_add, one_mul] using hrisk

/--
For every `n ≥ 13`, the literal clipped perturbation with the explicit
sample-size-only coefficient

`εₙ = unequalFixedDifferenceFourRealEpsilon
  (unequalFixedDifferenceFourSampleM n)`

has strictly smaller squared-error risk than the ordinary unequal-size
Graybill--Deal estimator throughout the positive-variance parameter space.
-/
theorem
    unequalFixedDifferenceFourAllNRawClippedPerturbedEstimator_sqRisk_lt_rawGraybillDealEstimator
    {n : ℕ} (hn : 13 ≤ n)
    {X :
      Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    {Y :
      Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (h :
      TwoNormalSamplesU
        (unequalFixedDifferenceFourAllNResidualDF1 n)
        (unequalFixedDifferenceFourAllNResidualDF2 n)
        X Y P μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i))
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    sqRisk μ
        (unequalFixedDifferenceFourAllNRawClippedPerturbedEstimator
          (unequalFixedDifferenceFourRealEpsilon
            (unequalFixedDifferenceFourSampleM n))
          n X Y) P
      <
    sqRisk μ
        (unequalFixedDifferenceFourAllNRawGraybillDealEstimator
          n X Y) P := by
  have hcanonical :=
    unequalFixedDifferenceFourAllNCanonicalClippedEstimatorRiskDifference_neg_of_raw_normal
      hn h hX hY hv₁ hv₂
  have hclipped :=
    h.ae_eq_unequalFixedDifferenceFourAllNCanonicalClippedEstimator_raw
      (unequalFixedDifferenceFourRealEpsilon
        (unequalFixedDifferenceFourSampleM n))
      hn hv₁ hv₂
  have hbase :=
    h.ae_eq_unequalFixedDifferenceFourAllNCanonicalBaseEstimator_raw
      hn hv₁ hv₂
  rw [sqRisk_congr_ae_unequalFixedDifferenceFourAllN hclipped,
    sqRisk_congr_ae_unequalFixedDifferenceFourAllN hbase] at hcanonical
  exact hcanonical

end

end GraybillDeal
