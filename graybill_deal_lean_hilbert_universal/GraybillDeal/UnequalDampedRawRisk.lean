import GraybillDeal.UnequalDampedCanonicalSummary
import GraybillDeal.UnequalDampedRawCoordinates

/-!
# Final raw `(13,17)` Graybill--Deal dominance theorem

This module instantiates the fixed unequal canonical risk theorem from two
independent raw normal samples and then transports both canonical estimators
to their literal sample-mean/sample-variance formulas almost everywhere.

The perturbation coefficient is the single fixed value
`unequalDampedEpsilon13_17 = 1 / 2,000,000`; it does not depend on the
unknown population variances.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem sqRisk_congr_ae_unequal
    {μ : ℝ} {estimator₁ estimator₂ : Ω → ℝ} {P : Measure Ω}
    (h : estimator₁ =ᵐ[P] estimator₂) :
    sqRisk μ estimator₁ P = sqRisk μ estimator₂ P := by
  unfold sqRisk
  apply integral_congr_ae
  filter_upwards [h] with ω hω
  rw [hω]

/--
Canonical strict risk improvement assembled directly from the raw normal
model at sample sizes `13` and `17`.
-/
theorem unequalDampedCanonicalClippedEstimatorRiskDifference_neg_of_raw_normal13_17
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ}
    {Pmeasure : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (h : TwoNormalSamplesU 12 16 X Y Pmeasure μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i))
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    sqRisk μ
        (fun ω =>
          μ
            + oracleCenteredError13_17 μ v₁ v₂ X Y ω
            + meanDifferenceU 12 16 X Y ω
              * (unequalDampedCanonicalClippedWeight13_17
                    unequalDampedEpsilon13_17
                    (oracleVarianceWeightU 12 16 v₁ v₂)
                    (normalRawP13_17 v₁ v₂ X Y ω)
                    (normalRawL13_17 v₁ v₂ X Y ω)
                    (normalRawV13_17 v₁ v₂ X Y ω)
                  - oracleVarianceWeightU 12 16 v₁ v₂)) Pmeasure
      <
    sqRisk μ
        (fun ω =>
          μ
            + oracleCenteredError13_17 μ v₁ v₂ X Y ω
            + meanDifferenceU 12 16 X Y ω
              * (unequalDampedCanonicalR13_17
                    (oracleVarianceWeightU 12 16 v₁ v₂)
                    (normalRawP13_17 v₁ v₂ X Y ω)
                  - oracleVarianceWeightU 12 16 v₁ v₂)) Pmeasure := by
  have hlaws :
      RawNormalSummaryLaws13_17 μ v₁ v₂ X Y Pmeasure :=
    rawNormalSummaryLaws13_17_of_normal_samples
      h hX hY hv₁ hv₂
  have hτ₁ : 0 < (v₁ : ℝ) / 13 :=
    div_pos hv₁ (by norm_num)
  have hτ₂ : 0 < (v₂ : ℝ) / 17 :=
    div_pos hv₂ (by norm_num)
  have hvarianceSum :
      0 < normalMeanVarianceSum13_17 v₁ v₂ := by
    unfold normalMeanVarianceSum13_17
    exact add_pos hτ₁ hτ₂
  have hθ0 :
      0 < oracleVarianceWeightU 12 16 v₁ v₂ := by
    norm_num [oracleVarianceWeightU]
    exact div_pos hτ₁ (add_pos hτ₁ hτ₂)
  have hθ1 :
      oracleVarianceWeightU 12 16 v₁ v₂ < 1 := by
    norm_num [oracleVarianceWeightU]
    rw [div_lt_one (add_pos hτ₁ hτ₂)]
    linarith
  have hV :
      HasLaw
        (fun ω =>
          unequalStandardizedDifference
            (normalMeanVarianceSum13_17 v₁ v₂)
            (meanDifferenceU 12 16 X Y ω))
        (gammaMeasure (1 / 2) (1 / 2)) Pmeasure := by
    apply hlaws.v_law.congr
    filter_upwards [] with ω
    simpa [unequalStandardizedDifference13_17,
      unequalStandardizedDifference] using
      (normalRawV13_17_eq_unequalStandardizedDifference
        v₁ v₂ X Y ω).symm
  have hP_LV :
      IndepFun (normalRawP13_17 v₁ v₂ X Y)
        (fun ω =>
          (normalRawL13_17 v₁ v₂ X Y ω,
            unequalStandardizedDifference
              (normalMeanVarianceSum13_17 v₁ v₂)
              (meanDifferenceU 12 16 X Y ω))) Pmeasure := by
    simpa [normalRawV13_17, generalStandardizedDifference,
      unequalStandardizedDifference] using hlaws.p_lv_indep
  have hVL :
      IndepFun
        (fun ω =>
          unequalStandardizedDifference
            (normalMeanVarianceSum13_17 v₁ v₂)
            (meanDifferenceU 12 16 X Y ω))
        (normalRawL13_17 v₁ v₂ X Y) Pmeasure := by
    apply hlaws.v_l_indep.congr
    · filter_upwards [] with ω
      simpa [unequalStandardizedDifference13_17,
        unequalStandardizedDifference] using
        (normalRawV13_17_eq_unequalStandardizedDifference
          v₁ v₂ X Y ω)
    · filter_upwards [] with ω
      rfl
  have hrisk :=
    unequalDampedCanonicalClippedEstimatorRiskDifference_neg_of_summary_laws
      μ (normalMeanVarianceSum13_17 v₁ v₂)
      (oracleVarianceWeightU 12 16 v₁ v₂)
      (oracleCenteredError13_17 μ v₁ v₂ X Y)
      (meanDifferenceU 12 16 X Y)
      (normalRawP13_17 v₁ v₂ X Y)
      (normalRawL13_17 v₁ v₂ X Y)
      Pmeasure hvarianceSum hθ0 hθ1
      (measurable_normalRawP13_17 hX hY)
      (measurable_normalRawL13_17 hX hY)
      (measurable_meanDifferenceU hX hY)
      (measurable_oracleCenteredError13_17 hX hY)
      hlaws.p_law hlaws.l_law hV hP_LV hVL
      hlaws.centered_d_p_l_indep
      hlaws.centered_sq hlaws.centered_zero
  simpa [normalRawV13_17, generalStandardizedDifference,
    unequalStandardizedDifference] using hrisk

/--
The literal clipped perturbation has strictly smaller squared-error risk
than the ordinary unequal-size Graybill--Deal estimator.
-/
theorem rawClippedPerturbedEstimator13_17_sqRisk_lt_rawGraybillDealEstimator13_17
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i))
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    sqRisk μ
        (rawClippedPerturbedEstimator13_17
          unequalDampedEpsilon13_17 X Y) P
      <
    sqRisk μ (rawGraybillDealEstimator13_17 X Y) P := by
  have hcanonical :=
    unequalDampedCanonicalClippedEstimatorRiskDifference_neg_of_raw_normal13_17
      h hX hY hv₁ hv₂
  have hclipped :=
    h.ae_eq_unequalDampedCanonicalClippedEstimator_raw13_17
      unequalDampedEpsilon13_17 hv₁ hv₂
  have hbase :=
    h.ae_eq_unequalDampedCanonicalBaseEstimator_raw13_17
      hv₁ hv₂
  rw [sqRisk_congr_ae_unequal hclipped,
    sqRisk_congr_ae_unequal hbase] at hcanonical
  exact hcanonical

/--
Final inadmissibility witness: at sample sizes `(13,17)`, the ordinary
Graybill--Deal estimator is strictly dominated throughout the positive
variance parameter space by one fixed clipped perturbation.
-/
theorem rawGraybillDealEstimator13_17_strictly_dominated
    {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i))
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    sqRisk μ
        (rawClippedPerturbedEstimator13_17
          (1 / 2000000) X Y) P
      <
    sqRisk μ (rawGraybillDealEstimator13_17 X Y) P := by
  simpa [unequalDampedEpsilon13_17] using
    rawClippedPerturbedEstimator13_17_sqRisk_lt_rawGraybillDealEstimator13_17
      h hX hY hv₁ hv₂

end

end GraybillDeal
