import GraybillDeal.UnequalFixedDifferenceFourCanonicalSummary
import GraybillDeal.UnequalFixedDifferenceFourRawCoordinates

/-!
# Final raw risk theorem for the fixed-difference-four family

This module instantiates the family canonical risk theorem from two
independent raw normal samples of sizes

`(n₁,n₂) = (2m-1,2m+3)`, `m ≥ 7`,

and then transports the two canonical estimators to their literal
sample-mean/sample-variance formulas almost everywhere.

The perturbation coefficient is the explicit family value
`unequalFixedDifferenceFourEpsilon m`; it depends only on the known sample
sizes and not on the unknown population variances.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem sqRisk_congr_ae_unequalFixedDifferenceFour
    {μ : ℝ} {estimator₁ estimator₂ : Ω → ℝ} {P : Measure Ω}
    (h : estimator₁ =ᵐ[P] estimator₂) :
    sqRisk μ estimator₁ P = sqRisk μ estimator₂ P := by
  unfold sqRisk
  apply integral_congr_ae
  filter_upwards [h] with ω hω
  rw [hω]

/--
Canonical strict risk improvement assembled directly from two raw normal
samples at family index `m ≥ 7`.
-/
theorem
    unequalFixedDifferenceFourCanonicalClippedEstimatorRiskDifference_neg_of_raw_normal
    {m : ℕ} (hm : 7 ≤ m)
    {X :
      Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    {Y :
      Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    {Pmeasure : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (h :
      TwoNormalSamplesU
        (unequalFixedDifferenceFourResidualDF1 m)
        (unequalFixedDifferenceFourResidualDF2 m)
        X Y Pmeasure μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i))
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    sqRisk μ
        (fun ω =>
          μ
            + unequalFixedDifferenceFourOracleCenteredError
                m μ v₁ v₂ X Y ω
            + meanDifferenceU
                (unequalFixedDifferenceFourResidualDF1 m)
                (unequalFixedDifferenceFourResidualDF2 m) X Y ω
              * (unequalFixedDifferenceFourCanonicalClippedWeight
                    m (unequalFixedDifferenceFourEpsilon m)
                    (oracleVarianceWeightU
                      (unequalFixedDifferenceFourResidualDF1 m)
                      (unequalFixedDifferenceFourResidualDF2 m)
                      v₁ v₂)
                    (unequalFixedDifferenceFourNormalRawP
                      m v₁ v₂ X Y ω)
                    (unequalFixedDifferenceFourNormalRawL
                      m v₁ v₂ X Y ω)
                    (unequalFixedDifferenceFourNormalRawV
                      m v₁ v₂ X Y ω)
                  - oracleVarianceWeightU
                      (unequalFixedDifferenceFourResidualDF1 m)
                      (unequalFixedDifferenceFourResidualDF2 m)
                      v₁ v₂)) Pmeasure
      <
    sqRisk μ
        (fun ω =>
          μ
            + unequalFixedDifferenceFourOracleCenteredError
                m μ v₁ v₂ X Y ω
            + meanDifferenceU
                (unequalFixedDifferenceFourResidualDF1 m)
                (unequalFixedDifferenceFourResidualDF2 m) X Y ω
              * (unequalFixedDifferenceFourCanonicalR
                    m
                    (oracleVarianceWeightU
                      (unequalFixedDifferenceFourResidualDF1 m)
                      (unequalFixedDifferenceFourResidualDF2 m)
                      v₁ v₂)
                    (unequalFixedDifferenceFourNormalRawP
                      m v₁ v₂ X Y ω)
                  - oracleVarianceWeightU
                      (unequalFixedDifferenceFourResidualDF1 m)
                      (unequalFixedDifferenceFourResidualDF2 m)
                      v₁ v₂)) Pmeasure := by
  have hlaws :
      UnequalFixedDifferenceFourRawNormalSummaryLaws
        m μ v₁ v₂ X Y Pmeasure :=
    unequalFixedDifferenceFourRawNormalSummaryLaws_of_normal_samples
      hm h hX hY hv₁ hv₂
  have hτ₁ :
      0 <
        (v₁ : ℝ)
          / (unequalFixedDifferenceFourResidualDF1 m + 1) :=
    div_pos hv₁ (by positivity)
  have hτ₂ :
      0 <
        (v₂ : ℝ)
          / (unequalFixedDifferenceFourResidualDF2 m + 1) :=
    div_pos hv₂ (by positivity)
  have hvarianceSum :
      0 <
        unequalFixedDifferenceFourNormalMeanVarianceSum
          m v₁ v₂ := by
    unfold unequalFixedDifferenceFourNormalMeanVarianceSum
    exact add_pos hτ₁ hτ₂
  have hθ0 :
      0 <
        oracleVarianceWeightU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m)
          v₁ v₂ := by
    unfold oracleVarianceWeightU
    exact div_pos hτ₁ (add_pos hτ₁ hτ₂)
  have hθ1 :
      oracleVarianceWeightU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m)
          v₁ v₂
        < 1 := by
    unfold oracleVarianceWeightU
    rw [div_lt_one (add_pos hτ₁ hτ₂)]
    linarith
  have hV :
      HasLaw
        (fun ω =>
          unequalStandardizedDifference
            (unequalFixedDifferenceFourNormalMeanVarianceSum
              m v₁ v₂)
            (meanDifferenceU
              (unequalFixedDifferenceFourResidualDF1 m)
              (unequalFixedDifferenceFourResidualDF2 m)
              X Y ω))
        (gammaMeasure (1 / 2) (1 / 2)) Pmeasure := by
    apply hlaws.v_law.congr
    filter_upwards [] with ω
    simp only
      [unequalFixedDifferenceFourNormalRawV,
        generalStandardizedDifference,
        unequalStandardizedDifference]
    ring
  have hP_LV :
      IndepFun
        (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y)
        (fun ω =>
          (unequalFixedDifferenceFourNormalRawL
              m v₁ v₂ X Y ω,
            unequalStandardizedDifference
              (unequalFixedDifferenceFourNormalMeanVarianceSum
                m v₁ v₂)
              (meanDifferenceU
                (unequalFixedDifferenceFourResidualDF1 m)
                (unequalFixedDifferenceFourResidualDF2 m)
                X Y ω)))
        Pmeasure := by
    simpa only
      [unequalFixedDifferenceFourNormalRawV,
        generalStandardizedDifference,
        unequalStandardizedDifference,
        Nat.cast_zero, zero_add, one_mul] using
      hlaws.p_lv_indep
  have hVL :
      IndepFun
        (fun ω =>
          unequalStandardizedDifference
            (unequalFixedDifferenceFourNormalMeanVarianceSum
              m v₁ v₂)
            (meanDifferenceU
              (unequalFixedDifferenceFourResidualDF1 m)
              (unequalFixedDifferenceFourResidualDF2 m)
              X Y ω))
        (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y)
        Pmeasure := by
    apply hlaws.v_l_indep.congr
    · filter_upwards [] with ω
      simp only
        [unequalFixedDifferenceFourNormalRawV,
          generalStandardizedDifference,
          unequalStandardizedDifference]
      ring
    · filter_upwards [] with ω
      rfl
  have hrisk :=
    unequalFixedDifferenceFourCanonicalClippedEstimatorRiskDifference_neg_of_summary_laws
      hm μ
      (unequalFixedDifferenceFourNormalMeanVarianceSum m v₁ v₂)
      (oracleVarianceWeightU
        (unequalFixedDifferenceFourResidualDF1 m)
        (unequalFixedDifferenceFourResidualDF2 m)
        v₁ v₂)
      (unequalFixedDifferenceFourOracleCenteredError
        m μ v₁ v₂ X Y)
      (meanDifferenceU
        (unequalFixedDifferenceFourResidualDF1 m)
        (unequalFixedDifferenceFourResidualDF2 m) X Y)
      (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y)
      (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y)
      Pmeasure hvarianceSum hθ0 hθ1
      (measurable_unequalFixedDifferenceFourNormalRawP hX hY)
      (measurable_unequalFixedDifferenceFourNormalRawL hX hY)
      (measurable_meanDifferenceU hX hY)
      (measurable_unequalFixedDifferenceFourOracleCenteredError hX hY)
      hlaws.p_law hlaws.l_law hV hP_LV hVL
      hlaws.centered_d_p_l_indep
      hlaws.centered_sq hlaws.centered_zero
  simpa only
    [unequalFixedDifferenceFourNormalRawV,
      generalStandardizedDifference,
      unequalStandardizedDifference,
      Nat.cast_zero, zero_add, one_mul] using hrisk

/--
For every family member `m ≥ 7`, the literal clipped perturbation with the
explicit coefficient `unequalFixedDifferenceFourEpsilon m` has strictly
smaller squared-error risk than the ordinary unequal-size Graybill--Deal
estimator throughout the positive-variance parameter space.
-/
theorem
    unequalFixedDifferenceFourRawClippedPerturbedEstimator_sqRisk_lt_rawGraybillDealEstimator
    {m : ℕ} (hm : 7 ≤ m)
    {X :
      Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    {Y :
      Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (h :
      TwoNormalSamplesU
        (unequalFixedDifferenceFourResidualDF1 m)
        (unequalFixedDifferenceFourResidualDF2 m)
        X Y P μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i))
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    sqRisk μ
        (unequalFixedDifferenceFourRawClippedPerturbedEstimator
          (unequalFixedDifferenceFourEpsilon m) m X Y) P
      <
    sqRisk μ
        (unequalFixedDifferenceFourRawGraybillDealEstimator
          m X Y) P := by
  have hcanonical :=
    unequalFixedDifferenceFourCanonicalClippedEstimatorRiskDifference_neg_of_raw_normal
      hm h hX hY hv₁ hv₂
  have hclipped :=
    h.ae_eq_unequalFixedDifferenceFourCanonicalClippedEstimator_raw
      (unequalFixedDifferenceFourEpsilon m) hm hv₁ hv₂
  have hbase :=
    h.ae_eq_unequalFixedDifferenceFourCanonicalBaseEstimator_raw
      hm hv₁ hv₂
  rw [sqRisk_congr_ae_unequalFixedDifferenceFour hclipped,
    sqRisk_congr_ae_unequalFixedDifferenceFour hbase] at hcanonical
  exact hcanonical

end

end GraybillDeal
