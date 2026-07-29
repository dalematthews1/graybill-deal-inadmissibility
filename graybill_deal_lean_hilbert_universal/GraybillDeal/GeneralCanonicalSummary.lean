import GraybillDeal.GeneralCanonicalClipping
import GraybillDeal.GeneralCanonicalLaws
import GraybillDeal.GeneralGraybillDealEpsilon
import GraybillDeal.GeneralSummaryIndependence

/-!
# Estimator-level canonical summary bridge at arbitrary sample size

This file packages the generic component-law calculation and the clipped
estimator risk comparison.  The perturbation coefficient is the fixed
`generalGraybillDealEpsilon ν`, which depends only on the residual degrees
of freedom and works simultaneously for every interior variance contrast.

The first theorem leaves the elementary centered-error integrability and
orthogonality assumptions explicit.  The second derives them from
square-integrability, mean zero, and independence of the centered error from
the joint statistic `(D,P,L)`.  A final wrapper accepts mutual independence
of the four summaries directly.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/--
The fixed generic clipped estimator has smaller risk under the three
component laws, provided the centered cross terms have already been removed.
-/
theorem generalCanonicalClippedEstimatorRiskDifference_neg_of_component_laws
    (ν : ℕ) (hν : 9 ≤ ν)
    (μ varianceSum s : ℝ) (centered D P L : Ω → ℝ) (ℙ : Measure Ω)
    (hvarianceSum : 0 < varianceSum) (hs : |s| < 1)
    (hP :
      ProbabilityTheory.HasLaw P
        (ProbabilityTheory.betaMeasure
          ((ν : ℝ) / 2) ((ν : ℝ) / 2)) ℙ)
    (hL :
      ProbabilityTheory.HasLaw L
        (ProbabilityTheory.gammaMeasure (ν : ℝ) (1 / 2)) ℙ)
    (hV :
      ProbabilityTheory.HasLaw
        (fun ω =>
          generalStandardizedDifference (ν : ℝ)
            varianceSum (D ω))
        (ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) ℙ)
    (hP_LV :
      ProbabilityTheory.IndepFun P
        (fun ω =>
          (L ω,
            generalStandardizedDifference (ν : ℝ)
              varianceSum (D ω))) ℙ)
    (hVL :
      ProbabilityTheory.IndepFun
        (fun ω =>
          generalStandardizedDifference (ν : ℝ)
            varianceSum (D ω)) L ℙ)
    (hcentered_sq : Integrable (fun ω => (centered ω) ^ 2) ℙ)
    (hcross_clipped :
      Integrable
        (fun ω =>
          centered ω * D ω
            * (generalCanonicalClippedWeight
                (generalGraybillDealEpsilon ν) (ν : ℝ) s
                (P ω) (L ω)
                (generalStandardizedDifference (ν : ℝ)
                  varianceSum (D ω))
              - canonicalTheta s)) ℙ)
    (hcross_base :
      Integrable
        (fun ω =>
          centered ω * D ω
            * (canonicalR s (P ω) - canonicalTheta s)) ℙ)
    (hquadratic_clipped :
      Integrable
        (fun ω =>
          (D ω) ^ 2
            * (generalCanonicalClippedWeight
                (generalGraybillDealEpsilon ν) (ν : ℝ) s
                (P ω) (L ω)
                (generalStandardizedDifference (ν : ℝ)
                  varianceSum (D ω))
              - canonicalTheta s) ^ 2) ℙ)
    (hquadratic_base :
      Integrable
        (fun ω =>
          (D ω) ^ 2
            * (canonicalR s (P ω) - canonicalTheta s) ^ 2) ℙ)
    (hcross_clipped_zero :
      (∫ ω,
        centered ω * D ω
          * (generalCanonicalClippedWeight
              (generalGraybillDealEpsilon ν) (ν : ℝ) s
              (P ω) (L ω)
              (generalStandardizedDifference (ν : ℝ)
                varianceSum (D ω))
            - canonicalTheta s) ∂ℙ) = 0)
    (hcross_base_zero :
      (∫ ω,
        centered ω * D ω
          * (canonicalR s (P ω) - canonicalTheta s) ∂ℙ) = 0) :
    sqRisk μ
        (fun ω =>
          μ + centered ω + D ω
            * (generalCanonicalClippedWeight
                (generalGraybillDealEpsilon ν) (ν : ℝ) s
                (P ω) (L ω)
                (generalStandardizedDifference (ν : ℝ)
                  varianceSum (D ω))
              - canonicalTheta s)) ℙ
      <
    sqRisk μ
        (fun ω =>
          μ + centered ω
            + D ω * (canonicalR s (P ω) - canonicalTheta s)) ℙ := by
  exact
    generalCanonicalClippedEstimatorRiskDifference_neg
      ν hν μ varianceSum
      (centeredBetaKa ((ν : ℝ) / 2))
      (generalGraybillDealEpsilon ν) s centered D P L ℙ
      hvarianceSum hs
      (generalCanonicalMomentBridge_of_component_laws
        ν hν s P L
        (fun ω =>
          generalStandardizedDifference (ν : ℝ)
            varianceSum (D ω))
        ℙ hs hP hL hV hP_LV hVL)
      (generalGraybillDealEpsilon_reduced_neg ν hν s hs)
      hcentered_sq hcross_clipped hcross_base
      hquadratic_clipped hquadratic_base
      hcross_clipped_zero hcross_base_zero

/--
On a finite measure space, square-integrability and strong measurability
imply integrability.
-/
private theorem general_integrable_of_integrable_sq
    {f : Ω → ℝ} {ℙ : Measure Ω} [IsFiniteMeasure ℙ]
    (hf : AEStronglyMeasurable f ℙ)
    (hfsq : Integrable (fun ω => f ω ^ 2) ℙ) :
    Integrable f ℙ := by
  apply (hfsq.add (integrable_const (1 : ℝ))).mono' hf
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  change |f ω| ≤ f ω ^ 2 + 1
  have hsquare : 0 ≤ (|f ω| - 1 / 2 : ℝ) ^ 2 := sq_nonneg _
  have habssq : |f ω| ^ 2 = f ω ^ 2 := sq_abs (f ω)
  norm_num at hsquare
  nlinarith

/--
Fully packaged estimator-level probability-law bridge at arbitrary residual
degrees of freedom.

The centered error is measurable, square-integrable, mean zero, and
independent of `(D,(P,L))`.  The gamma law of
`(ν+1)D² / varianceSum` supplies integrability of `D²`; the base and clipped
weights are bounded by one.  These facts discharge every integrability and
zero-cross-moment assumption in the lower-level clipped-risk theorem.
-/
theorem generalCanonicalClippedEstimatorRiskDifference_neg_of_summary_laws
    (ν : ℕ) (hν : 9 ≤ ν)
    (μ varianceSum s : ℝ) (centered D P L : Ω → ℝ) (ℙ : Measure Ω)
    (hvarianceSum : 0 < varianceSum) (hs : |s| < 1)
    (hPmeas : Measurable P) (hLmeas : Measurable L)
    (hDmeas : Measurable D) (hcentered_meas : Measurable centered)
    (hP :
      ProbabilityTheory.HasLaw P
        (ProbabilityTheory.betaMeasure
          ((ν : ℝ) / 2) ((ν : ℝ) / 2)) ℙ)
    (hL :
      ProbabilityTheory.HasLaw L
        (ProbabilityTheory.gammaMeasure (ν : ℝ) (1 / 2)) ℙ)
    (hV :
      ProbabilityTheory.HasLaw
        (fun ω =>
          generalStandardizedDifference (ν : ℝ)
            varianceSum (D ω))
        (ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) ℙ)
    (hP_LV :
      ProbabilityTheory.IndepFun P
        (fun ω =>
          (L ω,
            generalStandardizedDifference (ν : ℝ)
              varianceSum (D ω))) ℙ)
    (hVL :
      ProbabilityTheory.IndepFun
        (fun ω =>
          generalStandardizedDifference (ν : ℝ)
            varianceSum (D ω)) L ℙ)
    (hcentered_DPL :
      ProbabilityTheory.IndepFun centered
        (fun ω => (D ω, (P ω, L ω))) ℙ)
    (hcentered_sq : Integrable (fun ω => (centered ω) ^ 2) ℙ)
    (hcentered_zero : (∫ ω, centered ω ∂ℙ) = 0) :
    sqRisk μ
        (fun ω =>
          μ + centered ω + D ω
            * (generalCanonicalClippedWeight
                (generalGraybillDealEpsilon ν) (ν : ℝ) s
                (P ω) (L ω)
                (generalStandardizedDifference (ν : ℝ)
                  varianceSum (D ω))
              - canonicalTheta s)) ℙ
      <
    sqRisk μ
        (fun ω =>
          μ + centered ω
            + D ω * (canonicalR s (P ω) - canonicalTheta s)) ℙ := by
  let V : Ω → ℝ := fun ω =>
    generalStandardizedDifference (ν : ℝ) varianceSum (D ω)
  let baseFactor : Ω → ℝ := fun ω =>
    D ω * (canonicalR s (P ω) - canonicalTheta s)
  let clippedFactor : Ω → ℝ := fun ω =>
    D ω
      * (generalCanonicalClippedWeight
          (generalGraybillDealEpsilon ν) (ν : ℝ) s
          (P ω) (L ω) (V ω)
        - canonicalTheta s)
  have hνR : (9 : ℝ) ≤ (ν : ℝ) := by
    exact_mod_cast hν
  have hshape : 0 < (ν : ℝ) / 2 := by
    linarith
  letI : IsProbabilityMeasure
      (ProbabilityTheory.betaMeasure
        ((ν : ℝ) / 2) ((ν : ℝ) / 2)) :=
    ProbabilityTheory.isProbabilityMeasureBeta hshape hshape
  letI : IsProbabilityMeasure ℙ := hP.isProbabilityMeasure

  have hVmeas : Measurable V := by
    dsimp only [V]
    unfold generalStandardizedDifference
    fun_prop
  have hbaseFactor_meas : Measurable baseFactor := by
    dsimp only [baseFactor]
    unfold canonicalR canonicalDenom canonicalTheta
    fun_prop
  have hclippedFactor_meas : Measurable clippedFactor := by
    dsimp only [clippedFactor]
    unfold generalCanonicalClippedWeight generalCanonicalWeight
      generalCanonicalH canonicalG canonicalQ canonicalRTheta
      canonicalDenomTheta canonicalR canonicalDenom canonicalTheta
      perturbation weightPolynomial clip01
    fun_prop

  have hmom :
      GeneralCanonicalFiveMoments (ν : ℝ) L V ℙ :=
    generalCanonicalFiveMoments_of_gamma_laws
      (ν : ℝ) hνR L V ℙ hL hV
  have hνplus : (0 : ℝ) < (ν : ℝ) + 1 := by
    positivity
  have hD_sq : Integrable (fun ω => D ω ^ 2) ℙ := by
    have hscaled :=
      hmom.v_integrable.const_mul
        (varianceSum / ((ν : ℝ) + 1))
    apply hscaled.congr
    filter_upwards [] with ω
    dsimp only [V]
    exact
      scale_generalStandardizedDifference
        (ν : ℝ) varianceSum (D ω)
        (ne_of_gt hvarianceSum) (ne_of_gt hνplus)

  have hP_support :
      ∀ᵐ ω ∂ℙ, P ω ∈ Set.Icc (0 : ℝ) 1 := by
    exact (hP.ae_iff measurableSet_Icc.mem).2
      (betaMeasure_same_ae_mem_Icc ((ν : ℝ) / 2))

  have hquadratic_base :
      Integrable
        (fun ω =>
          D ω ^ 2
            * (canonicalR s (P ω) - canonicalTheta s) ^ 2) ℙ := by
    apply hD_sq.mono'
    · have heq :
          (fun ω =>
            D ω ^ 2
              * (canonicalR s (P ω) - canonicalTheta s) ^ 2)
            =
          (fun ω => baseFactor ω ^ 2) := by
            funext ω
            dsimp only [baseFactor]
            ring
      rw [heq]
      exact (hbaseFactor_meas.pow_const 2).aestronglyMeasurable
    · filter_upwards [hP_support] with ω hp
      have hr := canonicalR_mem_Icc_of_mem_Icc hs hp
      have htheta := canonicalTheta_mem_Icc hs
      have hsq :
          (canonicalR s (P ω) - canonicalTheta s) ^ 2 ≤ 1 := by
        rw [sq_le_one_iff_abs_le_one, abs_le]
        constructor <;> linarith [hr.1, hr.2, htheta.1, htheta.2]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact mul_le_of_le_one_right (sq_nonneg _) hsq

  have hquadratic_clipped :
      Integrable
        (fun ω =>
          D ω ^ 2
            * (generalCanonicalClippedWeight
                (generalGraybillDealEpsilon ν) (ν : ℝ) s
                (P ω) (L ω) (V ω)
              - canonicalTheta s) ^ 2) ℙ := by
    apply hD_sq.mono'
    · have heq :
          (fun ω =>
            D ω ^ 2
              * (generalCanonicalClippedWeight
                  (generalGraybillDealEpsilon ν) (ν : ℝ) s
                  (P ω) (L ω) (V ω)
                - canonicalTheta s) ^ 2)
            =
          (fun ω => clippedFactor ω ^ 2) := by
            funext ω
            dsimp only [clippedFactor]
            ring
      rw [heq]
      exact (hclippedFactor_meas.pow_const 2).aestronglyMeasurable
    · filter_upwards [] with ω
      have hw :=
        clip01_mem_Icc
          (generalCanonicalWeight
            (generalGraybillDealEpsilon ν) (ν : ℝ) s
            (P ω) (L ω) (V ω))
      have htheta := canonicalTheta_mem_Icc hs
      have hsq :
          (generalCanonicalClippedWeight
              (generalGraybillDealEpsilon ν) (ν : ℝ) s
              (P ω) (L ω) (V ω)
            - canonicalTheta s) ^ 2 ≤ 1 := by
        unfold generalCanonicalClippedWeight
        rw [sq_le_one_iff_abs_le_one, abs_le]
        constructor <;> linarith [hw.1, hw.2, htheta.1, htheta.2]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact mul_le_of_le_one_right (sq_nonneg _) hsq

  have hbaseFactor_sq :
      Integrable (fun ω => (baseFactor ω) ^ 2) ℙ := by
    apply hquadratic_base.congr
    filter_upwards [] with ω
    dsimp only [baseFactor]
    ring
  have hclippedFactor_sq :
      Integrable (fun ω => (clippedFactor ω) ^ 2) ℙ := by
    apply hquadratic_clipped.congr
    filter_upwards [] with ω
    dsimp only [clippedFactor]
    ring
  have hbaseFactor_int : Integrable baseFactor ℙ :=
    general_integrable_of_integrable_sq
      hbaseFactor_meas.aestronglyMeasurable hbaseFactor_sq
  have hclippedFactor_int : Integrable clippedFactor ℙ :=
    general_integrable_of_integrable_sq
      hclippedFactor_meas.aestronglyMeasurable hclippedFactor_sq
  have hcentered_int : Integrable centered ℙ :=
    general_integrable_of_integrable_sq
      hcentered_meas.aestronglyMeasurable hcentered_sq

  have hcentered_base :
      ProbabilityTheory.IndepFun centered baseFactor ℙ := by
    have hout :
        Measurable
          (fun z : ℝ × (ℝ × ℝ) =>
            z.1 * (canonicalR s z.2.1 - canonicalTheta s)) := by
      unfold canonicalR canonicalDenom canonicalTheta
      fun_prop
    simpa only [baseFactor, Function.comp_def, id_eq] using
      hcentered_DPL.comp measurable_id hout
  have hcentered_clipped :
      ProbabilityTheory.IndepFun centered clippedFactor ℙ := by
    have hout :
        Measurable
          (fun z : ℝ × (ℝ × ℝ) =>
            z.1
              * (generalCanonicalClippedWeight
                  (generalGraybillDealEpsilon ν) (ν : ℝ) s
                  z.2.1 z.2.2
                  (generalStandardizedDifference (ν : ℝ)
                    varianceSum z.1)
                - canonicalTheta s)) := by
      unfold generalCanonicalClippedWeight generalCanonicalWeight
        generalCanonicalH canonicalG canonicalQ canonicalRTheta
        canonicalDenomTheta canonicalR canonicalDenom canonicalTheta
        generalStandardizedDifference perturbation weightPolynomial clip01
      fun_prop
    simpa only [clippedFactor, V, Function.comp_def, id_eq] using
      hcentered_DPL.comp measurable_id hout

  have hcross_base :
      Integrable
        (fun ω =>
          centered ω * D ω
            * (canonicalR s (P ω) - canonicalTheta s)) ℙ := by
    have hmul :=
      hcentered_base.integrable_mul hcentered_int hbaseFactor_int
    apply hmul.congr
    filter_upwards [] with ω
    dsimp only [baseFactor]
    simp only [Pi.mul_apply]
    ring
  have hcross_clipped :
      Integrable
        (fun ω =>
          centered ω * D ω
            * (generalCanonicalClippedWeight
                (generalGraybillDealEpsilon ν) (ν : ℝ) s
                (P ω) (L ω) (V ω)
              - canonicalTheta s)) ℙ := by
    have hmul :=
      hcentered_clipped.integrable_mul
        hcentered_int hclippedFactor_int
    apply hmul.congr
    filter_upwards [] with ω
    dsimp only [clippedFactor]
    simp only [Pi.mul_apply]
    ring

  have hcross_base_zero :
      (∫ ω,
        centered ω * D ω
          * (canonicalR s (P ω) - canonicalTheta s) ∂ℙ) = 0 := by
    calc
      (∫ ω,
        centered ω * D ω
          * (canonicalR s (P ω) - canonicalTheta s) ∂ℙ)
          =
        ∫ ω, centered ω * baseFactor ω ∂ℙ := by
          apply integral_congr_ae
          filter_upwards [] with ω
          dsimp only [baseFactor]
          ring
      _ =
        (∫ ω, centered ω ∂ℙ) * ∫ ω, baseFactor ω ∂ℙ := by
          exact hcentered_base.integral_fun_mul_eq_mul_integral
            hcentered_meas.aestronglyMeasurable
            hbaseFactor_meas.aestronglyMeasurable
      _ = 0 := by rw [hcentered_zero, zero_mul]
  have hcross_clipped_zero :
      (∫ ω,
        centered ω * D ω
          * (generalCanonicalClippedWeight
              (generalGraybillDealEpsilon ν) (ν : ℝ) s
              (P ω) (L ω) (V ω)
            - canonicalTheta s) ∂ℙ) = 0 := by
    calc
      (∫ ω,
        centered ω * D ω
          * (generalCanonicalClippedWeight
              (generalGraybillDealEpsilon ν) (ν : ℝ) s
              (P ω) (L ω) (V ω)
            - canonicalTheta s) ∂ℙ)
          =
        ∫ ω, centered ω * clippedFactor ω ∂ℙ := by
          apply integral_congr_ae
          filter_upwards [] with ω
          dsimp only [clippedFactor]
          ring
      _ =
        (∫ ω, centered ω ∂ℙ) * ∫ ω, clippedFactor ω ∂ℙ := by
          exact hcentered_clipped.integral_fun_mul_eq_mul_integral
            hcentered_meas.aestronglyMeasurable
            hclippedFactor_meas.aestronglyMeasurable
      _ = 0 := by rw [hcentered_zero, zero_mul]

  exact
    generalCanonicalClippedEstimatorRiskDifference_neg_of_component_laws
      ν hν μ varianceSum s centered D P L ℙ hvarianceSum hs
      hP hL hV hP_LV hVL hcentered_sq
      (by simpa only [V] using hcross_clipped)
      hcross_base
      (by simpa only [V] using hquadratic_clipped)
      hquadratic_base
      (by simpa only [V] using hcross_clipped_zero)
      hcross_base_zero

/--
Mutual-independence wrapper for the packaged summary-law bridge.

This is the convenient interface for the raw Gaussian assembly: mutual
independence of `(centered,D,P,L)` is converted to the three nested
independence statements required by the component-law and centered-error
calculations.
-/
theorem generalCanonicalClippedEstimatorRiskDifference_neg_of_iIndepFun_summary4
    (ν : ℕ) (hν : 9 ≤ ν)
    (μ varianceSum s : ℝ) (centered D P L : Ω → ℝ) (ℙ : Measure Ω)
    (hvarianceSum : 0 < varianceSum) (hs : |s| < 1)
    (hPmeas : Measurable P) (hLmeas : Measurable L)
    (hDmeas : Measurable D) (hcentered_meas : Measurable centered)
    (hP :
      ProbabilityTheory.HasLaw P
        (ProbabilityTheory.betaMeasure
          ((ν : ℝ) / 2) ((ν : ℝ) / 2)) ℙ)
    (hL :
      ProbabilityTheory.HasLaw L
        (ProbabilityTheory.gammaMeasure (ν : ℝ) (1 / 2)) ℙ)
    (hV :
      ProbabilityTheory.HasLaw
        (fun ω =>
          generalStandardizedDifference (ν : ℝ)
            varianceSum (D ω))
        (ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) ℙ)
    (hsummary :
      ProbabilityTheory.iIndepFun ![centered, D, P, L] ℙ)
    (hcentered_sq : Integrable (fun ω => (centered ω) ^ 2) ℙ)
    (hcentered_zero : (∫ ω, centered ω ∂ℙ) = 0) :
    sqRisk μ
        (fun ω =>
          μ + centered ω + D ω
            * (generalCanonicalClippedWeight
                (generalGraybillDealEpsilon ν) (ν : ℝ) s
                (P ω) (L ω)
                (generalStandardizedDifference (ν : ℝ)
                  varianceSum (D ω))
              - canonicalTheta s)) ℙ
      <
    sqRisk μ
        (fun ω =>
          μ + centered ω
            + D ω * (canonicalR s (P ω) - canonicalTheta s)) ℙ := by
  exact
    generalCanonicalClippedEstimatorRiskDifference_neg_of_summary_laws
      ν hν μ varianceSum s centered D P L ℙ
      hvarianceSum hs hPmeas hLmeas hDmeas hcentered_meas
      hP hL hV
      (indepFun_p_l_generalStandardizedDifference_of_iIndepFun_summary4
        (ν : ℝ) varianceSum centered D P L ℙ
        hcentered_meas hDmeas hPmeas hLmeas hsummary)
      (indepFun_generalStandardizedDifference_l_of_iIndepFun_summary4
        (ν : ℝ) varianceSum centered D P L ℙ
        hcentered_meas hDmeas hPmeas hLmeas hsummary)
      (indepFun_centered_d_p_l_of_iIndepFun_generalSummary4
        centered D P L ℙ
        hcentered_meas hDmeas hPmeas hLmeas hsummary)
      hcentered_sq hcentered_zero

end

end GraybillDeal
