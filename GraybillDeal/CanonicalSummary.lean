import GraybillDeal.CanonicalLaws
import GraybillDeal.CanonicalClipping

/-!
# Estimator-level summary of the canonical probability bridge

`CanonicalLaws.lean` derives the two reduced moments from the component
beta/gamma laws.  `CanonicalClipping.lean` turns those moments into a strict
risk improvement, provided the usual centered-error terms can be removed.

This file packages the two stages.  The first theorem leaves the elementary
centered-error integrability and orthogonality assumptions explicit.  The
second derives all of them from square-integrability, mean zero, and
independence of the centered error from `(D,P,L)`.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/--
The clipped estimator has smaller risk under the three component laws.

Compared with `canonicalClippedEstimatorRiskDifference13_neg`, this theorem
has no moment-bridge hypothesis: it constructs that bridge from the
`Beta(6,6)`, `Gamma(12,1/2)`, and `Gamma(1/2,1/2)` laws and the two required
independence statements.
-/
theorem canonicalClippedEstimatorRiskDifference13_neg_of_component_laws
    (μ varianceSum s : ℝ) (centered D P L : Ω → ℝ) (ℙ : Measure Ω)
    (hvarianceSum : 0 < varianceSum) (hs : |s| < 1)
    (hP :
      ProbabilityTheory.HasLaw P
        (ProbabilityTheory.betaMeasure 6 6) ℙ)
    (hL :
      ProbabilityTheory.HasLaw L
        (ProbabilityTheory.gammaMeasure 12 (1 / 2)) ℙ)
    (hV :
      ProbabilityTheory.HasLaw
        (fun ω => standardizedDifference13 varianceSum (D ω))
        (ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) ℙ)
    (hP_LV :
      ProbabilityTheory.IndepFun P
        (fun ω =>
          (L ω, standardizedDifference13 varianceSum (D ω))) ℙ)
    (hVL :
      ProbabilityTheory.IndepFun
        (fun ω => standardizedDifference13 varianceSum (D ω)) L ℙ)
    (hcentered_sq : Integrable (fun ω => (centered ω) ^ 2) ℙ)
    (hcross_clipped :
      Integrable
        (fun ω =>
          centered ω * D ω
            * (canonicalClippedWeight13 epsilon13 s (P ω) (L ω)
                (standardizedDifference13 varianceSum (D ω))
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
            * (canonicalClippedWeight13 epsilon13 s (P ω) (L ω)
                (standardizedDifference13 varianceSum (D ω))
              - canonicalTheta s) ^ 2) ℙ)
    (hquadratic_base :
      Integrable
        (fun ω =>
          (D ω) ^ 2
            * (canonicalR s (P ω) - canonicalTheta s) ^ 2) ℙ)
    (hcross_clipped_zero :
      (∫ ω,
        centered ω * D ω
          * (canonicalClippedWeight13 epsilon13 s (P ω) (L ω)
              (standardizedDifference13 varianceSum (D ω))
            - canonicalTheta s) ∂ℙ) = 0)
    (hcross_base_zero :
      (∫ ω,
        centered ω * D ω
          * (canonicalR s (P ω) - canonicalTheta s) ∂ℙ) = 0) :
    sqRisk μ
        (fun ω =>
          μ + centered ω + D ω
            * (canonicalClippedWeight13 epsilon13 s (P ω) (L ω)
                (standardizedDifference13 varianceSum (D ω))
              - canonicalTheta s)) ℙ
      <
    sqRisk μ
        (fun ω =>
          μ + centered ω
            + D ω * (canonicalR s (P ω) - canonicalTheta s)) ℙ := by
  exact canonicalClippedEstimatorRiskDifference13_neg
    μ varianceSum canonicalKa13 s centered D P L ℙ
    hvarianceSum canonicalKa13_pos hs
    (canonicalMomentBridge13_of_component_laws
      s P L (fun ω => standardizedDifference13 varianceSum (D ω)) ℙ
      hs hP hL hV hP_LV hVL)
    hcentered_sq hcross_clipped hcross_base
    hquadratic_clipped hquadratic_base
    hcross_clipped_zero hcross_base_zero

/--
On a finite measure space, square-integrability plus measurability implies
integrability.  The deliberately coarse bound `|x| ≤ x² + 1` is enough here.
-/
private theorem integrable_of_integrable_sq
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
Fully packaged estimator-level probability-law bridge.

The centered error is assumed measurable, square-integrable, mean zero, and
independent of the joint statistic `(D,P,L)`.  These assumptions imply both
cross-term integrability statements and both zero-cross-moment identities.
The two quadratic integrability statements follow from the gamma law of
`13D² / varianceSum` and the fact that both the base and clipped weights lie
in `[0,1]` almost surely.

Thus the only probabilistic work still outside this theorem is deriving the
displayed component laws and independence statements from the original
normal-sample model.
-/
theorem canonicalClippedEstimatorRiskDifference13_neg_of_summary_laws
    (μ varianceSum s : ℝ) (centered D P L : Ω → ℝ) (ℙ : Measure Ω)
    (hvarianceSum : 0 < varianceSum) (hs : |s| < 1)
    (hPmeas : Measurable P) (hLmeas : Measurable L)
    (hDmeas : Measurable D) (hcentered_meas : Measurable centered)
    (hP :
      ProbabilityTheory.HasLaw P
        (ProbabilityTheory.betaMeasure 6 6) ℙ)
    (hL :
      ProbabilityTheory.HasLaw L
        (ProbabilityTheory.gammaMeasure 12 (1 / 2)) ℙ)
    (hV :
      ProbabilityTheory.HasLaw
        (fun ω => standardizedDifference13 varianceSum (D ω))
        (ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) ℙ)
    (hP_LV :
      ProbabilityTheory.IndepFun P
        (fun ω =>
          (L ω, standardizedDifference13 varianceSum (D ω))) ℙ)
    (hVL :
      ProbabilityTheory.IndepFun
        (fun ω => standardizedDifference13 varianceSum (D ω)) L ℙ)
    (hcentered_DPL :
      ProbabilityTheory.IndepFun centered
        (fun ω => (D ω, (P ω, L ω))) ℙ)
    (hcentered_sq : Integrable (fun ω => (centered ω) ^ 2) ℙ)
    (hcentered_zero : (∫ ω, centered ω ∂ℙ) = 0) :
    sqRisk μ
        (fun ω =>
          μ + centered ω + D ω
            * (canonicalClippedWeight13 epsilon13 s (P ω) (L ω)
                (standardizedDifference13 varianceSum (D ω))
              - canonicalTheta s)) ℙ
      <
    sqRisk μ
        (fun ω =>
          μ + centered ω
            + D ω * (canonicalR s (P ω) - canonicalTheta s)) ℙ := by
  let V : Ω → ℝ := fun ω =>
    standardizedDifference13 varianceSum (D ω)
  let baseFactor : Ω → ℝ := fun ω =>
    D ω * (canonicalR s (P ω) - canonicalTheta s)
  let clippedFactor : Ω → ℝ := fun ω =>
    D ω
      * (canonicalClippedWeight13 epsilon13 s (P ω) (L ω) (V ω)
        - canonicalTheta s)
  letI : IsProbabilityMeasure
      (ProbabilityTheory.betaMeasure 6 6) :=
    ProbabilityTheory.isProbabilityMeasureBeta (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure ℙ := hP.isProbabilityMeasure

  have hVmeas : Measurable V := by
    dsimp only [V]
    unfold standardizedDifference13
    fun_prop
  have hbaseFactor_meas : Measurable baseFactor := by
    dsimp only [baseFactor]
    unfold canonicalR canonicalDenom canonicalTheta
    fun_prop
  have hclippedFactor_meas : Measurable clippedFactor := by
    dsimp only [clippedFactor]
    unfold canonicalClippedWeight13 canonicalWeight13 perturbation
      canonicalH13 canonicalQ13 canonicalR canonicalDenom canonicalTheta
      weightPolynomial clip01
    fun_prop

  have hmom :
      CanonicalFiveMoments13 L V ℙ :=
    canonicalFiveMoments13_of_gamma_laws L V ℙ hL hV
  have hD_sq : Integrable (fun ω => D ω ^ 2) ℙ := by
    have hscaled := hmom.v_integrable.const_mul (varianceSum / 13)
    apply hscaled.congr
    filter_upwards [] with ω
    dsimp only [V]
    exact (scale_standardizedDifference13 varianceSum (D ω)
      (ne_of_gt hvarianceSum))

  have hP_support :
      ∀ᵐ ω ∂ℙ, P ω ∈ Set.Icc (0 : ℝ) 1 := by
    exact (hP.ae_iff measurableSet_Icc.mem).2
      betaMeasure_six_six_ae_mem_Icc

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
            * (canonicalClippedWeight13 epsilon13 s (P ω) (L ω) (V ω)
              - canonicalTheta s) ^ 2) ℙ := by
    apply hD_sq.mono'
    · have heq :
          (fun ω =>
            D ω ^ 2
              * (canonicalClippedWeight13 epsilon13 s (P ω) (L ω) (V ω)
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
          (canonicalWeight13 epsilon13 s (P ω) (L ω) (V ω))
      have htheta := canonicalTheta_mem_Icc hs
      have hsq :
          (canonicalClippedWeight13 epsilon13 s (P ω) (L ω) (V ω)
              - canonicalTheta s) ^ 2 ≤ 1 := by
        unfold canonicalClippedWeight13
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
    integrable_of_integrable_sq
      hbaseFactor_meas.aestronglyMeasurable hbaseFactor_sq
  have hclippedFactor_int : Integrable clippedFactor ℙ :=
    integrable_of_integrable_sq
      hclippedFactor_meas.aestronglyMeasurable hclippedFactor_sq
  have hcentered_int : Integrable centered ℙ :=
    integrable_of_integrable_sq
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
              * (canonicalClippedWeight13 epsilon13 s z.2.1 z.2.2
                  (standardizedDifference13 varianceSum z.1)
                - canonicalTheta s)) := by
      unfold canonicalClippedWeight13 canonicalWeight13 perturbation
        canonicalH13 canonicalQ13 canonicalR canonicalDenom canonicalTheta
        standardizedDifference13 weightPolynomial clip01
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
            * (canonicalClippedWeight13 epsilon13 s (P ω) (L ω) (V ω)
              - canonicalTheta s)) ℙ := by
    have hmul :=
      hcentered_clipped.integrable_mul hcentered_int hclippedFactor_int
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
          * (canonicalClippedWeight13 epsilon13 s (P ω) (L ω) (V ω)
            - canonicalTheta s) ∂ℙ) = 0 := by
    calc
      (∫ ω,
        centered ω * D ω
          * (canonicalClippedWeight13 epsilon13 s (P ω) (L ω) (V ω)
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

  exact canonicalClippedEstimatorRiskDifference13_neg_of_component_laws
    μ varianceSum s centered D P L ℙ hvarianceSum hs
    hP hL hV hP_LV hVL hcentered_sq
    (by simpa only [V] using hcross_clipped)
    hcross_base
    (by simpa only [V] using hquadratic_clipped)
    hquadratic_base
    (by simpa only [V] using hcross_clipped_zero)
    hcross_base_zero

end

end GraybillDeal
