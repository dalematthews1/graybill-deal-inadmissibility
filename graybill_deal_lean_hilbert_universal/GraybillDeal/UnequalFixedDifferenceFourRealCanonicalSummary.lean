import GraybillDeal.UnequalFixedDifferenceFourRealCanonicalLaws

/-!
# Real-parameter estimator-level canonical summary bridge

For every real family parameter `m ≥ 7`, the analytic canonical summaries
have component laws

* `P ~ Beta(m-1,m+1)`;
* `L ~ Gamma(2m,1/2)`;
* `V = D² / varianceSum ~ Gamma(1/2,1/2)`.

This module deliberately stays at the canonical-summary level.  It makes no
claim that an arbitrary real `m` is itself a raw sample dimension.  Integer
sample-size pairs `(n,n+4)` are recovered later by setting
`m = (n+1)/2`, which may be integral or half-integral.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Component-law risk theorem -/

/--
The real-family canonical clipped estimator has smaller risk under the three
component laws once the centered cross terms have been removed.

This is the minimal estimator-risk consequence of the real canonical
product/law bridge: it involves no raw sample dimensions.
-/
theorem
    unequalFixedDifferenceFourRealCanonicalClippedEstimatorRiskDifference_neg_of_component_laws
    {m : ℝ} (hm : 7 ≤ m)
    (μ varianceSum θ : ℝ)
    (centered D P L : Ω → ℝ) (ℙ : Measure Ω)
    (hvarianceSum : 0 < varianceSum)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hP :
      ProbabilityTheory.HasLaw P
        (ProbabilityTheory.betaMeasure (m - 1) (m + 1)) ℙ)
    (hL :
      ProbabilityTheory.HasLaw L
        (ProbabilityTheory.gammaMeasure (2 * m) (1 / 2)) ℙ)
    (hV :
      ProbabilityTheory.HasLaw
        (fun ω => unequalStandardizedDifference varianceSum (D ω))
        (ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) ℙ)
    (hP_LV :
      ProbabilityTheory.IndepFun P
        (fun ω =>
          (L ω,
            unequalStandardizedDifference varianceSum (D ω))) ℙ)
    (hVL :
      ProbabilityTheory.IndepFun
        (fun ω => unequalStandardizedDifference varianceSum (D ω))
        L ℙ)
    (hcentered_sq :
      Integrable (fun ω => centered ω ^ 2) ℙ)
    (hcross_clipped :
      Integrable
        (fun ω =>
          centered ω * D ω
            * (unequalFixedDifferenceFourRealCanonicalClippedWeight
                m (unequalFixedDifferenceFourRealEpsilon m)
                θ (P ω) (L ω)
                (unequalStandardizedDifference varianceSum (D ω))
              - θ)) ℙ)
    (hcross_base :
      Integrable
        (fun ω =>
          centered ω * D ω
            * (unequalFixedDifferenceFourRealCanonicalR
                m θ (P ω) - θ)) ℙ)
    (hquadratic_clipped :
      Integrable
        (fun ω =>
          D ω ^ 2
            * (unequalFixedDifferenceFourRealCanonicalClippedWeight
                m (unequalFixedDifferenceFourRealEpsilon m)
                θ (P ω) (L ω)
                (unequalStandardizedDifference varianceSum (D ω))
              - θ) ^ 2) ℙ)
    (hquadratic_base :
      Integrable
        (fun ω =>
          D ω ^ 2
            * (unequalFixedDifferenceFourRealCanonicalR
                m θ (P ω) - θ) ^ 2) ℙ)
    (hcross_clipped_zero :
      (∫ ω,
        centered ω * D ω
          * (unequalFixedDifferenceFourRealCanonicalClippedWeight
              m (unequalFixedDifferenceFourRealEpsilon m)
              θ (P ω) (L ω)
              (unequalStandardizedDifference varianceSum (D ω))
            - θ) ∂ℙ) = 0)
    (hcross_base_zero :
      (∫ ω,
        centered ω * D ω
          * (unequalFixedDifferenceFourRealCanonicalR
              m θ (P ω) - θ) ∂ℙ) = 0) :
    sqRisk μ
        (fun ω =>
          μ + centered ω + D ω
            * (unequalFixedDifferenceFourRealCanonicalClippedWeight
                m (unequalFixedDifferenceFourRealEpsilon m)
                θ (P ω) (L ω)
                (unequalStandardizedDifference varianceSum (D ω))
              - θ)) ℙ
      <
    sqRisk μ
        (fun ω =>
          μ + centered ω + D ω
            * (unequalFixedDifferenceFourRealCanonicalR
                m θ (P ω) - θ)) ℙ := by
  have hbridge :=
    unequalFixedDifferenceFourRealCanonicalMomentBridge_of_component_laws
      hm θ hθ0 hθ1 P L
      (fun ω => unequalStandardizedDifference varianceSum (D ω))
      ℙ hP hL hV hP_LV hVL
  have hrisk :=
    unequalDampedClippedEstimatorRiskDifference_neg
      μ varianceSum θ
      (unequalFixedDifferenceFourRealEpsilon m)
      (unequalFixedDifferenceFourRealCanonicalB m θ)
      (unequalFixedDifferenceFourRealCanonicalC m θ)
      centered D
      (fun ω =>
        unequalFixedDifferenceFourRealCanonicalR m θ (P ω))
      (fun ω =>
        unequalFixedDifferenceFourRealCanonicalH
          m θ (P ω) (L ω)
          (unequalStandardizedDifference varianceSum (D ω)))
      ℙ hvarianceSum ⟨hθ0.le, hθ1.le⟩ hbridge
      (unequalFixedDifferenceFourRealCanonicalReducedRisk_neg
        hm hθ0 hθ1)
      hcentered_sq
      (by
        simpa only
          [unequalFixedDifferenceFourRealCanonicalClippedWeight,
            unequalFixedDifferenceFourRealCanonicalWeight,
            unequalDampedClippedWeight,
            unequalDampedPerturbedWeight] using hcross_clipped)
      hcross_base
      (by
        simpa only
          [unequalFixedDifferenceFourRealCanonicalClippedWeight,
            unequalFixedDifferenceFourRealCanonicalWeight,
            unequalDampedClippedWeight,
            unequalDampedPerturbedWeight] using hquadratic_clipped)
      hquadratic_base
      (by
        simpa only
          [unequalFixedDifferenceFourRealCanonicalClippedWeight,
            unequalFixedDifferenceFourRealCanonicalWeight,
            unequalDampedClippedWeight,
            unequalDampedPerturbedWeight] using hcross_clipped_zero)
      hcross_base_zero
  simpa only
    [unequalFixedDifferenceFourRealCanonicalClippedWeight,
      unequalFixedDifferenceFourRealCanonicalWeight,
      unequalDampedClippedWeight,
      unequalDampedPerturbedWeight] using hrisk

/-! ## Automatic discharge of centered cross terms -/

/--
On a finite measure space, square-integrability and strong measurability
imply integrability.
-/
private theorem unequalFD4Real_integrable_of_integrable_sq
    {f : Ω → ℝ} {ℙ : Measure Ω} [IsFiniteMeasure ℙ]
    (hf : AEStronglyMeasurable f ℙ)
    (hfsq : Integrable (fun ω => f ω ^ 2) ℙ) :
    Integrable f ℙ := by
  apply (hfsq.add (integrable_const (1 : ℝ))).mono' hf
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  change |f ω| ≤ f ω ^ 2 + 1
  have hsquare : 0 ≤ (|f ω| - 1 / 2 : ℝ) ^ 2 :=
    sq_nonneg _
  have habssq : |f ω| ^ 2 = f ω ^ 2 :=
    sq_abs (f ω)
  norm_num at hsquare
  nlinarith

/--
Fully packaged estimator-level bridge for the real-family canonical
summaries.

The centered error is measurable, square-integrable, mean zero, and
independent of `(D,(P,L))`.  The law of `V=D²/varianceSum` supplies
integrability of `D²`; the baseline and clipped weights lie in `[0,1]`.
These facts discharge all integrability and zero-cross-moment hypotheses
of the lower-level clipped-risk theorem.
-/
theorem
    unequalFixedDifferenceFourRealCanonicalClippedEstimatorRiskDifference_neg_of_summary_laws
    {m : ℝ} (hm : 7 ≤ m)
    (μ varianceSum θ : ℝ)
    (centered D P L : Ω → ℝ) (ℙ : Measure Ω)
    (hvarianceSum : 0 < varianceSum)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hPmeas : Measurable P)
    (hLmeas : Measurable L)
    (hDmeas : Measurable D)
    (hcentered_meas : Measurable centered)
    (hP :
      ProbabilityTheory.HasLaw P
        (ProbabilityTheory.betaMeasure (m - 1) (m + 1)) ℙ)
    (hL :
      ProbabilityTheory.HasLaw L
        (ProbabilityTheory.gammaMeasure (2 * m) (1 / 2)) ℙ)
    (hV :
      ProbabilityTheory.HasLaw
        (fun ω => unequalStandardizedDifference varianceSum (D ω))
        (ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) ℙ)
    (hP_LV :
      ProbabilityTheory.IndepFun P
        (fun ω =>
          (L ω,
            unequalStandardizedDifference varianceSum (D ω))) ℙ)
    (hVL :
      ProbabilityTheory.IndepFun
        (fun ω => unequalStandardizedDifference varianceSum (D ω))
        L ℙ)
    (hcentered_DPL :
      ProbabilityTheory.IndepFun centered
        (fun ω => (D ω, (P ω, L ω))) ℙ)
    (hcentered_sq :
      Integrable (fun ω => centered ω ^ 2) ℙ)
    (hcentered_zero :
      (∫ ω, centered ω ∂ℙ) = 0) :
    sqRisk μ
        (fun ω =>
          μ + centered ω + D ω
            * (unequalFixedDifferenceFourRealCanonicalClippedWeight
                m (unequalFixedDifferenceFourRealEpsilon m)
                θ (P ω) (L ω)
                (unequalStandardizedDifference varianceSum (D ω))
              - θ)) ℙ
      <
    sqRisk μ
        (fun ω =>
          μ + centered ω + D ω
            * (unequalFixedDifferenceFourRealCanonicalR
                m θ (P ω) - θ)) ℙ := by
  let V : Ω → ℝ :=
    fun ω => unequalStandardizedDifference varianceSum (D ω)
  let baseFactor : Ω → ℝ :=
    fun ω =>
      D ω
        * (unequalFixedDifferenceFourRealCanonicalR
            m θ (P ω) - θ)
  let clippedFactor : Ω → ℝ :=
    fun ω =>
      D ω
        * (unequalFixedDifferenceFourRealCanonicalClippedWeight
            m (unequalFixedDifferenceFourRealEpsilon m)
            θ (P ω) (L ω) (V ω) - θ)
  letI :
      IsProbabilityMeasure
        (ProbabilityTheory.betaMeasure (m - 1) (m + 1)) :=
    ProbabilityTheory.isProbabilityMeasureBeta
      (by linarith) (by linarith)
  letI : IsProbabilityMeasure ℙ :=
    hP.isProbabilityMeasure

  have hVmeas : Measurable V := by
    dsimp only [V]
    unfold unequalStandardizedDifference
    fun_prop
  have hbaseFactor_meas : Measurable baseFactor := by
    dsimp only [baseFactor]
    unfold unequalFixedDifferenceFourRealCanonicalR
      unequalFixedDifferenceFourRealCanonicalDenom
    fun_prop
  have hclippedFactor_meas : Measurable clippedFactor := by
    dsimp only [clippedFactor]
    unfold unequalFixedDifferenceFourRealCanonicalClippedWeight
      unequalFixedDifferenceFourRealCanonicalWeight
      unequalFixedDifferenceFourRealCanonicalH
      unequalFixedDifferenceFourRealCanonicalQ
      unequalFixedDifferenceFourRealCanonicalR
      unequalFixedDifferenceFourRealCanonicalDenom
      unequalDampedPhi unequalDampedInner perturbation clip01
    fun_prop

  have hmom :
      GeneralCanonicalFiveMoments
        (2 * m) L V ℙ :=
    generalCanonicalFiveMoments_of_gamma_laws
      (2 * m) (by linarith)
      L V ℙ hL (by simpa only [V] using hV)
  have hD_sq :
      Integrable (fun ω => D ω ^ 2) ℙ := by
    have hscaled :=
      hmom.v_integrable.const_mul varianceSum
    apply hscaled.congr
    filter_upwards [] with ω
    dsimp only [V]
    exact
      scale_unequalStandardizedDifference
        varianceSum (D ω) (ne_of_gt hvarianceSum)

  have hP_support :
      ∀ᵐ ω ∂ℙ, P ω ∈ Icc (0 : ℝ) 1 := by
    exact (hP.ae_iff measurableSet_Icc.mem).2
      (betaMeasure_unequalFixedDifferenceFourReal_ae_mem_Icc m)

  have hquadratic_base :
      Integrable
        (fun ω =>
          D ω ^ 2
            * (unequalFixedDifferenceFourRealCanonicalR
                m θ (P ω) - θ) ^ 2) ℙ := by
    apply hD_sq.mono'
    · have heq :
          (fun ω =>
            D ω ^ 2
              * (unequalFixedDifferenceFourRealCanonicalR
                  m θ (P ω) - θ) ^ 2)
            =
          (fun ω => baseFactor ω ^ 2) := by
            funext ω
            dsimp only [baseFactor]
            ring
      rw [heq]
      exact
        (hbaseFactor_meas.pow_const 2).aestronglyMeasurable
    · filter_upwards [hP_support] with ω hp
      have hr :=
        unequalFixedDifferenceFourRealCanonicalR_mem_Icc
          hm hθ0 hθ1 hp
      have hsq :
          (unequalFixedDifferenceFourRealCanonicalR
              m θ (P ω) - θ) ^ 2 ≤ 1 := by
        rw [sq_le_one_iff_abs_le_one, abs_le]
        constructor <;>
          linarith [hr.1, hr.2, hθ0, hθ1]
      rw [Real.norm_eq_abs,
        abs_of_nonneg
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact mul_le_of_le_one_right (sq_nonneg _) hsq

  have hquadratic_clipped :
      Integrable
        (fun ω =>
          D ω ^ 2
            * (unequalFixedDifferenceFourRealCanonicalClippedWeight
                m (unequalFixedDifferenceFourRealEpsilon m)
                θ (P ω) (L ω) (V ω) - θ) ^ 2) ℙ := by
    apply hD_sq.mono'
    · have heq :
          (fun ω =>
            D ω ^ 2
              * (unequalFixedDifferenceFourRealCanonicalClippedWeight
                  m (unequalFixedDifferenceFourRealEpsilon m)
                  θ (P ω) (L ω) (V ω) - θ) ^ 2)
            =
          (fun ω => clippedFactor ω ^ 2) := by
            funext ω
            dsimp only [clippedFactor]
            ring
      rw [heq]
      exact
        (hclippedFactor_meas.pow_const 2).aestronglyMeasurable
    · filter_upwards [] with ω
      have hw :=
        clip01_mem_Icc
          (unequalFixedDifferenceFourRealCanonicalWeight
            m (unequalFixedDifferenceFourRealEpsilon m)
            θ (P ω) (L ω) (V ω))
      have hsq :
          (unequalFixedDifferenceFourRealCanonicalClippedWeight
              m (unequalFixedDifferenceFourRealEpsilon m)
              θ (P ω) (L ω) (V ω) - θ) ^ 2 ≤ 1 := by
        unfold unequalFixedDifferenceFourRealCanonicalClippedWeight
        rw [sq_le_one_iff_abs_le_one, abs_le]
        constructor <;>
          linarith [hw.1, hw.2, hθ0, hθ1]
      rw [Real.norm_eq_abs,
        abs_of_nonneg
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact mul_le_of_le_one_right (sq_nonneg _) hsq

  have hbaseFactor_sq :
      Integrable (fun ω => baseFactor ω ^ 2) ℙ := by
    apply hquadratic_base.congr
    filter_upwards [] with ω
    dsimp only [baseFactor]
    ring
  have hclippedFactor_sq :
      Integrable (fun ω => clippedFactor ω ^ 2) ℙ := by
    apply hquadratic_clipped.congr
    filter_upwards [] with ω
    dsimp only [clippedFactor]
    ring
  have hbaseFactor_int :
      Integrable baseFactor ℙ :=
    unequalFD4Real_integrable_of_integrable_sq
      hbaseFactor_meas.aestronglyMeasurable
      hbaseFactor_sq
  have hclippedFactor_int :
      Integrable clippedFactor ℙ :=
    unequalFD4Real_integrable_of_integrable_sq
      hclippedFactor_meas.aestronglyMeasurable
      hclippedFactor_sq
  have hcentered_int :
      Integrable centered ℙ :=
    unequalFD4Real_integrable_of_integrable_sq
      hcentered_meas.aestronglyMeasurable
      hcentered_sq

  have hcentered_base :
      ProbabilityTheory.IndepFun centered baseFactor ℙ := by
    have hout :
        Measurable
          (fun z : ℝ × (ℝ × ℝ) =>
            z.1
              * (unequalFixedDifferenceFourRealCanonicalR
                  m θ z.2.1 - θ)) := by
      unfold unequalFixedDifferenceFourRealCanonicalR
        unequalFixedDifferenceFourRealCanonicalDenom
      fun_prop
    simpa only [baseFactor, Function.comp_def, id_eq] using
      hcentered_DPL.comp measurable_id hout
  have hcentered_clipped :
      ProbabilityTheory.IndepFun centered clippedFactor ℙ := by
    have hout :
        Measurable
          (fun z : ℝ × (ℝ × ℝ) =>
            z.1
              * (unequalFixedDifferenceFourRealCanonicalClippedWeight
                  m (unequalFixedDifferenceFourRealEpsilon m)
                  θ z.2.1 z.2.2
                  (unequalStandardizedDifference varianceSum z.1)
                - θ)) := by
      unfold unequalFixedDifferenceFourRealCanonicalClippedWeight
        unequalFixedDifferenceFourRealCanonicalWeight
        unequalFixedDifferenceFourRealCanonicalH
        unequalFixedDifferenceFourRealCanonicalQ
        unequalFixedDifferenceFourRealCanonicalR
        unequalFixedDifferenceFourRealCanonicalDenom
        unequalDampedPhi unequalDampedInner
        unequalStandardizedDifference perturbation clip01
      fun_prop
    simpa only
      [clippedFactor, V, Function.comp_def, id_eq] using
      hcentered_DPL.comp measurable_id hout

  have hcross_base :
      Integrable
        (fun ω =>
          centered ω * D ω
            * (unequalFixedDifferenceFourRealCanonicalR
                m θ (P ω) - θ)) ℙ := by
    have hmul :=
      hcentered_base.integrable_mul
        hcentered_int hbaseFactor_int
    apply hmul.congr
    filter_upwards [] with ω
    dsimp only [baseFactor]
    simp only [Pi.mul_apply]
    ring
  have hcross_clipped :
      Integrable
        (fun ω =>
          centered ω * D ω
            * (unequalFixedDifferenceFourRealCanonicalClippedWeight
                m (unequalFixedDifferenceFourRealEpsilon m)
                θ (P ω) (L ω) (V ω) - θ)) ℙ := by
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
          * (unequalFixedDifferenceFourRealCanonicalR
              m θ (P ω) - θ) ∂ℙ) = 0 := by
    calc
      (∫ ω,
        centered ω * D ω
          * (unequalFixedDifferenceFourRealCanonicalR
              m θ (P ω) - θ) ∂ℙ)
          =
        ∫ ω, centered ω * baseFactor ω ∂ℙ := by
          apply integral_congr_ae
          filter_upwards [] with ω
          dsimp only [baseFactor]
          ring
      _ =
        (∫ ω, centered ω ∂ℙ)
          * ∫ ω, baseFactor ω ∂ℙ := by
            exact
              hcentered_base.integral_fun_mul_eq_mul_integral
                hcentered_meas.aestronglyMeasurable
                hbaseFactor_meas.aestronglyMeasurable
      _ = 0 := by
        rw [hcentered_zero, zero_mul]
  have hcross_clipped_zero :
      (∫ ω,
        centered ω * D ω
          * (unequalFixedDifferenceFourRealCanonicalClippedWeight
              m (unequalFixedDifferenceFourRealEpsilon m)
              θ (P ω) (L ω) (V ω) - θ) ∂ℙ) = 0 := by
    calc
      (∫ ω,
        centered ω * D ω
          * (unequalFixedDifferenceFourRealCanonicalClippedWeight
              m (unequalFixedDifferenceFourRealEpsilon m)
              θ (P ω) (L ω) (V ω) - θ) ∂ℙ)
          =
        ∫ ω, centered ω * clippedFactor ω ∂ℙ := by
          apply integral_congr_ae
          filter_upwards [] with ω
          dsimp only [clippedFactor]
          ring
      _ =
        (∫ ω, centered ω ∂ℙ)
          * ∫ ω, clippedFactor ω ∂ℙ := by
            exact
              hcentered_clipped.integral_fun_mul_eq_mul_integral
                hcentered_meas.aestronglyMeasurable
                hclippedFactor_meas.aestronglyMeasurable
      _ = 0 := by
        rw [hcentered_zero, zero_mul]

  exact
    unequalFixedDifferenceFourRealCanonicalClippedEstimatorRiskDifference_neg_of_component_laws
      hm μ varianceSum θ centered D P L ℙ
      hvarianceSum hθ0 hθ1 hP hL
      (by simpa only [V] using hV)
      (by simpa only [V] using hP_LV)
      (by simpa only [V] using hVL)
      hcentered_sq
      (by simpa only [V] using hcross_clipped)
      hcross_base
      (by simpa only [V] using hquadratic_clipped)
      hquadratic_base
      (by simpa only [V] using hcross_clipped_zero)
      hcross_base_zero

end

end GraybillDeal
