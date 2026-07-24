import GraybillDeal.GeneralCanonical

/-!
# Clipping the generalized canonical competitor

Projection of the generic perturbed weight onto `[0,1]` can only decrease
its squared distance from the true variance-ratio weight.  This turns the
un-clipped all-sample-size bridge into an estimator-level clipped risk
comparison.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

def generalCanonicalClippedWeight
    (ε ν s p l v : ℝ) : ℝ :=
  clip01 (generalCanonicalWeight ε ν s p l v)

theorem generalCanonicalClippedWeight_sq_sub_le
    {ε ν s p l v : ℝ} (hs : |s| < 1) :
    (generalCanonicalClippedWeight ε ν s p l v - canonicalTheta s) ^ 2
      ≤
    (generalCanonicalWeight ε ν s p l v - canonicalTheta s) ^ 2 := by
  unfold generalCanonicalClippedWeight
  exact clip01_sq_sub_le_sq_sub _ _ (canonicalTheta_mem_Icc hs)

/--
Clipped estimator-level bridge at arbitrary residual degrees of freedom.
-/
theorem generalCanonicalClippedEstimatorRiskDifference_neg
    (ν : ℕ) (hν : 9 ≤ ν)
    (μ varianceSum Ka ε s : ℝ)
    (centered D P L : Ω → ℝ) (ℙ : Measure Ω)
    (hvarianceSum : 0 < varianceSum) (hs : |s| < 1)
    (hbridge :
      GeneralCanonicalMomentBridge Ka (ν : ℝ) s P L
        (fun ω =>
          generalStandardizedDifference (ν : ℝ)
            varianceSum (D ω)) ℙ)
    (hreduced :
      2 * ε * generalBtheta Ka (ν : ℝ) s
        + ε ^ 2 * generalCtheta Ka (ν : ℝ) s < 0)
    (hcentered_sq : Integrable (fun ω => (centered ω) ^ 2) ℙ)
    (hcross_clipped :
      Integrable
        (fun ω =>
          centered ω * D ω
            * (generalCanonicalClippedWeight ε (ν : ℝ) s
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
            * (generalCanonicalClippedWeight ε (ν : ℝ) s
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
          * (generalCanonicalClippedWeight ε (ν : ℝ) s
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
            * (generalCanonicalClippedWeight ε (ν : ℝ) s
                (P ω) (L ω)
                (generalStandardizedDifference (ν : ℝ)
                  varianceSum (D ω))
              - canonicalTheta s)) ℙ
      <
    sqRisk μ
        (fun ω =>
          μ + centered ω
            + D ω * (canonicalR s (P ω) - canonicalTheta s)) ℙ := by
  let V : Ω → ℝ :=
    fun ω =>
      generalStandardizedDifference (ν : ℝ) varianceSum (D ω)
  let w : Ω → ℝ :=
    fun ω =>
      generalCanonicalWeight ε (ν : ℝ) s (P ω) (L ω) (V ω)
  let wc : Ω → ℝ := fun ω => clip01 (w ω)
  let r : Ω → ℝ := fun ω => canonicalR s (P ω)
  let linear : Ω → ℝ :=
    fun ω =>
      V ω * (r ω - canonicalTheta s)
        * generalCanonicalH (ν : ℝ) s (P ω) (L ω) (V ω)
  let quadratic : Ω → ℝ :=
    fun ω =>
      V ω
        * (generalCanonicalH (ν : ℝ) s
            (P ω) (L ω) (V ω)) ^ 2

  have hnormalized_integrable :
      Integrable
        (fun ω =>
          V ω *
            ((w ω - canonicalTheta s) ^ 2
              - (r ω - canonicalTheta s) ^ 2)) ℙ := by
    have hsum :
        Integrable
          (fun ω =>
            2 * ε * linear ω + ε ^ 2 * quadratic ω) ℙ :=
      (hbridge.linear_integrable.const_mul (2 * ε)).add
        (hbridge.quadratic_integrable.const_mul (ε ^ 2))
    apply hsum.congr
    filter_upwards [] with ω
    dsimp only [w, r, linear, quadratic]
    unfold generalCanonicalWeight
    rw [perturbation_sq_sub_diff]
    ring

  have hνplus : (0 : ℝ) < (ν : ℝ) + 1 := by positivity
  have hunclipped_difference_integrable :
      Integrable
        (fun ω =>
          (D ω) ^ 2
            * ((w ω - canonicalTheta s) ^ 2
              - (r ω - canonicalTheta s) ^ 2)) ℙ := by
    have hscaled :=
      hnormalized_integrable.const_mul
        (varianceSum / ((ν : ℝ) + 1))
    apply hscaled.congr
    filter_upwards [] with ω
    dsimp only [V]
    rw [← scale_generalStandardizedDifference
      (ν : ℝ) varianceSum (D ω)
      (ne_of_gt hvarianceSum) (ne_of_gt hνplus)]
    ring

  have hclipped_difference_integrable :
      Integrable
        (fun ω =>
          (D ω) ^ 2
            * ((wc ω - canonicalTheta s) ^ 2
              - (r ω - canonicalTheta s) ^ 2)) ℙ := by
    apply (hquadratic_clipped.sub hquadratic_base).congr
    filter_upwards [] with ω
    change
      (D ω) ^ 2
            * (generalCanonicalClippedWeight ε (ν : ℝ) s
                (P ω) (L ω)
                (generalStandardizedDifference (ν : ℝ)
                  varianceSum (D ω))
              - canonicalTheta s) ^ 2
          - (D ω) ^ 2
            * (canonicalR s (P ω) - canonicalTheta s) ^ 2
        =
      (D ω) ^ 2
        * ((wc ω - canonicalTheta s) ^ 2
          - (r ω - canonicalTheta s) ^ 2)
    dsimp only [wc, w, r, V]
    unfold generalCanonicalClippedWeight
    ring

  have hpointwise :
      ∀ ω,
        (D ω) ^ 2
            * ((wc ω - canonicalTheta s) ^ 2
              - (r ω - canonicalTheta s) ^ 2)
          ≤
        (D ω) ^ 2
            * ((w ω - canonicalTheta s) ^ 2
              - (r ω - canonicalTheta s) ^ 2) := by
    intro ω
    have hclip :
        (wc ω - canonicalTheta s) ^ 2
          ≤ (w ω - canonicalTheta s) ^ 2 := by
      dsimp only [wc]
      exact clip01_sq_sub_le_sq_sub _ _
        (canonicalTheta_mem_Icc hs)
    have hmul :=
      mul_le_mul_of_nonneg_left hclip (sq_nonneg (D ω))
    linarith

  have hrisk :=
    sqRisk_weight_difference μ (canonicalTheta s)
      centered D wc r ℙ hcentered_sq hcross_clipped hcross_base
      hquadratic_clipped hquadratic_base
      hcross_clipped_zero hcross_base_zero
  have hnormalized :
      generalCanonicalNormalizedRiskDifference
        ε (ν : ℝ) s P L V ℙ < 0 :=
    generalCanonicalNormalizedRiskDifference_neg
      Ka ε (ν : ℝ) s P L V ℙ hbridge hreduced
  have hscale :
      0 < varianceSum / ((ν : ℝ) + 1) := by positivity
  rw [sub_lt_zero.symm]
  change
    sqRisk μ
        (fun ω =>
          μ + centered ω + D ω * (wc ω - canonicalTheta s)) ℙ
      -
      sqRisk μ
        (fun ω =>
          μ + centered ω + D ω * (r ω - canonicalTheta s)) ℙ
      < 0
  rw [hrisk]
  calc
    (∫ ω,
      (D ω) ^ 2
        * ((wc ω - canonicalTheta s) ^ 2
          - (r ω - canonicalTheta s) ^ 2) ∂ℙ)
        ≤
      ∫ ω,
        (D ω) ^ 2
          * ((w ω - canonicalTheta s) ^ 2
            - (r ω - canonicalTheta s) ^ 2) ∂ℙ := by
          exact integral_mono hclipped_difference_integrable
            hunclipped_difference_integrable hpointwise
    _ =
      varianceSum / ((ν : ℝ) + 1)
        * generalCanonicalNormalizedRiskDifference
          ε (ν : ℝ) s P L V ℙ := by
            unfold generalCanonicalNormalizedRiskDifference
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards [] with ω
            dsimp only [V, w, r]
            rw [← scale_generalStandardizedDifference
              (ν : ℝ) varianceSum (D ω)
              (ne_of_gt hvarianceSum) (ne_of_gt hνplus)]
            ring
    _ < 0 := mul_neg_of_pos_of_neg hscale hnormalized

end

end GraybillDeal
