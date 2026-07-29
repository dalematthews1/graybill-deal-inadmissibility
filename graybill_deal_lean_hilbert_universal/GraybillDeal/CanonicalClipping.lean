import GraybillDeal.Canonical

/-!
# Clipping the canonical competitor

This file completes the deterministic clipping step in the canonical
probability-law bridge.  The perturbed weight is projected onto `[0,1]`.
Because `canonicalTheta s ∈ [0,1]`, this projection cannot increase its
squared distance from the target weight.  Multiplication by `D²` and
integration therefore show that clipping cannot increase the risk.

The estimator-level theorem assumes only the integrability and orthogonality
conditions needed to decompose the risks of the *clipped* competitor and the
Graybill--Deal baseline.  It does not assume the corresponding conditions for
the un-clipped competitor.  Integrability of the un-clipped risk difference
is instead derived from `CanonicalMomentBridge13`.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The canonical perturbed weight projected onto the admissible interval. -/
def canonicalClippedWeight13 (ε s p l v : ℝ) : ℝ :=
  clip01 (canonicalWeight13 ε s p l v)

/--
Pointwise, clipping the perturbed weight cannot increase its squared distance
from the true canonical weight `canonicalTheta s`.
-/
theorem canonicalClippedWeight13_sq_sub_le
    {ε s p l v : ℝ} (hs : |s| < 1) :
    (canonicalClippedWeight13 ε s p l v - canonicalTheta s) ^ 2
      ≤
    (canonicalWeight13 ε s p l v - canonicalTheta s) ^ 2 := by
  unfold canonicalClippedWeight13
  exact clip01_sq_sub_le_sq_sub _ _ (canonicalTheta_mem_Icc hs)

/--
Clipped estimator-level probability bridge.

The seven analytic assumptions after `hbridge` are precisely those consumed by
`sqRisk_weight_difference` for the clipped weight and the baseline:

* square-integrability of the common centered error;
* integrability and zero expectation of the two cross terms;
* integrability of the two quadratic terms.

No cross-term or individual quadratic-integrability assumption is made for
the un-clipped weight.  Its *difference* from the baseline is integrable by
the two moment conditions in `hbridge`.
-/
theorem canonicalClippedEstimatorRiskDifference13_neg
    (μ varianceSum Ka s : ℝ) (centered D P L : Ω → ℝ) (ℙ : Measure Ω)
    (hvarianceSum : 0 < varianceSum) (hKa : 0 < Ka) (hs : |s| < 1)
    (hbridge :
      CanonicalMomentBridge13 Ka s P L
        (fun ω => standardizedDifference13 varianceSum (D ω)) ℙ)
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
  let V : Ω → ℝ := fun ω =>
    standardizedDifference13 varianceSum (D ω)
  let w : Ω → ℝ := fun ω =>
    canonicalWeight13 epsilon13 s (P ω) (L ω) (V ω)
  let wc : Ω → ℝ := fun ω => clip01 (w ω)
  let r : Ω → ℝ := fun ω => canonicalR s (P ω)
  let linear : Ω → ℝ := fun ω =>
    V ω * (r ω - canonicalTheta s)
      * canonicalH13 s (P ω) (L ω) (V ω)
  let quadratic : Ω → ℝ := fun ω =>
    V ω * (canonicalH13 s (P ω) (L ω) (V ω)) ^ 2

  have hnormalized_integrable :
      Integrable
        (fun ω =>
          V ω *
            ((w ω - canonicalTheta s) ^ 2
              - (r ω - canonicalTheta s) ^ 2)) ℙ := by
    have hsum :
        Integrable
          (fun ω =>
            2 * epsilon13 * linear ω
              + epsilon13 ^ 2 * quadratic ω) ℙ :=
      (hbridge.linear_integrable.const_mul
          (2 * epsilon13)).add
        (hbridge.quadratic_integrable.const_mul (epsilon13 ^ 2))
    apply hsum.congr
    filter_upwards [] with ω
    dsimp only [w, r, linear, quadratic]
    unfold canonicalWeight13
    rw [perturbation_sq_sub_diff]
    ring

  have hunclipped_difference_integrable :
      Integrable
        (fun ω =>
          (D ω) ^ 2
            * ((w ω - canonicalTheta s) ^ 2
              - (r ω - canonicalTheta s) ^ 2)) ℙ := by
    have hscaled :=
      hnormalized_integrable.const_mul (varianceSum / 13)
    apply hscaled.congr
    filter_upwards [] with ω
    dsimp only [V]
    rw [← scale_standardizedDifference13 varianceSum (D ω)
      (ne_of_gt hvarianceSum)]
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
            * (canonicalClippedWeight13 epsilon13 s (P ω) (L ω)
                (standardizedDifference13 varianceSum (D ω))
              - canonicalTheta s) ^ 2
          - (D ω) ^ 2
            * (canonicalR s (P ω) - canonicalTheta s) ^ 2
        =
      (D ω) ^ 2
        * ((wc ω - canonicalTheta s) ^ 2
          - (r ω - canonicalTheta s) ^ 2)
    dsimp only [wc, w, r, V]
    unfold canonicalClippedWeight13
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
    have hmul := mul_le_mul_of_nonneg_left hclip (sq_nonneg (D ω))
    linarith

  have hrisk :=
    sqRisk_weight_difference μ (canonicalTheta s)
      centered D wc r ℙ hcentered_sq hcross_clipped hcross_base
      hquadratic_clipped hquadratic_base
      hcross_clipped_zero hcross_base_zero
  have hnormalized :
      canonicalNormalizedRiskDifference13 epsilon13 s P L V ℙ < 0 :=
    canonicalNormalizedRiskDifference13_neg Ka s P L V ℙ
      hKa hs hbridge
  have hscale : 0 < varianceSum / 13 := by positivity
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
            hunclipped_difference_integrable
            hpointwise
    _ =
      varianceSum / 13
        * canonicalNormalizedRiskDifference13 epsilon13 s P L V ℙ := by
          unfold canonicalNormalizedRiskDifference13
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with ω
          dsimp only [V, w, r]
          rw [← scale_standardizedDifference13 varianceSum (D ω)
            (ne_of_gt hvarianceSum)]
          ring
    _ < 0 := mul_neg_of_pos_of_neg hscale hnormalized

end

end GraybillDeal
