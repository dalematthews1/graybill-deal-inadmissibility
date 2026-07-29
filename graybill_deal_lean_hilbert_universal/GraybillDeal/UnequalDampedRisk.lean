import GraybillDeal.Risk
import Mathlib.Tactic.FieldSimp

/-!
# Deterministic risk bridge for the unequal-size damped perturbation

This module is deliberately independent of the particular one-sided
coordinates and probability laws used by the fixed `(13,17)` certificate.
It packages the two normalized moments

`B = E[V (R-θ) H]`,  `C = E[V H²]`

and proves that the un-clipped normalized risk difference is exactly

`2 ε B + ε² C`.

The final theorem combines that identity with projection onto `[0,1]` and
the general squared-risk decomposition.  Later modules only need to supply
the component-law moment bridge and the usual centered-error orthogonality
hypotheses.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The un-clipped perturbation of an arbitrary base weight. -/
def unequalDampedPerturbedWeight (ε r h : ℝ) : ℝ :=
  perturbation r ε h

/-- Projection of the perturbed weight onto the admissible weight interval. -/
def unequalDampedClippedWeight (ε r h : ℝ) : ℝ :=
  clip01 (unequalDampedPerturbedWeight ε r h)

/-- The normalization `V = D² / λ` for the squared mean difference. -/
def unequalStandardizedDifference (varianceSum d : ℝ) : ℝ :=
  d ^ 2 / varianceSum

theorem unequalStandardizedDifference_nonneg
    {varianceSum d : ℝ} (hvarianceSum : 0 < varianceSum) :
    0 ≤ unequalStandardizedDifference varianceSum d := by
  unfold unequalStandardizedDifference
  positivity

theorem scale_unequalStandardizedDifference
    (varianceSum d : ℝ) (hvarianceSum : varianceSum ≠ 0) :
    varianceSum * unequalStandardizedDifference varianceSum d = d ^ 2 := by
  unfold unequalStandardizedDifference
  field_simp

/--
The normalized quadratic-risk difference for an arbitrary base weight `R`
and perturbation direction `H`.
-/
def unequalDampedNormalizedRiskDifference
    (θ ε : ℝ) (R H V : Ω → ℝ) (ℙ : Measure Ω) : ℝ :=
  ∫ ω,
    V ω *
      ((unequalDampedPerturbedWeight ε (R ω) (H ω) - θ) ^ 2
        - (R ω - θ) ^ 2) ∂ℙ

/--
The exact two-moment interface used by the unequal-size risk calculation.
-/
structure UnequalDampedMomentBridge
    (θ B C : ℝ) (R H V : Ω → ℝ) (ℙ : Measure Ω) : Prop where
  linear_integrable :
    Integrable (fun ω => V ω * (R ω - θ) * H ω) ℙ
  quadratic_integrable :
    Integrable (fun ω => V ω * (H ω) ^ 2) ℙ
  linear_moment :
    (∫ ω, V ω * (R ω - θ) * H ω ∂ℙ) = B
  quadratic_moment :
    (∫ ω, V ω * (H ω) ^ 2 ∂ℙ) = C

/--
The normalized risk difference is exactly the reduced quadratic
`2 ε B + ε² C`.
-/
theorem unequalDampedNormalizedRiskDifference_eq
    (θ ε B C : ℝ) (R H V : Ω → ℝ) (ℙ : Measure Ω)
    (hbridge : UnequalDampedMomentBridge θ B C R H V ℙ) :
    unequalDampedNormalizedRiskDifference θ ε R H V ℙ
      = 2 * ε * B + ε ^ 2 * C := by
  let linear : Ω → ℝ :=
    fun ω => V ω * (R ω - θ) * H ω
  let quadratic : Ω → ℝ :=
    fun ω => V ω * (H ω) ^ 2
  have hpointwise :
      ∀ ω,
        V ω *
            ((unequalDampedPerturbedWeight ε (R ω) (H ω) - θ) ^ 2
              - (R ω - θ) ^ 2)
          =
        2 * ε * linear ω + ε ^ 2 * quadratic ω := by
    intro ω
    unfold unequalDampedPerturbedWeight
    rw [perturbation_sq_sub_diff]
    dsimp only [linear, quadratic]
    ring
  unfold unequalDampedNormalizedRiskDifference
  calc
    (∫ ω,
      V ω *
        ((unequalDampedPerturbedWeight ε (R ω) (H ω) - θ) ^ 2
          - (R ω - θ) ^ 2) ∂ℙ)
        =
      ∫ ω, 2 * ε * linear ω + ε ^ 2 * quadratic ω ∂ℙ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact hpointwise ω
    _ =
      (∫ ω, 2 * ε * linear ω ∂ℙ)
        + ∫ ω, ε ^ 2 * quadratic ω ∂ℙ := by
          exact integral_add
            (hbridge.linear_integrable.const_mul (2 * ε))
            (hbridge.quadratic_integrable.const_mul (ε ^ 2))
    _ =
      2 * ε * (∫ ω, linear ω ∂ℙ)
        + ε ^ 2 * (∫ ω, quadratic ω ∂ℙ) := by
          rw [integral_const_mul, integral_const_mul]
    _ = 2 * ε * B + ε ^ 2 * C := by
      rw [show (∫ ω, linear ω ∂ℙ) = B by
            exact hbridge.linear_moment,
        show (∫ ω, quadratic ω ∂ℙ) = C by
            exact hbridge.quadratic_moment]

theorem unequalDampedNormalizedRiskDifference_neg
    (θ ε B C : ℝ) (R H V : Ω → ℝ) (ℙ : Measure Ω)
    (hbridge : UnequalDampedMomentBridge θ B C R H V ℙ)
    (hreduced : 2 * ε * B + ε ^ 2 * C < 0) :
    unequalDampedNormalizedRiskDifference θ ε R H V ℙ < 0 := by
  rw [unequalDampedNormalizedRiskDifference_eq
    θ ε B C R H V ℙ hbridge]
  exact hreduced

theorem unequalDampedClippedWeight_sq_sub_le
    {θ ε r h : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    (unequalDampedClippedWeight ε r h - θ) ^ 2
      ≤ (unequalDampedPerturbedWeight ε r h - θ) ^ 2 := by
  unfold unequalDampedClippedWeight
  exact clip01_sq_sub_le_sq_sub _ _ hθ

/--
Estimator-level clipped risk bridge.

The normalized variable is `V = D² / varianceSum`, so multiplying the
normalized risk difference by the strictly positive `varianceSum` recovers
the actual quadratic part of the squared-risk difference.
-/
theorem unequalDampedClippedEstimatorRiskDifference_neg
    (μ varianceSum θ ε B C : ℝ)
    (centered D R H : Ω → ℝ) (ℙ : Measure Ω)
    (hvarianceSum : 0 < varianceSum)
    (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hbridge :
      UnequalDampedMomentBridge θ B C R H
        (fun ω => unequalStandardizedDifference varianceSum (D ω)) ℙ)
    (hreduced : 2 * ε * B + ε ^ 2 * C < 0)
    (hcentered_sq : Integrable (fun ω => (centered ω) ^ 2) ℙ)
    (hcross_clipped :
      Integrable
        (fun ω =>
          centered ω * D ω
            * (unequalDampedClippedWeight ε (R ω) (H ω) - θ)) ℙ)
    (hcross_base :
      Integrable (fun ω => centered ω * D ω * (R ω - θ)) ℙ)
    (hquadratic_clipped :
      Integrable
        (fun ω =>
          (D ω) ^ 2
            * (unequalDampedClippedWeight ε (R ω) (H ω) - θ) ^ 2) ℙ)
    (hquadratic_base :
      Integrable (fun ω => (D ω) ^ 2 * (R ω - θ) ^ 2) ℙ)
    (hcross_clipped_zero :
      (∫ ω,
        centered ω * D ω
          * (unequalDampedClippedWeight ε (R ω) (H ω) - θ) ∂ℙ) = 0)
    (hcross_base_zero :
      (∫ ω, centered ω * D ω * (R ω - θ) ∂ℙ) = 0) :
    sqRisk μ
        (fun ω =>
          μ + centered ω
            + D ω
              * (unequalDampedClippedWeight ε (R ω) (H ω) - θ)) ℙ
      <
    sqRisk μ
        (fun ω => μ + centered ω + D ω * (R ω - θ)) ℙ := by
  let V : Ω → ℝ :=
    fun ω => unequalStandardizedDifference varianceSum (D ω)
  let w : Ω → ℝ :=
    fun ω => unequalDampedPerturbedWeight ε (R ω) (H ω)
  let wc : Ω → ℝ := fun ω => clip01 (w ω)

  have hnormalized_integrable :
      Integrable
        (fun ω =>
          V ω * ((w ω - θ) ^ 2 - (R ω - θ) ^ 2)) ℙ := by
    let linear : Ω → ℝ :=
      fun ω => V ω * (R ω - θ) * H ω
    let quadratic : Ω → ℝ :=
      fun ω => V ω * (H ω) ^ 2
    have hsum :
        Integrable
          (fun ω =>
            2 * ε * linear ω + ε ^ 2 * quadratic ω) ℙ :=
      (hbridge.linear_integrable.const_mul (2 * ε)).add
        (hbridge.quadratic_integrable.const_mul (ε ^ 2))
    apply hsum.congr
    filter_upwards [] with ω
    dsimp only [V, w, linear, quadratic]
    unfold unequalDampedPerturbedWeight
    rw [perturbation_sq_sub_diff]
    ring

  have hunclipped_difference_integrable :
      Integrable
        (fun ω =>
          (D ω) ^ 2 * ((w ω - θ) ^ 2 - (R ω - θ) ^ 2)) ℙ := by
    have hscaled := hnormalized_integrable.const_mul varianceSum
    apply hscaled.congr
    filter_upwards [] with ω
    dsimp only [V]
    rw [← scale_unequalStandardizedDifference
      varianceSum (D ω) (ne_of_gt hvarianceSum)]
    ring

  have hclipped_difference_integrable :
      Integrable
        (fun ω =>
          (D ω) ^ 2 * ((wc ω - θ) ^ 2 - (R ω - θ) ^ 2)) ℙ := by
    apply (hquadratic_clipped.sub hquadratic_base).congr
    filter_upwards [] with ω
    change
      (D ω) ^ 2
            * (unequalDampedClippedWeight ε (R ω) (H ω) - θ) ^ 2
          - (D ω) ^ 2 * (R ω - θ) ^ 2
        =
      (D ω) ^ 2 * ((wc ω - θ) ^ 2 - (R ω - θ) ^ 2)
    dsimp only [wc, w]
    unfold unequalDampedClippedWeight
    ring

  have hpointwise :
      ∀ ω,
        (D ω) ^ 2 * ((wc ω - θ) ^ 2 - (R ω - θ) ^ 2)
          ≤
        (D ω) ^ 2 * ((w ω - θ) ^ 2 - (R ω - θ) ^ 2) := by
    intro ω
    have hclip : (wc ω - θ) ^ 2 ≤ (w ω - θ) ^ 2 := by
      dsimp only [wc]
      exact clip01_sq_sub_le_sq_sub _ _ hθ
    have hmul :=
      mul_le_mul_of_nonneg_left hclip (sq_nonneg (D ω))
    linarith

  have hrisk :=
    sqRisk_weight_difference μ θ centered D wc R ℙ
      hcentered_sq hcross_clipped hcross_base
      hquadratic_clipped hquadratic_base
      hcross_clipped_zero hcross_base_zero
  have hnormalized :
      unequalDampedNormalizedRiskDifference
        θ ε R H V ℙ < 0 :=
    unequalDampedNormalizedRiskDifference_neg
      θ ε B C R H V ℙ hbridge hreduced
  have hscale : 0 < varianceSum := hvarianceSum
  rw [sub_lt_zero.symm]
  change
    sqRisk μ
        (fun ω => μ + centered ω + D ω * (wc ω - θ)) ℙ
      -
      sqRisk μ
        (fun ω => μ + centered ω + D ω * (R ω - θ)) ℙ
      < 0
  rw [hrisk]
  calc
    (∫ ω,
      (D ω) ^ 2 * ((wc ω - θ) ^ 2 - (R ω - θ) ^ 2) ∂ℙ)
        ≤
      ∫ ω,
        (D ω) ^ 2 * ((w ω - θ) ^ 2 - (R ω - θ) ^ 2) ∂ℙ := by
          exact integral_mono hclipped_difference_integrable
            hunclipped_difference_integrable hpointwise
    _ =
      varianceSum
        * unequalDampedNormalizedRiskDifference θ ε R H V ℙ := by
          unfold unequalDampedNormalizedRiskDifference
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with ω
          dsimp only [V, w]
          rw [← scale_unequalStandardizedDifference
            varianceSum (D ω) (ne_of_gt hvarianceSum)]
          ring
    _ < 0 := mul_neg_of_pos_of_neg hscale hnormalized

end

end GraybillDeal
