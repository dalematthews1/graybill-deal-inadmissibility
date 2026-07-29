import GraybillDeal.UnequalDampedCanonical
import GraybillDeal.UnequalDampedEnvelopeIntegrals
import GraybillDeal.UnequalDampedMomentIntegrals

/-!
# Reduced risk certificate for the damped `(13,17)` construction

This module joins the two one-sided analytic estimates to the fixed
perturbation size.  On the side `θ ≥ 3/7` we use the coordinate

`s = (7θ-3)/(4θ)` and `Y = 1-P ~ Beta(8,6)`.

On the side `θ < 3/7` we swap the two samples, use

`s = (3-7θ)/(3(1-θ))`, and retain `Y=P ~ Beta(6,8)`.

The one-sided linear coefficients are the positive coordinate prefactors
times `unequalDampedPlusH` and `unequalDampedMinusH`.  The corresponding
quadratic coefficients are precisely the beta expectations already bounded
in `UnequalDampedEnvelopeIntegrals`.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- The original-side reduced linear coefficient in the `s` chart. -/
def unequalDampedPlusB (s : ℝ) : ℝ :=
  (1 - s) ^ 2 / (1 - (4 / 7 : ℝ) * s)
    * unequalDampedPlusH s

/-- The sample-swapped reduced linear coefficient in the `s` chart. -/
def unequalDampedMinusB (s : ℝ) : ℝ :=
  (1 - s) ^ 2 / (1 - (3 / 7 : ℝ) * s)
    * unequalDampedMinusH s

/-- The original-side reduced quadratic coefficient in the `s` chart. -/
def unequalDampedPlusC (s : ℝ) : ℝ :=
  ∫ y,
    unequalDampedPhi (3 / 7) unequalDampedKappa13_17
          (unequalDampedR s y) ^ 2
      * unequalDampedCKernel13_17 (unequalDampedU (4 / 7) s y)
    ∂betaMeasure 8 6

/-- The sample-swapped reduced quadratic coefficient in the `s` chart. -/
def unequalDampedMinusC (s : ℝ) : ℝ :=
  ∫ y,
    unequalDampedPhi (4 / 7) (-unequalDampedKappa13_17)
          (unequalDampedR s y) ^ 2
      * unequalDampedCKernel13_17 (unequalDampedU (3 / 7) s y)
    ∂betaMeasure 6 8

private theorem oneSided_prefactor_nonneg
    {q s : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    0 ≤ (1 - s) ^ 2 / (1 - q * s) := by
  exact div_nonneg (sq_nonneg _)
    (one_sub_qs_pos hq0 hq1 hs0 hs1).le

private theorem neg_b0_prefactor_le
    {q s : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (1 - s) ^ 2 / (1 - q * s) * (-unequalDampedB0)
      ≤ -unequalDampedB0 * (1 - s) ^ 2 := by
  have hdpos : 0 < 1 - q * s :=
    one_sub_qs_pos hq0 hq1 hs0 hs1
  have hdle : 1 - q * s ≤ 1 := by
    have : 0 ≤ q * s := mul_nonneg hq0 hs0
    linarith
  have hnum :
      0 ≤ unequalDampedB0 * (1 - s) ^ 2 :=
    mul_nonneg unequalDampedB0_pos.le (sq_nonneg _)
  have hdiv :
      unequalDampedB0 * (1 - s) ^ 2
        ≤ unequalDampedB0 * (1 - s) ^ 2 / (1 - q * s) := by
    apply (le_div_iff₀ hdpos).2
    calc
      unequalDampedB0 * (1 - s) ^ 2 * (1 - q * s)
          ≤ unequalDampedB0 * (1 - s) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hdle hnum
      _ = unequalDampedB0 * (1 - s) ^ 2 := by ring
  calc
    (1 - s) ^ 2 / (1 - q * s) * (-unequalDampedB0)
        =
      -(unequalDampedB0 * (1 - s) ^ 2 / (1 - q * s)) := by
        ring
    _ ≤ -(unequalDampedB0 * (1 - s) ^ 2) :=
      neg_le_neg hdiv
    _ = -unequalDampedB0 * (1 - s) ^ 2 := by ring

/-- Uniform original-side linear bound. -/
theorem unequalDampedPlusB_le
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalDampedPlusB s
      ≤ -unequalDampedB0 * (1 - s) ^ 2 := by
  have hH := unequalDampedPlusH_le_neg_b0 hs0 hs1
  unfold unequalDampedPlusB
  calc
    (1 - s) ^ 2 / (1 - (4 / 7 : ℝ) * s)
          * unequalDampedPlusH s
        ≤
      (1 - s) ^ 2 / (1 - (4 / 7 : ℝ) * s)
          * (-unequalDampedB0) := by
            exact mul_le_mul_of_nonneg_left hH
              (oneSided_prefactor_nonneg
                (by norm_num) (by norm_num) hs0 hs1)
    _ ≤ -unequalDampedB0 * (1 - s) ^ 2 :=
      neg_b0_prefactor_le
        (by norm_num) (by norm_num) hs0 hs1

/-- Uniform sample-swapped linear bound. -/
theorem unequalDampedMinusB_le
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalDampedMinusB s
      ≤ -unequalDampedB0 * (1 - s) ^ 2 := by
  have hH := unequalDampedMinusH_le_neg_b0 hs0 hs1
  unfold unequalDampedMinusB
  calc
    (1 - s) ^ 2 / (1 - (3 / 7 : ℝ) * s)
          * unequalDampedMinusH s
        ≤
      (1 - s) ^ 2 / (1 - (3 / 7 : ℝ) * s)
          * (-unequalDampedB0) := by
            exact mul_le_mul_of_nonneg_left hH
              (oneSided_prefactor_nonneg
                (by norm_num) (by norm_num) hs0 hs1)
    _ ≤ -unequalDampedB0 * (1 - s) ^ 2 :=
      neg_b0_prefactor_le
        (by norm_num) (by norm_num) hs0 hs1

/-- Uniform original-side quadratic bound. -/
theorem unequalDampedPlusC_le
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalDampedPlusC s
      ≤ unequalDampedMPlus * (1 - s) ^ 2 := by
  simpa only [unequalDampedPlusC] using
    (integral_unequalDampedPlusC_beta_le hs0 hs1)

/-- Uniform sample-swapped quadratic bound. -/
theorem unequalDampedMinusC_le
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalDampedMinusC s
      ≤ unequalDampedMPlus * (1 - s) ^ 2 := by
  simpa only [unequalDampedMinusC] using
    (integral_unequalDampedMinusC_beta_le hs0 hs1)

/-- Fixed-epsilon original-side reduced-risk inequality. -/
theorem unequalDampedPlusReducedRisk_neg
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    2 * unequalDampedEpsilon13_17 * unequalDampedPlusB s
      + unequalDampedEpsilon13_17 ^ 2 * unequalDampedPlusC s < 0 := by
  exact unequalDampedReducedRisk_neg_of_bounds hs1
    (unequalDampedPlusB_le hs0 hs1)
    (unequalDampedPlusC_le hs0 hs1)

/-- Fixed-epsilon sample-swapped reduced-risk inequality. -/
theorem unequalDampedMinusReducedRisk_neg
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    2 * unequalDampedEpsilon13_17 * unequalDampedMinusB s
      + unequalDampedEpsilon13_17 ^ 2 * unequalDampedMinusC s < 0 := by
  exact unequalDampedReducedRisk_neg_of_bounds hs1
    (unequalDampedMinusB_le hs0 hs1)
    (unequalDampedMinusC_le hs0 hs1)

/-! ## Direct canonical coefficients -/

/-- The direct `P`-integrand for the canonical linear coefficient. -/
def unequalDampedCanonicalBIntegrand13_17 (θ p : ℝ) : ℝ :=
  (unequalDampedCanonicalR13_17 θ p - θ)
    * unequalDampedPhi13_17 (unequalDampedCanonicalR13_17 θ p)
    * (unequalDampedC13_17
      - unequalDampedK13_17 / unequalDampedCanonicalDenom13_17 θ p)

/-- The direct `P`-integrand for the canonical quadratic coefficient. -/
def unequalDampedCanonicalCIntegrand13_17 (θ p : ℝ) : ℝ :=
  unequalDampedPhi13_17 (unequalDampedCanonicalR13_17 θ p) ^ 2
    * unequalDampedCKernel13_17
      ((unequalDampedCanonicalDenom13_17 θ p)⁻¹)

/-- The direct canonical linear coefficient under `P ~ Beta(6,8)`. -/
def unequalDampedCanonicalB13_17 (θ : ℝ) : ℝ :=
  ∫ p, unequalDampedCanonicalBIntegrand13_17 θ p
    ∂betaMeasure 6 8

/-- The direct canonical quadratic coefficient under `P ~ Beta(6,8)`. -/
def unequalDampedCanonicalC13_17 (θ : ℝ) : ℝ :=
  ∫ p, unequalDampedCanonicalCIntegrand13_17 θ p
    ∂betaMeasure 6 8

theorem measurable_unequalDampedCanonicalBIntegrand13_17 (θ : ℝ) :
    Measurable (unequalDampedCanonicalBIntegrand13_17 θ) := by
  unfold unequalDampedCanonicalBIntegrand13_17
    unequalDampedCanonicalR13_17 unequalDampedCanonicalDenom13_17
    unequalDampedPhi13_17
  fun_prop

theorem measurable_unequalDampedCanonicalCIntegrand13_17 (θ : ℝ) :
    Measurable (unequalDampedCanonicalCIntegrand13_17 θ) := by
  unfold unequalDampedCanonicalCIntegrand13_17
    unequalDampedCanonicalR13_17 unequalDampedCanonicalDenom13_17
    unequalDampedPhi13_17 unequalDampedCKernel13_17
  fun_prop

/-- The original-side chart parameter. -/
def unequalDampedPlusS (θ : ℝ) : ℝ :=
  (7 * θ - 3) / (4 * θ)

/-- The sample-swapped chart parameter. -/
def unequalDampedMinusS (θ : ℝ) : ℝ :=
  (3 - 7 * θ) / (3 * (1 - θ))

theorem unequalDampedPlusS_nonneg
    {θ : ℝ} (hθ : 3 / 7 ≤ θ) (hθ0 : 0 < θ) :
    0 ≤ unequalDampedPlusS θ := by
  unfold unequalDampedPlusS
  exact div_nonneg (by linarith) (by positivity)

theorem unequalDampedPlusS_lt_one
    {θ : ℝ} (hθ1 : θ < 1) (hθ0 : 0 < θ) :
    unequalDampedPlusS θ < 1 := by
  unfold unequalDampedPlusS
  rw [div_lt_one (by positivity : 0 < 4 * θ)]
  linarith

theorem unequalDampedMinusS_nonneg
    {θ : ℝ} (hθ : θ ≤ 3 / 7) (hθ1 : θ < 1) :
    0 ≤ unequalDampedMinusS θ := by
  unfold unequalDampedMinusS
  exact div_nonneg (by linarith) (by positivity)

theorem unequalDampedMinusS_lt_one
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    unequalDampedMinusS θ < 1 := by
  unfold unequalDampedMinusS
  rw [div_lt_one (by positivity : 0 < 3 * (1 - θ))]
  linarith

theorem unequalDampedTheta_plusS
    {θ : ℝ} (hθ0 : 0 < θ) :
    unequalDampedTheta (3 / 7) (4 / 7) (unequalDampedPlusS θ)
      = θ := by
  unfold unequalDampedTheta unequalDampedPlusS
  field_simp [ne_of_gt hθ0]
  ring

theorem unequalDampedTheta_minusS
    {θ : ℝ} (hθ1 : θ < 1) :
    unequalDampedTheta (4 / 7) (3 / 7) (unequalDampedMinusS θ)
      = 1 - θ := by
  unfold unequalDampedTheta unequalDampedMinusS
  field_simp [ne_of_gt (sub_pos.mpr hθ1)]
  ring

/-- The normalized residual denominator in the original-side chart. -/
theorem unequalDampedCanonicalDenom13_17_plus_chart
    {s y : ℝ} (hqs : 1 - (4 / 7 : ℝ) * s ≠ 0) :
    unequalDampedCanonicalDenom13_17
        (unequalDampedTheta (3 / 7) (4 / 7) s) (1 - y)
      =
    unequalDampedDenom s y / (1 - (4 / 7) * s) := by
  have hden : 7 - 4 * s ≠ 0 := by
    intro hz
    apply hqs
    calc
      1 - (4 / 7 : ℝ) * s = (7 - 4 * s) / 7 := by ring
      _ = 0 := by rw [hz]; norm_num
  unfold unequalDampedCanonicalDenom13_17 unequalDampedTheta
    unequalDampedDenom
  field_simp [hden]
  ring

/-- The canonical weight in the original-side chart. -/
theorem unequalDampedCanonicalR13_17_plus_chart
    {s y : ℝ}
    (hqs : 1 - (4 / 7 : ℝ) * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedCanonicalR13_17
        (unequalDampedTheta (3 / 7) (4 / 7) s) (1 - y)
      =
    unequalDampedR s y := by
  have hden : 7 - 4 * s ≠ 0 := by
    intro hz
    apply hqs
    calc
      1 - (4 / 7 : ℝ) * s = (7 - 4 * s) / 7 := by ring
      _ = 0 := by rw [hz]; norm_num
  rw [unequalDampedCanonicalR13_17,
    unequalDampedCanonicalDenom13_17_plus_chart hqs]
  unfold unequalDampedTheta unequalDampedR
  field_simp [hden, hsy]

/-- The reciprocal canonical denominator in the original-side chart. -/
theorem unequalDampedCanonicalDenom13_17_inv_plus_chart
    {s y : ℝ}
    (hqs : 1 - (4 / 7 : ℝ) * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    (unequalDampedCanonicalDenom13_17
        (unequalDampedTheta (3 / 7) (4 / 7) s) (1 - y))⁻¹
      =
    unequalDampedU (4 / 7) s y := by
  rw [unequalDampedCanonicalDenom13_17_plus_chart hqs]
  unfold unequalDampedU
  field_simp [hqs, hsy]

/-- The normalized residual denominator in the sample-swapped chart. -/
theorem unequalDampedCanonicalDenom13_17_minus_chart
    {s y : ℝ} (hqs : 1 - (3 / 7 : ℝ) * s ≠ 0) :
    unequalDampedCanonicalDenom13_17
        (1 - unequalDampedTheta (4 / 7) (3 / 7) s) y
      =
    unequalDampedDenom s y / (1 - (3 / 7) * s) := by
  have hden : 7 - 3 * s ≠ 0 := by
    intro hz
    apply hqs
    calc
      1 - (3 / 7 : ℝ) * s = (7 - 3 * s) / 7 := by ring
      _ = 0 := by rw [hz]; norm_num
  unfold unequalDampedCanonicalDenom13_17 unequalDampedTheta
    unequalDampedDenom
  field_simp [hden]
  ring

/-- Complementing the canonical weight gives the swapped chart weight. -/
theorem one_sub_unequalDampedCanonicalR13_17_minus_chart
    {s y : ℝ}
    (hqs : 1 - (3 / 7 : ℝ) * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    1 - unequalDampedCanonicalR13_17
        (1 - unequalDampedTheta (4 / 7) (3 / 7) s) y
      =
    unequalDampedR s y := by
  have hden : 7 - 3 * s ≠ 0 := by
    intro hz
    apply hqs
    calc
      1 - (3 / 7 : ℝ) * s = (7 - 3 * s) / 7 := by ring
      _ = 0 := by rw [hz]; norm_num
  rw [unequalDampedCanonicalR13_17,
    unequalDampedCanonicalDenom13_17_minus_chart hqs]
  unfold unequalDampedTheta unequalDampedR
  unfold unequalDampedDenom at hsy ⊢
  field_simp [hden, hsy]
  ring

/-- The reciprocal canonical denominator in the sample-swapped chart. -/
theorem unequalDampedCanonicalDenom13_17_inv_minus_chart
    {s y : ℝ}
    (hqs : 1 - (3 / 7 : ℝ) * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    (unequalDampedCanonicalDenom13_17
        (1 - unequalDampedTheta (4 / 7) (3 / 7) s) y)⁻¹
      =
    unequalDampedU (3 / 7) s y := by
  rw [unequalDampedCanonicalDenom13_17_minus_chart hqs]
  unfold unequalDampedU
  field_simp [hqs, hsy]

/-- The fixed direction transforms equivariantly under sample swapping. -/
theorem unequalDampedPhi13_17_swap (r : ℝ) :
    unequalDampedPhi13_17 r
      =
    -unequalDampedPhi (4 / 7) (-unequalDampedKappa13_17) (1 - r) := by
  unfold unequalDampedPhi13_17 unequalDampedPhi unequalDampedInner
  ring

/-- Pointwise original-side identification of the direct `B` integrand. -/
theorem unequalDampedCanonicalBIntegrand13_17_plus_chart
    {s y : ℝ}
    (hqs : 1 - (4 / 7 : ℝ) * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedCanonicalBIntegrand13_17
        (unequalDampedTheta (3 / 7) (4 / 7) s) (1 - y)
      =
    (1 - s) ^ 2 / (1 - (4 / 7) * s)
      *
    (((4 / 7 : ℝ) - y) * y * (1 - y)
        * unequalDampedF (3 / 7) (4 / 7)
          unequalDampedKappa13_17 s y
        * unequalDampedPsiNumerator (4 / 7)
          unequalDampedC13_17 unequalDampedK13_17 s y
      / unequalDampedDenom s y ^ 6) := by
  unfold unequalDampedCanonicalBIntegrand13_17
  rw [unequalDampedCanonicalR13_17_plus_chart hqs hsy]
  rw [show
      unequalDampedK13_17 /
          unequalDampedCanonicalDenom13_17
            (unequalDampedTheta (3 / 7) (4 / 7) s) (1 - y)
        =
      unequalDampedK13_17 * unequalDampedU (4 / 7) s y by
        rw [div_eq_mul_inv,
          unequalDampedCanonicalDenom13_17_inv_plus_chart hqs hsy]]
  rw [← unequalDampedPhi_original_eq]
  exact unequalDampedB_integrand_factorization13_17 hqs hsy

/-- Pointwise swapped-side identification of the direct `B` integrand. -/
theorem unequalDampedCanonicalBIntegrand13_17_minus_chart
    {s y : ℝ}
    (hqs : 1 - (3 / 7 : ℝ) * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedCanonicalBIntegrand13_17
        (1 - unequalDampedTheta (4 / 7) (3 / 7) s) y
      =
    (1 - s) ^ 2 / (1 - (3 / 7) * s)
      *
    (((3 / 7 : ℝ) - y) * y * (1 - y)
        * unequalDampedF (4 / 7) (3 / 7)
          (-unequalDampedKappa13_17) s y
        * unequalDampedPsiNumerator (3 / 7)
          unequalDampedC13_17 unequalDampedK13_17 s y
      / unequalDampedDenom s y ^ 6) := by
  let r := unequalDampedCanonicalR13_17
    (1 - unequalDampedTheta (4 / 7) (3 / 7) s) y
  have hr :
      1 - r = unequalDampedR s y := by
    exact one_sub_unequalDampedCanonicalR13_17_minus_chart hqs hsy
  have hr' :
      r = 1 - unequalDampedR s y := by
    linarith
  unfold unequalDampedCanonicalBIntegrand13_17
  change
    (r - (1 - unequalDampedTheta (4 / 7) (3 / 7) s))
        * unequalDampedPhi13_17 r
        * (unequalDampedC13_17
          - unequalDampedK13_17 /
            unequalDampedCanonicalDenom13_17
              (1 - unequalDampedTheta (4 / 7) (3 / 7) s) y)
      = _
  rw [unequalDampedPhi13_17_swap r]
  rw [show
      unequalDampedK13_17 /
          unequalDampedCanonicalDenom13_17
            (1 - unequalDampedTheta (4 / 7) (3 / 7) s) y
        =
      unequalDampedK13_17 * unequalDampedU (3 / 7) s y by
        rw [div_eq_mul_inv,
          unequalDampedCanonicalDenom13_17_inv_minus_chart hqs hsy]]
  rw [hr, hr']
  convert unequalDampedB_integrand_factorization17_13 hqs hsy using 1 <;>
    ring

/-- Pointwise original-side identification of the direct `C` integrand. -/
theorem unequalDampedCanonicalCIntegrand13_17_plus_chart
    {s y : ℝ}
    (hqs : 1 - (4 / 7 : ℝ) * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedCanonicalCIntegrand13_17
        (unequalDampedTheta (3 / 7) (4 / 7) s) (1 - y)
      =
    unequalDampedPhi (3 / 7) unequalDampedKappa13_17
          (unequalDampedR s y) ^ 2
      * unequalDampedCKernel13_17 (unequalDampedU (4 / 7) s y) := by
  unfold unequalDampedCanonicalCIntegrand13_17
  rw [unequalDampedCanonicalR13_17_plus_chart hqs hsy,
    unequalDampedCanonicalDenom13_17_inv_plus_chart hqs hsy,
    ← unequalDampedPhi_original_eq]

/-- Pointwise swapped-side identification of the direct `C` integrand. -/
theorem unequalDampedCanonicalCIntegrand13_17_minus_chart
    {s y : ℝ}
    (hqs : 1 - (3 / 7 : ℝ) * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedCanonicalCIntegrand13_17
        (1 - unequalDampedTheta (4 / 7) (3 / 7) s) y
      =
    unequalDampedPhi (4 / 7) (-unequalDampedKappa13_17)
          (unequalDampedR s y) ^ 2
      * unequalDampedCKernel13_17 (unequalDampedU (3 / 7) s y) := by
  let r := unequalDampedCanonicalR13_17
    (1 - unequalDampedTheta (4 / 7) (3 / 7) s) y
  have hr :
      1 - r = unequalDampedR s y :=
    one_sub_unequalDampedCanonicalR13_17_minus_chart hqs hsy
  unfold unequalDampedCanonicalCIntegrand13_17
  change
    unequalDampedPhi13_17 r ^ 2
        * unequalDampedCKernel13_17
          ((unequalDampedCanonicalDenom13_17
            (1 - unequalDampedTheta (4 / 7) (3 / 7) s) y)⁻¹)
      = _
  rw [unequalDampedPhi13_17_swap r,
    unequalDampedCanonicalDenom13_17_inv_minus_chart hqs hsy,
    ← hr]
  ring

/-! ## Beta-complement and integral chart identities -/

/--
Complementing a `Beta(6,8)` variable gives a `Beta(8,6)` variable.

This formulation is deliberately stated directly at the level of
expectations, so later chart arguments do not need a separate measurable-map
or pushforward theorem.
-/
theorem integral_betaMeasure_six_eight_eq_complement_eight_six
    (f : ℝ → ℝ) :
    (∫ p, f p ∂betaMeasure 6 8)
      =
    ∫ y, f (1 - y) ∂betaMeasure 8 6 := by
  rw [integral_betaMeasure_six_eight_eq_interval,
    integral_betaMeasure_eight_six_eq_interval]
  calc
    (∫ p in (0 : ℝ)..1,
      unequalDampedMinusDensity p * f p)
        =
      ∫ p in (0 : ℝ)..1,
        (fun y =>
          unequalDampedPlusDensity y * f (1 - y)) (1 - p) := by
            apply intervalIntegral.integral_congr
            intro p _
            unfold unequalDampedPlusDensity unequalDampedMinusDensity
            ring
    _ =
      ∫ y in (0 : ℝ)..1,
        unequalDampedPlusDensity y * f (1 - y) := by
          simpa using
            (intervalIntegral.integral_comp_sub_left
              (fun y : ℝ =>
                unequalDampedPlusDensity y * f (1 - y))
              (a := (0 : ℝ)) (b := 1) 1)

/-- The direct canonical `B` coefficient in the original-side chart. -/
theorem unequalDampedCanonicalB13_17_plus_chart
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalDampedCanonicalB13_17
        (unequalDampedTheta (3 / 7) (4 / 7) s)
      =
    unequalDampedPlusB s := by
  unfold unequalDampedCanonicalB13_17
  rw [integral_betaMeasure_six_eight_eq_complement_eight_six]
  unfold unequalDampedPlusB unequalDampedPlusH
  calc
    (∫ y,
      unequalDampedCanonicalBIntegrand13_17
        (unequalDampedTheta (3 / 7) (4 / 7) s) (1 - y)
      ∂betaMeasure 8 6)
        =
      ∫ y in (0 : ℝ)..1,
        unequalDampedPlusDensity y
          * unequalDampedCanonicalBIntegrand13_17
            (unequalDampedTheta (3 / 7) (4 / 7) s) (1 - y) :=
      integral_betaMeasure_eight_six_eq_interval _
    _ =
      ∫ y in (0 : ℝ)..1,
        (1 - s) ^ 2 / (1 - (4 / 7 : ℝ) * s)
          *
        unequalDampedHIntegrand
          unequalDampedPlusDensity
          (3 / 7) (4 / 7) unequalDampedKappa13_17
          unequalDampedC13_17 unequalDampedK13_17 s y := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hy' : y ∈ Icc (0 : ℝ) 1 := by
              simpa [uIcc_of_le] using hy
            have hqs : 1 - (4 / 7 : ℝ) * s ≠ 0 :=
              ne_of_gt
                (one_sub_qs_pos
                  (by norm_num) (by norm_num) hs0 hs1)
            have hsy : unequalDampedDenom s y ≠ 0 :=
              ne_of_gt
                (unequalDampedDenom_pos hs0 hs1 hy'.1 hy'.2)
            change
              unequalDampedPlusDensity y
                  * unequalDampedCanonicalBIntegrand13_17
                    (unequalDampedTheta (3 / 7) (4 / 7) s) (1 - y)
                =
              (1 - s) ^ 2 / (1 - (4 / 7 : ℝ) * s)
                *
              unequalDampedHIntegrand
                unequalDampedPlusDensity
                (3 / 7) (4 / 7) unequalDampedKappa13_17
                unequalDampedC13_17 unequalDampedK13_17 s y
            rw [unequalDampedCanonicalBIntegrand13_17_plus_chart
              hqs hsy]
            unfold unequalDampedHIntegrand
            ring
    _ =
      (1 - s) ^ 2 / (1 - (4 / 7 : ℝ) * s)
        *
      ∫ y in (0 : ℝ)..1,
        unequalDampedHIntegrand
          unequalDampedPlusDensity
          (3 / 7) (4 / 7) unequalDampedKappa13_17
          unequalDampedC13_17 unequalDampedK13_17 s y := by
            rw [intervalIntegral.integral_const_mul]

/-- The direct canonical `C` coefficient in the original-side chart. -/
theorem unequalDampedCanonicalC13_17_plus_chart
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalDampedCanonicalC13_17
        (unequalDampedTheta (3 / 7) (4 / 7) s)
      =
    unequalDampedPlusC s := by
  unfold unequalDampedCanonicalC13_17
  rw [integral_betaMeasure_six_eight_eq_complement_eight_six]
  calc
    (∫ y,
      unequalDampedCanonicalCIntegrand13_17
        (unequalDampedTheta (3 / 7) (4 / 7) s) (1 - y)
      ∂betaMeasure 8 6)
        =
      ∫ y in (0 : ℝ)..1,
        unequalDampedPlusDensity y
          * unequalDampedCanonicalCIntegrand13_17
            (unequalDampedTheta (3 / 7) (4 / 7) s) (1 - y) :=
      integral_betaMeasure_eight_six_eq_interval _
    _ =
      ∫ y in (0 : ℝ)..1,
        unequalDampedPlusDensity y
          *
        (unequalDampedPhi (3 / 7) unequalDampedKappa13_17
              (unequalDampedR s y) ^ 2
          * unequalDampedCKernel13_17
              (unequalDampedU (4 / 7) s y)) := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hy' : y ∈ Icc (0 : ℝ) 1 := by
              simpa [uIcc_of_le] using hy
            have hqs : 1 - (4 / 7 : ℝ) * s ≠ 0 :=
              ne_of_gt
                (one_sub_qs_pos
                  (by norm_num) (by norm_num) hs0 hs1)
            have hsy : unequalDampedDenom s y ≠ 0 :=
              ne_of_gt
                (unequalDampedDenom_pos hs0 hs1 hy'.1 hy'.2)
            change
              unequalDampedPlusDensity y
                  * unequalDampedCanonicalCIntegrand13_17
                    (unequalDampedTheta (3 / 7) (4 / 7) s) (1 - y)
                =
              unequalDampedPlusDensity y
                *
              (unequalDampedPhi (3 / 7) unequalDampedKappa13_17
                    (unequalDampedR s y) ^ 2
                * unequalDampedCKernel13_17
                    (unequalDampedU (4 / 7) s y))
            rw [unequalDampedCanonicalCIntegrand13_17_plus_chart
              hqs hsy]
    _ =
      ∫ y,
        unequalDampedPhi (3 / 7) unequalDampedKappa13_17
            (unequalDampedR s y) ^ 2
          * unequalDampedCKernel13_17
            (unequalDampedU (4 / 7) s y)
        ∂betaMeasure 8 6 := by
          symm
          exact integral_betaMeasure_eight_six_eq_interval _
    _ = unequalDampedPlusC s := rfl

/-- The direct canonical `B` coefficient in the sample-swapped chart. -/
theorem unequalDampedCanonicalB13_17_minus_chart
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalDampedCanonicalB13_17
        (1 - unequalDampedTheta (4 / 7) (3 / 7) s)
      =
    unequalDampedMinusB s := by
  unfold unequalDampedCanonicalB13_17 unequalDampedMinusB
    unequalDampedMinusH
  calc
    (∫ y,
      unequalDampedCanonicalBIntegrand13_17
        (1 - unequalDampedTheta (4 / 7) (3 / 7) s) y
      ∂betaMeasure 6 8)
        =
      ∫ y in (0 : ℝ)..1,
        unequalDampedMinusDensity y
          * unequalDampedCanonicalBIntegrand13_17
            (1 - unequalDampedTheta (4 / 7) (3 / 7) s) y :=
      integral_betaMeasure_six_eight_eq_interval _
    _ =
      ∫ y in (0 : ℝ)..1,
        (1 - s) ^ 2 / (1 - (3 / 7 : ℝ) * s)
          *
        unequalDampedHIntegrand
          unequalDampedMinusDensity
          (4 / 7) (3 / 7) (-unequalDampedKappa13_17)
          unequalDampedC13_17 unequalDampedK13_17 s y := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hy' : y ∈ Icc (0 : ℝ) 1 := by
              simpa [uIcc_of_le] using hy
            have hqs : 1 - (3 / 7 : ℝ) * s ≠ 0 :=
              ne_of_gt
                (one_sub_qs_pos
                  (by norm_num) (by norm_num) hs0 hs1)
            have hsy : unequalDampedDenom s y ≠ 0 :=
              ne_of_gt
                (unequalDampedDenom_pos hs0 hs1 hy'.1 hy'.2)
            change
              unequalDampedMinusDensity y
                  * unequalDampedCanonicalBIntegrand13_17
                    (1 - unequalDampedTheta (4 / 7) (3 / 7) s) y
                =
              (1 - s) ^ 2 / (1 - (3 / 7 : ℝ) * s)
                *
              unequalDampedHIntegrand
                unequalDampedMinusDensity
                (4 / 7) (3 / 7) (-unequalDampedKappa13_17)
                unequalDampedC13_17 unequalDampedK13_17 s y
            rw [unequalDampedCanonicalBIntegrand13_17_minus_chart
              hqs hsy]
            unfold unequalDampedHIntegrand
            ring
    _ =
      (1 - s) ^ 2 / (1 - (3 / 7 : ℝ) * s)
        *
      ∫ y in (0 : ℝ)..1,
        unequalDampedHIntegrand
          unequalDampedMinusDensity
          (4 / 7) (3 / 7) (-unequalDampedKappa13_17)
          unequalDampedC13_17 unequalDampedK13_17 s y := by
            rw [intervalIntegral.integral_const_mul]

/-- The direct canonical `C` coefficient in the sample-swapped chart. -/
theorem unequalDampedCanonicalC13_17_minus_chart
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalDampedCanonicalC13_17
        (1 - unequalDampedTheta (4 / 7) (3 / 7) s)
      =
    unequalDampedMinusC s := by
  unfold unequalDampedCanonicalC13_17
  calc
    (∫ y,
      unequalDampedCanonicalCIntegrand13_17
        (1 - unequalDampedTheta (4 / 7) (3 / 7) s) y
      ∂betaMeasure 6 8)
        =
      ∫ y in (0 : ℝ)..1,
        unequalDampedMinusDensity y
          * unequalDampedCanonicalCIntegrand13_17
            (1 - unequalDampedTheta (4 / 7) (3 / 7) s) y :=
      integral_betaMeasure_six_eight_eq_interval _
    _ =
      ∫ y in (0 : ℝ)..1,
        unequalDampedMinusDensity y
          *
        (unequalDampedPhi (4 / 7) (-unequalDampedKappa13_17)
              (unequalDampedR s y) ^ 2
          * unequalDampedCKernel13_17
              (unequalDampedU (3 / 7) s y)) := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hy' : y ∈ Icc (0 : ℝ) 1 := by
              simpa [uIcc_of_le] using hy
            have hqs : 1 - (3 / 7 : ℝ) * s ≠ 0 :=
              ne_of_gt
                (one_sub_qs_pos
                  (by norm_num) (by norm_num) hs0 hs1)
            have hsy : unequalDampedDenom s y ≠ 0 :=
              ne_of_gt
                (unequalDampedDenom_pos hs0 hs1 hy'.1 hy'.2)
            change
              unequalDampedMinusDensity y
                  * unequalDampedCanonicalCIntegrand13_17
                    (1 - unequalDampedTheta (4 / 7) (3 / 7) s) y
                =
              unequalDampedMinusDensity y
                *
              (unequalDampedPhi (4 / 7) (-unequalDampedKappa13_17)
                    (unequalDampedR s y) ^ 2
                * unequalDampedCKernel13_17
                    (unequalDampedU (3 / 7) s y))
            rw [unequalDampedCanonicalCIntegrand13_17_minus_chart
              hqs hsy]
    _ =
      ∫ y,
        unequalDampedPhi (4 / 7) (-unequalDampedKappa13_17)
            (unequalDampedR s y) ^ 2
          * unequalDampedCKernel13_17
            (unequalDampedU (3 / 7) s y)
        ∂betaMeasure 6 8 := by
          symm
          exact integral_betaMeasure_six_eight_eq_interval _
    _ = unequalDampedMinusC s := rfl

/-! ## Global canonical coefficient identities and risk inequality -/

/-- Original-side chart identity for the global direct `B` coefficient. -/
theorem unequalDampedCanonicalB13_17_eq_plus
    {θ : ℝ} (hθ0 : 0 < θ) (hθpivot : 3 / 7 ≤ θ)
    (hθ1 : θ < 1) :
    unequalDampedCanonicalB13_17 θ
      =
    unequalDampedPlusB (unequalDampedPlusS θ) := by
  have hs0 :=
    unequalDampedPlusS_nonneg hθpivot hθ0
  have hs1 :=
    unequalDampedPlusS_lt_one hθ1 hθ0
  calc
    unequalDampedCanonicalB13_17 θ
        =
      unequalDampedCanonicalB13_17
        (unequalDampedTheta (3 / 7) (4 / 7)
          (unequalDampedPlusS θ)) := by
            rw [unequalDampedTheta_plusS hθ0]
    _ = unequalDampedPlusB (unequalDampedPlusS θ) :=
      unequalDampedCanonicalB13_17_plus_chart hs0 hs1

/-- Original-side chart identity for the global direct `C` coefficient. -/
theorem unequalDampedCanonicalC13_17_eq_plus
    {θ : ℝ} (hθ0 : 0 < θ) (hθpivot : 3 / 7 ≤ θ)
    (hθ1 : θ < 1) :
    unequalDampedCanonicalC13_17 θ
      =
    unequalDampedPlusC (unequalDampedPlusS θ) := by
  have hs0 :=
    unequalDampedPlusS_nonneg hθpivot hθ0
  have hs1 :=
    unequalDampedPlusS_lt_one hθ1 hθ0
  calc
    unequalDampedCanonicalC13_17 θ
        =
      unequalDampedCanonicalC13_17
        (unequalDampedTheta (3 / 7) (4 / 7)
          (unequalDampedPlusS θ)) := by
            rw [unequalDampedTheta_plusS hθ0]
    _ = unequalDampedPlusC (unequalDampedPlusS θ) :=
      unequalDampedCanonicalC13_17_plus_chart hs0 hs1

/-- Sample-swapped chart identity for the global direct `B` coefficient. -/
theorem unequalDampedCanonicalB13_17_eq_minus
    {θ : ℝ} (hθ0 : 0 < θ) (hθpivot : θ ≤ 3 / 7)
    (hθ1 : θ < 1) :
    unequalDampedCanonicalB13_17 θ
      =
    unequalDampedMinusB (unequalDampedMinusS θ) := by
  have hs0 :=
    unequalDampedMinusS_nonneg hθpivot hθ1
  have hs1 :=
    unequalDampedMinusS_lt_one hθ0 hθ1
  calc
    unequalDampedCanonicalB13_17 θ
        =
      unequalDampedCanonicalB13_17
        (1 - unequalDampedTheta (4 / 7) (3 / 7)
          (unequalDampedMinusS θ)) := by
            rw [unequalDampedTheta_minusS hθ1]
            ring
    _ = unequalDampedMinusB (unequalDampedMinusS θ) :=
      unequalDampedCanonicalB13_17_minus_chart hs0 hs1

/-- Sample-swapped chart identity for the global direct `C` coefficient. -/
theorem unequalDampedCanonicalC13_17_eq_minus
    {θ : ℝ} (hθ0 : 0 < θ) (hθpivot : θ ≤ 3 / 7)
    (hθ1 : θ < 1) :
    unequalDampedCanonicalC13_17 θ
      =
    unequalDampedMinusC (unequalDampedMinusS θ) := by
  have hs0 :=
    unequalDampedMinusS_nonneg hθpivot hθ1
  have hs1 :=
    unequalDampedMinusS_lt_one hθ0 hθ1
  calc
    unequalDampedCanonicalC13_17 θ
        =
      unequalDampedCanonicalC13_17
        (1 - unequalDampedTheta (4 / 7) (3 / 7)
          (unequalDampedMinusS θ)) := by
            rw [unequalDampedTheta_minusS hθ1]
            ring
    _ = unequalDampedMinusC (unequalDampedMinusS θ) :=
      unequalDampedCanonicalC13_17_minus_chart hs0 hs1

/-- The global canonical first-order coefficient is strictly negative. -/
theorem unequalDampedCanonicalB13_17_neg
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    unequalDampedCanonicalB13_17 θ < 0 := by
  by_cases hside : 3 / 7 ≤ θ
  · rw [unequalDampedCanonicalB13_17_eq_plus hθ0 hside hθ1]
    unfold unequalDampedPlusB
    exact mul_neg_of_pos_of_neg
      (div_pos
        (sq_pos_of_pos
          (sub_pos.mpr
            (unequalDampedPlusS_lt_one hθ1 hθ0)))
        (one_sub_qs_pos
          (by norm_num) (by norm_num)
          (unequalDampedPlusS_nonneg hside hθ0)
          (unequalDampedPlusS_lt_one hθ1 hθ0)))
      (unequalDampedPlusH_neg
        (unequalDampedPlusS_nonneg hside hθ0)
        (unequalDampedPlusS_lt_one hθ1 hθ0))
  · have hside' : θ ≤ 3 / 7 := le_of_not_ge hside
    rw [unequalDampedCanonicalB13_17_eq_minus hθ0 hside' hθ1]
    unfold unequalDampedMinusB
    exact mul_neg_of_pos_of_neg
      (div_pos
        (sq_pos_of_pos
          (sub_pos.mpr
            (unequalDampedMinusS_lt_one hθ0 hθ1)))
        (one_sub_qs_pos
          (by norm_num) (by norm_num)
          (unequalDampedMinusS_nonneg hside' hθ1)
          (unequalDampedMinusS_lt_one hθ0 hθ1)))
      (unequalDampedMinusH_neg
        (unequalDampedMinusS_nonneg hside' hθ1)
        (unequalDampedMinusS_lt_one hθ0 hθ1))

/--
Global fixed-epsilon reduced-risk inequality for every interior variance
ratio.
-/
theorem unequalDampedCanonicalReducedRisk_neg13_17
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    2 * unequalDampedEpsilon13_17
          * unequalDampedCanonicalB13_17 θ
      + unequalDampedEpsilon13_17 ^ 2
          * unequalDampedCanonicalC13_17 θ
      < 0 := by
  by_cases hside : 3 / 7 ≤ θ
  · rw [unequalDampedCanonicalB13_17_eq_plus hθ0 hside hθ1,
      unequalDampedCanonicalC13_17_eq_plus hθ0 hside hθ1]
    exact unequalDampedPlusReducedRisk_neg
      (unequalDampedPlusS_nonneg hside hθ0)
      (unequalDampedPlusS_lt_one hθ1 hθ0)
  · have hside' : θ ≤ 3 / 7 := le_of_not_ge hside
    rw [unequalDampedCanonicalB13_17_eq_minus hθ0 hside' hθ1,
      unequalDampedCanonicalC13_17_eq_minus hθ0 hside' hθ1]
    exact unequalDampedMinusReducedRisk_neg
      (unequalDampedMinusS_nonneg hside' hθ1)
      (unequalDampedMinusS_lt_one hθ0 hθ1)

end

end GraybillDeal
