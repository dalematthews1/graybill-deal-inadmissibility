import GraybillDeal.UnequalFixedDifferenceFourCanonical
import GraybillDeal.UnequalFixedDifferenceFourReduced

/-!
# Canonical reduced-risk bridge for the fixed-difference-four family

This module transports the two one-sided analytic certificates for

`(n₁,n₂) = (2m-1,2m+3)`, `m ≥ 7`,

to the direct canonical beta coordinate.  The residual ratio has law
`Beta(m-1,m+1)`.  On the right of its pivot we complement that ratio and
use the `Beta(m+1,m-1)` certificate; on the left we use it directly.
-/

namespace GraybillDeal

open MeasureTheory Set ProbabilityTheory

noncomputable section

/-! ## Direct canonical coefficients -/

/-- Direct canonical integrand for the linear reduced-risk coefficient. -/
def unequalFixedDifferenceFourCanonicalBIntegrand
    (m : ℕ) (θ p : ℝ) : ℝ :=
  (unequalFixedDifferenceFourCanonicalR m θ p - θ)
    * unequalDampedPhi
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourKappa m)
        (unequalFixedDifferenceFourCanonicalR m θ p)
    * (unequalFixedDifferenceFourC m
      - unequalFixedDifferenceFourK m
        / unequalFixedDifferenceFourCanonicalDenom m θ p)

/-- Direct canonical integrand for the quadratic reduced-risk coefficient. -/
def unequalFixedDifferenceFourCanonicalCIntegrand
    (m : ℕ) (θ p : ℝ) : ℝ :=
  unequalDampedPhi
      (unequalFixedDifferenceFourT m)
      (unequalFixedDifferenceFourKappa m)
      (unequalFixedDifferenceFourCanonicalR m θ p) ^ 2
    * unequalFixedDifferenceFourCKernel m
        ((unequalFixedDifferenceFourCanonicalDenom m θ p)⁻¹)

/-- Direct canonical linear coefficient under `Beta(m-1,m+1)`. -/
def unequalFixedDifferenceFourCanonicalB
    (m : ℕ) (θ : ℝ) : ℝ :=
  ∫ p, unequalFixedDifferenceFourCanonicalBIntegrand m θ p
    ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1)

/-- Direct canonical quadratic coefficient under `Beta(m-1,m+1)`. -/
def unequalFixedDifferenceFourCanonicalC
    (m : ℕ) (θ : ℝ) : ℝ :=
  ∫ p, unequalFixedDifferenceFourCanonicalCIntegrand m θ p
    ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1)

theorem measurable_unequalFixedDifferenceFourCanonicalBIntegrand
    (m : ℕ) (θ : ℝ) :
    Measurable (unequalFixedDifferenceFourCanonicalBIntegrand m θ) := by
  unfold unequalFixedDifferenceFourCanonicalBIntegrand
    unequalFixedDifferenceFourCanonicalR
    unequalFixedDifferenceFourCanonicalDenom
    unequalDampedPhi unequalDampedInner
  fun_prop

theorem measurable_unequalFixedDifferenceFourCanonicalCIntegrand
    (m : ℕ) (θ : ℝ) :
    Measurable (unequalFixedDifferenceFourCanonicalCIntegrand m θ) := by
  unfold unequalFixedDifferenceFourCanonicalCIntegrand
    unequalFixedDifferenceFourCanonicalR
    unequalFixedDifferenceFourCanonicalDenom
    unequalFixedDifferenceFourCKernel
    unequalDampedPhi unequalDampedInner
  fun_prop

/-! ## Family beta interval and complement identities -/

/--
Integration under the right-chart `Beta(m+1,m-1)` law is interval
integration against the polynomial density used by the analytic proof.
-/
theorem integral_betaMeasure_unequalFixedDifferenceFourPlus_eq_interval
    {m : ℕ} (hm : 7 ≤ m) (f : ℝ → ℝ) :
    (∫ y, f y ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1))
      =
    ∫ y in (0 : ℝ)..1,
      unequalFixedDifferenceFourPlusDensity m y * f y := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have ha : 0 < (m : ℝ) + 1 := by linarith
  have hb : 0 < (m : ℝ) - 1 := by linarith
  rw [integral_betaMeasure_eq_interval_of_shapes_pos ha hb]
  apply intervalIntegral.integral_congr_uIoo
  intro y hy
  rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
  have hy0 : 0 < y := hy.1
  have hy1 : 0 < 1 - y := sub_pos.mpr hy.2
  have hm2 : 2 ≤ m := by omega
  have hfirst :
      y ^ ((m : ℝ) + 1 - 1) = y ^ m := by
    rw [show (m : ℝ) + 1 - 1 = (m : ℝ) by ring,
      Real.rpow_natCast]
  have hsecond :
      (1 - y) ^ ((m : ℝ) - 1 - 1) = (1 - y) ^ (m - 2) := by
    rw [show (m : ℝ) - 1 - 1 = ((m - 2 : ℕ) : ℝ) by
      rw [Nat.cast_sub hm2]
      push_cast
      ring,
      Real.rpow_natCast]
  dsimp only
  rw [hfirst, hsecond]
  unfold unequalFixedDifferenceFourPlusDensity
  ring

/--
Integration under the left-chart `Beta(m-1,m+1)` law is interval
integration against the corresponding polynomial density.
-/
theorem integral_betaMeasure_unequalFixedDifferenceFourMinus_eq_interval
    {m : ℕ} (hm : 7 ≤ m) (f : ℝ → ℝ) :
    (∫ y, f y ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
      =
    ∫ y in (0 : ℝ)..1,
      unequalFixedDifferenceFourMinusDensity m y * f y := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have ha : 0 < (m : ℝ) - 1 := by linarith
  have hb : 0 < (m : ℝ) + 1 := by linarith
  rw [integral_betaMeasure_eq_interval_of_shapes_pos ha hb]
  apply intervalIntegral.integral_congr_uIoo
  intro y hy
  rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
  have hy0 : 0 < y := hy.1
  have hy1 : 0 < 1 - y := sub_pos.mpr hy.2
  have hm2 : 2 ≤ m := by omega
  have hfirst :
      y ^ ((m : ℝ) - 1 - 1) = y ^ (m - 2) := by
    rw [show (m : ℝ) - 1 - 1 = ((m - 2 : ℕ) : ℝ) by
      rw [Nat.cast_sub hm2]
      push_cast
      ring,
      Real.rpow_natCast]
  have hsecond :
      (1 - y) ^ ((m : ℝ) + 1 - 1) = (1 - y) ^ m := by
    rw [show (m : ℝ) + 1 - 1 = (m : ℝ) by ring,
      Real.rpow_natCast]
  dsimp only
  rw [hfirst, hsecond]
  unfold unequalFixedDifferenceFourMinusDensity
  ring

theorem unequalFixedDifferenceFourMinusDensity_eq_complementPlus
    (m : ℕ) (p : ℝ) :
    unequalFixedDifferenceFourMinusDensity m p
      = unequalFixedDifferenceFourPlusDensity m (1 - p) := by
  unfold unequalFixedDifferenceFourMinusDensity
    unequalFixedDifferenceFourPlusDensity
  rw [beta_symm_real ((m : ℝ) - 1) ((m : ℝ) + 1)]
  ring

/--
Complementing `Beta(m-1,m+1)` gives `Beta(m+1,m-1)`, stated directly at
the level of expectations.
-/
theorem integral_betaMeasure_unequalFixedDifferenceFour_complement
    {m : ℕ} (hm : 7 ≤ m) (f : ℝ → ℝ) :
    (∫ p, f p ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
      =
    ∫ y, f (1 - y)
      ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1) := by
  rw [integral_betaMeasure_unequalFixedDifferenceFourMinus_eq_interval
      hm,
    integral_betaMeasure_unequalFixedDifferenceFourPlus_eq_interval
      hm]
  calc
    (∫ p in (0 : ℝ)..1,
      unequalFixedDifferenceFourMinusDensity m p * f p)
        =
      ∫ p in (0 : ℝ)..1,
        (fun y =>
          unequalFixedDifferenceFourPlusDensity m y
            * f (1 - y)) (1 - p) := by
              apply intervalIntegral.integral_congr
              intro p _
              dsimp only
              rw [←
                unequalFixedDifferenceFourMinusDensity_eq_complementPlus
                  m p]
              ring
    _ =
      ∫ y in (0 : ℝ)..1,
        unequalFixedDifferenceFourPlusDensity m y
          * f (1 - y) := by
            simpa using
              (intervalIntegral.integral_comp_sub_left
                (fun y : ℝ =>
                  unequalFixedDifferenceFourPlusDensity m y
                    * f (1 - y))
                (a := (0 : ℝ)) (b := 1) 1)

/-! ## The two global chart parameters -/

/-- Right-chart coordinate for oracle weights above the beta pivot. -/
def unequalFixedDifferenceFourCanonicalPlusS
    (m : ℕ) (θ : ℝ) : ℝ :=
  (θ - unequalFixedDifferenceFourT m)
    / (unequalFixedDifferenceFourQ m * θ)

/-- Left-chart coordinate for oracle weights below the beta pivot. -/
def unequalFixedDifferenceFourCanonicalMinusS
    (m : ℕ) (θ : ℝ) : ℝ :=
  (unequalFixedDifferenceFourT m - θ)
    / (unequalFixedDifferenceFourT m * (1 - θ))

theorem unequalFixedDifferenceFourCanonicalPlusS_nonneg
    {m : ℕ} (hm : 7 ≤ m)
    {θ : ℝ} (hθpivot : unequalFixedDifferenceFourT m ≤ θ)
    (hθ0 : 0 < θ) :
    0 ≤ unequalFixedDifferenceFourCanonicalPlusS m θ := by
  unfold unequalFixedDifferenceFourCanonicalPlusS
  exact div_nonneg (sub_nonneg.mpr hθpivot)
    (mul_nonneg (unequalFixedDifferenceFourQ_pos hm).le hθ0.le)

theorem unequalFixedDifferenceFourCanonicalPlusS_lt_one
    {m : ℕ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    unequalFixedDifferenceFourCanonicalPlusS m θ < 1 := by
  have ht := unequalFixedDifferenceFourT_pos hm
  have ht := unequalFixedDifferenceFourT_pos hm
  have hq := unequalFixedDifferenceFourQ_pos hm
  have htq := unequalFixedDifferenceFourT_add_Q hm
  unfold unequalFixedDifferenceFourCanonicalPlusS
  rw [div_lt_one (mul_pos hq hθ0)]
  nlinarith

theorem unequalFixedDifferenceFourCanonicalMinusS_nonneg
    {m : ℕ} (hm : 7 ≤ m)
    {θ : ℝ} (hθpivot : θ ≤ unequalFixedDifferenceFourT m)
    (hθ1 : θ < 1) :
    0 ≤ unequalFixedDifferenceFourCanonicalMinusS m θ := by
  unfold unequalFixedDifferenceFourCanonicalMinusS
  exact div_nonneg (sub_nonneg.mpr hθpivot)
    (mul_nonneg (unequalFixedDifferenceFourT_pos hm).le
      (sub_nonneg.mpr hθ1.le))

theorem unequalFixedDifferenceFourCanonicalMinusS_lt_one
    {m : ℕ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    unequalFixedDifferenceFourCanonicalMinusS m θ < 1 := by
  have ht := unequalFixedDifferenceFourT_pos hm
  have hq := unequalFixedDifferenceFourQ_pos hm
  have htq := unequalFixedDifferenceFourT_add_Q hm
  unfold unequalFixedDifferenceFourCanonicalMinusS
  rw [div_lt_one (mul_pos ht (sub_pos.mpr hθ1))]
  nlinarith

theorem unequalFixedDifferenceFourTheta_plusS
    {m : ℕ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) :
    unequalDampedTheta
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourQ m)
        (unequalFixedDifferenceFourCanonicalPlusS m θ)
      = θ := by
  have ht := unequalFixedDifferenceFourT_pos hm
  have hq := unequalFixedDifferenceFourQ_pos hm
  have htq := unequalFixedDifferenceFourT_add_Q hm
  unfold unequalDampedTheta
    unequalFixedDifferenceFourCanonicalPlusS
  field_simp [ht.ne', hq.ne', hθ0.ne']
  nlinarith

theorem unequalFixedDifferenceFourTheta_minusS
    {m : ℕ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ1 : θ < 1) :
    unequalDampedTheta
        (unequalFixedDifferenceFourQ m)
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourCanonicalMinusS m θ)
      = 1 - θ := by
  have ht := unequalFixedDifferenceFourT_pos hm
  have hq := unequalFixedDifferenceFourQ_pos hm
  have htq := unequalFixedDifferenceFourT_add_Q hm
  have h1θ : 1 - θ ≠ 0 := ne_of_gt (sub_pos.mpr hθ1)
  unfold unequalDampedTheta
    unequalFixedDifferenceFourCanonicalMinusS
  have hden :
      1 -
          unequalFixedDifferenceFourT m
            * ((unequalFixedDifferenceFourT m - θ)
              / (unequalFixedDifferenceFourT m * (1 - θ)))
        =
      unequalFixedDifferenceFourQ m / (1 - θ) := by
    field_simp [ht.ne', h1θ]
    nlinarith
  rw [hden]
  field_simp [hq.ne', h1θ]

/-! ## Pointwise chart algebra -/

/-- The canonical denominator in the right chart. -/
theorem unequalFixedDifferenceFourCanonicalDenom_plus_chart
    {m : ℕ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourQ m * s ≠ 0) :
    unequalFixedDifferenceFourCanonicalDenom m
        (unequalDampedTheta
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m) s)
        (1 - y)
      =
    unequalDampedDenom s y
      / (1 - unequalFixedDifferenceFourQ m * s) := by
  have ht := unequalFixedDifferenceFourT_pos hm
  have hq := unequalFixedDifferenceFourQ_pos hm
  have htq := unequalFixedDifferenceFourT_add_Q hm
  unfold unequalFixedDifferenceFourCanonicalDenom
    unequalDampedTheta unequalDampedDenom
  field_simp [ht.ne', hq.ne', hqs]
  rw [show unequalFixedDifferenceFourQ m
      = 1 - unequalFixedDifferenceFourT m by linarith]
  ring

/-- The canonical Graybill--Deal weight in the right chart. -/
theorem unequalFixedDifferenceFourCanonicalR_plus_chart
    {m : ℕ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourQ m * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalFixedDifferenceFourCanonicalR m
        (unequalDampedTheta
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m) s)
        (1 - y)
      =
    unequalDampedR s y := by
  have ht := unequalFixedDifferenceFourT_pos hm
  rw [unequalFixedDifferenceFourCanonicalR,
    unequalFixedDifferenceFourCanonicalDenom_plus_chart hm hqs]
  unfold unequalDampedTheta unequalDampedR
  field_simp [ht.ne', hqs, hsy]

/-- The reciprocal canonical denominator in the right chart. -/
theorem unequalFixedDifferenceFourCanonicalDenom_inv_plus_chart
    {m : ℕ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourQ m * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    (unequalFixedDifferenceFourCanonicalDenom m
        (unequalDampedTheta
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m) s)
        (1 - y))⁻¹
      =
    unequalDampedU (unequalFixedDifferenceFourQ m) s y := by
  rw [unequalFixedDifferenceFourCanonicalDenom_plus_chart hm hqs]
  unfold unequalDampedU
  field_simp [hqs, hsy]

/-- The canonical denominator in the sample-swapped chart. -/
theorem unequalFixedDifferenceFourCanonicalDenom_minus_chart
    {m : ℕ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourT m * s ≠ 0) :
    unequalFixedDifferenceFourCanonicalDenom m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourQ m)
            (unequalFixedDifferenceFourT m) s)
        y
      =
    unequalDampedDenom s y
      / (1 - unequalFixedDifferenceFourT m * s) := by
  have ht := unequalFixedDifferenceFourT_pos hm
  have hq := unequalFixedDifferenceFourQ_pos hm
  have htq := unequalFixedDifferenceFourT_add_Q hm
  unfold unequalFixedDifferenceFourCanonicalDenom
    unequalDampedTheta unequalDampedDenom
  field_simp [ht.ne', hq.ne', hqs]
  rw [show unequalFixedDifferenceFourQ m
      = 1 - unequalFixedDifferenceFourT m by linarith]
  ring

/-- Complementing the canonical weight gives the swapped chart weight. -/
theorem one_sub_unequalFixedDifferenceFourCanonicalR_minus_chart
    {m : ℕ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourT m * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    1 -
        unequalFixedDifferenceFourCanonicalR m
          (1 -
            unequalDampedTheta
              (unequalFixedDifferenceFourQ m)
              (unequalFixedDifferenceFourT m) s)
          y
      =
    unequalDampedR s y := by
  have ht := unequalFixedDifferenceFourT_pos hm
  have hq := unequalFixedDifferenceFourQ_pos hm
  have htq := unequalFixedDifferenceFourT_add_Q hm
  rw [unequalFixedDifferenceFourCanonicalR,
    unequalFixedDifferenceFourCanonicalDenom_minus_chart hm hqs]
  unfold unequalDampedTheta unequalDampedR
  unfold unequalDampedDenom at hsy ⊢
  field_simp [ht.ne', hq.ne', hqs, hsy]
  rw [show unequalFixedDifferenceFourQ m
      = 1 - unequalFixedDifferenceFourT m by linarith]
  ring

/-- The reciprocal canonical denominator in the swapped chart. -/
theorem unequalFixedDifferenceFourCanonicalDenom_inv_minus_chart
    {m : ℕ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourT m * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    (unequalFixedDifferenceFourCanonicalDenom m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourQ m)
            (unequalFixedDifferenceFourT m) s)
        y)⁻¹
      =
    unequalDampedU (unequalFixedDifferenceFourT m) s y := by
  rw [unequalFixedDifferenceFourCanonicalDenom_minus_chart hm hqs]
  unfold unequalDampedU
  field_simp [hqs, hsy]

/-- The family direction is equivariant under sample swapping. -/
theorem unequalFixedDifferenceFourCanonicalPhi_swap
    {m : ℕ} (hm : 7 ≤ m) (r : ℝ) :
    unequalDampedPhi
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourKappa m) r
      =
    -unequalDampedPhi
        (unequalFixedDifferenceFourQ m)
        (-unequalFixedDifferenceFourKappa m) (1 - r) := by
  have htq := unequalFixedDifferenceFourT_add_Q hm
  unfold unequalDampedPhi unequalDampedInner
  rw [show unequalFixedDifferenceFourQ m
      = 1 - unequalFixedDifferenceFourT m by linarith]
  ring

/-- Pointwise right-chart identification of the direct linear integrand. -/
theorem unequalFixedDifferenceFourCanonicalBIntegrand_plus_chart
    {m : ℕ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourQ m * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalFixedDifferenceFourCanonicalBIntegrand m
        (unequalDampedTheta
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m) s)
        (1 - y)
      =
    (1 - s) ^ 2
        / (1 - unequalFixedDifferenceFourQ m * s)
      *
    ((unequalFixedDifferenceFourQ m - y) * y * (1 - y)
        * unequalDampedF
            (unequalFixedDifferenceFourT m)
            (unequalFixedDifferenceFourQ m)
            (unequalFixedDifferenceFourKappa m) s y
        * unequalDampedPsiNumerator
            (unequalFixedDifferenceFourQ m)
            (unequalFixedDifferenceFourC m)
            (unequalFixedDifferenceFourK m) s y
      / unequalDampedDenom s y ^ 6) := by
  have htq := unequalFixedDifferenceFourT_add_Q hm
  unfold unequalFixedDifferenceFourCanonicalBIntegrand
  rw [unequalFixedDifferenceFourCanonicalR_plus_chart hm hqs hsy]
  rw [show
      unequalFixedDifferenceFourK m
          / unequalFixedDifferenceFourCanonicalDenom m
            (unequalDampedTheta
              (unequalFixedDifferenceFourT m)
              (unequalFixedDifferenceFourQ m) s)
            (1 - y)
        =
      unequalFixedDifferenceFourK m
        * unequalDampedU
            (unequalFixedDifferenceFourQ m) s y by
          rw [div_eq_mul_inv,
            unequalFixedDifferenceFourCanonicalDenom_inv_plus_chart
              hm hqs hsy]]
  exact unequalDampedB_integrand_factorization htq hqs hsy

/-- Pointwise swapped-chart identification of the direct linear integrand. -/
theorem unequalFixedDifferenceFourCanonicalBIntegrand_minus_chart
    {m : ℕ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourT m * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalFixedDifferenceFourCanonicalBIntegrand m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourQ m)
            (unequalFixedDifferenceFourT m) s)
        y
      =
    (1 - s) ^ 2
        / (1 - unequalFixedDifferenceFourT m * s)
      *
    ((unequalFixedDifferenceFourT m - y) * y * (1 - y)
        * unequalDampedF
            (unequalFixedDifferenceFourQ m)
            (unequalFixedDifferenceFourT m)
            (-unequalFixedDifferenceFourKappa m) s y
        * unequalDampedPsiNumerator
            (unequalFixedDifferenceFourT m)
            (unequalFixedDifferenceFourC m)
            (unequalFixedDifferenceFourK m) s y
      / unequalDampedDenom s y ^ 6) := by
  let r :=
    unequalFixedDifferenceFourCanonicalR m
      (1 -
        unequalDampedTheta
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourT m) s)
      y
  have hr :
      1 - r = unequalDampedR s y :=
    one_sub_unequalFixedDifferenceFourCanonicalR_minus_chart
      hm hqs hsy
  have hr' : r = 1 - unequalDampedR s y := by
    linarith
  have hqt :
      unequalFixedDifferenceFourQ m
        + unequalFixedDifferenceFourT m = 1 := by
    have htq := unequalFixedDifferenceFourT_add_Q hm
    linarith
  unfold unequalFixedDifferenceFourCanonicalBIntegrand
  change
    (r -
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourQ m)
            (unequalFixedDifferenceFourT m) s))
      *
      unequalDampedPhi
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourKappa m) r
      *
      (unequalFixedDifferenceFourC m
        - unequalFixedDifferenceFourK m
          / unequalFixedDifferenceFourCanonicalDenom m
            (1 -
              unequalDampedTheta
                (unequalFixedDifferenceFourQ m)
                (unequalFixedDifferenceFourT m) s)
            y)
      = _
  rw [unequalFixedDifferenceFourCanonicalPhi_swap hm r]
  rw [show
      unequalFixedDifferenceFourK m
          / unequalFixedDifferenceFourCanonicalDenom m
            (1 -
              unequalDampedTheta
                (unequalFixedDifferenceFourQ m)
                (unequalFixedDifferenceFourT m) s)
            y
        =
      unequalFixedDifferenceFourK m
        * unequalDampedU
            (unequalFixedDifferenceFourT m) s y by
          rw [div_eq_mul_inv,
            unequalFixedDifferenceFourCanonicalDenom_inv_minus_chart
              hm hqs hsy]]
  rw [hr, hr']
  convert
    unequalDampedB_integrand_factorization
      (t := unequalFixedDifferenceFourQ m)
      (q := unequalFixedDifferenceFourT m)
      (κ := -unequalFixedDifferenceFourKappa m)
      (c := unequalFixedDifferenceFourC m)
      (k := unequalFixedDifferenceFourK m)
      hqt hqs hsy using 1 <;>
    ring

/-- Pointwise right-chart identification of the direct quadratic integrand. -/
theorem unequalFixedDifferenceFourCanonicalCIntegrand_plus_chart
    {m : ℕ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourQ m * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalFixedDifferenceFourCanonicalCIntegrand m
        (unequalDampedTheta
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m) s)
        (1 - y)
      =
    unequalFixedDifferenceFourPlusCIntegrand m s y := by
  unfold unequalFixedDifferenceFourCanonicalCIntegrand
    unequalFixedDifferenceFourPlusCIntegrand
  rw [unequalFixedDifferenceFourCanonicalR_plus_chart hm hqs hsy,
    unequalFixedDifferenceFourCanonicalDenom_inv_plus_chart
      hm hqs hsy]

/-- Pointwise swapped-chart identification of the direct quadratic integrand. -/
theorem unequalFixedDifferenceFourCanonicalCIntegrand_minus_chart
    {m : ℕ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourT m * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalFixedDifferenceFourCanonicalCIntegrand m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourQ m)
            (unequalFixedDifferenceFourT m) s)
        y
      =
    unequalFixedDifferenceFourMinusCIntegrand m s y := by
  let r :=
    unequalFixedDifferenceFourCanonicalR m
      (1 -
        unequalDampedTheta
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourT m) s)
      y
  have hr :
      1 - r = unequalDampedR s y :=
    one_sub_unequalFixedDifferenceFourCanonicalR_minus_chart
      hm hqs hsy
  unfold unequalFixedDifferenceFourCanonicalCIntegrand
    unequalFixedDifferenceFourMinusCIntegrand
  change
    unequalDampedPhi
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourKappa m) r ^ 2
      *
      unequalFixedDifferenceFourCKernel m
        ((unequalFixedDifferenceFourCanonicalDenom m
          (1 -
            unequalDampedTheta
              (unequalFixedDifferenceFourQ m)
              (unequalFixedDifferenceFourT m) s)
          y)⁻¹)
      = _
  rw [unequalFixedDifferenceFourCanonicalPhi_swap hm r,
    unequalFixedDifferenceFourCanonicalDenom_inv_minus_chart
      hm hqs hsy,
    ← hr]
  ring

/-! ## Integral chart identities -/

/-- The direct canonical linear coefficient in the right chart. -/
theorem unequalFixedDifferenceFourCanonicalB_plus_chart
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourCanonicalB m
        (unequalDampedTheta
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m) s)
      =
    unequalFixedDifferenceFourPlusB m s := by
  unfold unequalFixedDifferenceFourCanonicalB
  rw [integral_betaMeasure_unequalFixedDifferenceFour_complement hm]
  unfold unequalFixedDifferenceFourPlusB
    unequalFixedDifferenceFourPlusAnalyticH
    unequalFixedDifferenceFourPlusH
  calc
    (∫ y,
      unequalFixedDifferenceFourCanonicalBIntegrand m
        (unequalDampedTheta
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m) s)
        (1 - y)
      ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1))
        =
      ∫ y in (0 : ℝ)..1,
        unequalFixedDifferenceFourPlusDensity m y
          *
        unequalFixedDifferenceFourCanonicalBIntegrand m
          (unequalDampedTheta
            (unequalFixedDifferenceFourT m)
            (unequalFixedDifferenceFourQ m) s)
          (1 - y) :=
      integral_betaMeasure_unequalFixedDifferenceFourPlus_eq_interval
        hm _
    _ =
      ∫ y in (0 : ℝ)..1,
        (1 - s) ^ 2
            / (1 - unequalFixedDifferenceFourQ m * s)
          *
        unequalDampedHIntegrand
          (unequalFixedDifferenceFourPlusDensity m)
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourKappa m)
          (unequalFixedDifferenceFourC m)
          (unequalFixedDifferenceFourK m) s y := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hy' : y ∈ Icc (0 : ℝ) 1 := by
              simpa [uIcc_of_le] using hy
            have hqs :
                1 - unequalFixedDifferenceFourQ m * s ≠ 0 :=
              ne_of_gt
                (one_sub_qs_pos
                  (unequalFixedDifferenceFourQ_pos hm).le
                  (unequalFixedDifferenceFourQ_le_one hm)
                  hs0 hs1)
            have hsy : unequalDampedDenom s y ≠ 0 :=
              ne_of_gt
                (unequalDampedDenom_pos
                  hs0 hs1 hy'.1 hy'.2)
            dsimp only
            rw [unequalFixedDifferenceFourCanonicalBIntegrand_plus_chart
              hm hqs hsy]
            unfold unequalDampedHIntegrand
            ring
    _ =
      (1 - s) ^ 2
          / (1 - unequalFixedDifferenceFourQ m * s)
        *
      ∫ y in (0 : ℝ)..1,
        unequalDampedHIntegrand
          (unequalFixedDifferenceFourPlusDensity m)
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourKappa m)
          (unequalFixedDifferenceFourC m)
          (unequalFixedDifferenceFourK m) s y := by
            rw [intervalIntegral.integral_const_mul]

/-- The direct canonical quadratic coefficient in the right chart. -/
theorem unequalFixedDifferenceFourCanonicalC_plus_chart
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourCanonicalC m
        (unequalDampedTheta
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m) s)
      =
    unequalFixedDifferenceFourPlusC m s := by
  unfold unequalFixedDifferenceFourCanonicalC
  rw [integral_betaMeasure_unequalFixedDifferenceFour_complement hm]
  calc
    (∫ y,
      unequalFixedDifferenceFourCanonicalCIntegrand m
        (unequalDampedTheta
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m) s)
        (1 - y)
      ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1))
        =
      ∫ y in (0 : ℝ)..1,
        unequalFixedDifferenceFourPlusDensity m y
          *
        unequalFixedDifferenceFourCanonicalCIntegrand m
          (unequalDampedTheta
            (unequalFixedDifferenceFourT m)
            (unequalFixedDifferenceFourQ m) s)
          (1 - y) :=
      integral_betaMeasure_unequalFixedDifferenceFourPlus_eq_interval
        hm _
    _ =
      ∫ y in (0 : ℝ)..1,
        unequalFixedDifferenceFourPlusDensity m y
          * unequalFixedDifferenceFourPlusCIntegrand m s y := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hy' : y ∈ Icc (0 : ℝ) 1 := by
              simpa [uIcc_of_le] using hy
            have hqs :
                1 - unequalFixedDifferenceFourQ m * s ≠ 0 :=
              ne_of_gt
                (one_sub_qs_pos
                  (unequalFixedDifferenceFourQ_pos hm).le
                  (unequalFixedDifferenceFourQ_le_one hm)
                  hs0 hs1)
            have hsy : unequalDampedDenom s y ≠ 0 :=
              ne_of_gt
                (unequalDampedDenom_pos
                  hs0 hs1 hy'.1 hy'.2)
            dsimp only
            rw [unequalFixedDifferenceFourCanonicalCIntegrand_plus_chart
              hm hqs hsy]
    _ =
      ∫ y, unequalFixedDifferenceFourPlusCIntegrand m s y
        ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1) := by
          symm
          exact
            integral_betaMeasure_unequalFixedDifferenceFourPlus_eq_interval
              hm _
    _ = unequalFixedDifferenceFourPlusC m s := rfl

/-- The direct canonical linear coefficient in the sample-swapped chart. -/
theorem unequalFixedDifferenceFourCanonicalB_minus_chart
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourCanonicalB m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourQ m)
            (unequalFixedDifferenceFourT m) s)
      =
    unequalFixedDifferenceFourMinusB m s := by
  unfold unequalFixedDifferenceFourCanonicalB
    unequalFixedDifferenceFourMinusB
    unequalFixedDifferenceFourMinusAnalyticH
    unequalFixedDifferenceFourMinusH
  calc
    (∫ y,
      unequalFixedDifferenceFourCanonicalBIntegrand m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourQ m)
            (unequalFixedDifferenceFourT m) s)
        y
      ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
        =
      ∫ y in (0 : ℝ)..1,
        unequalFixedDifferenceFourMinusDensity m y
          *
        unequalFixedDifferenceFourCanonicalBIntegrand m
          (1 -
            unequalDampedTheta
              (unequalFixedDifferenceFourQ m)
              (unequalFixedDifferenceFourT m) s)
          y :=
      integral_betaMeasure_unequalFixedDifferenceFourMinus_eq_interval
        hm _
    _ =
      ∫ y in (0 : ℝ)..1,
        (1 - s) ^ 2
            / (1 - unequalFixedDifferenceFourT m * s)
          *
        unequalDampedHIntegrand
          (unequalFixedDifferenceFourMinusDensity m)
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourT m)
          (-unequalFixedDifferenceFourKappa m)
          (unequalFixedDifferenceFourC m)
          (unequalFixedDifferenceFourK m) s y := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hy' : y ∈ Icc (0 : ℝ) 1 := by
              simpa [uIcc_of_le] using hy
            have hqs :
                1 - unequalFixedDifferenceFourT m * s ≠ 0 :=
              ne_of_gt
                (one_sub_qs_pos
                  (unequalFixedDifferenceFourT_pos hm).le
                  (unequalFixedDifferenceFourT_le_one hm)
                  hs0 hs1)
            have hsy : unequalDampedDenom s y ≠ 0 :=
              ne_of_gt
                (unequalDampedDenom_pos
                  hs0 hs1 hy'.1 hy'.2)
            dsimp only
            rw [unequalFixedDifferenceFourCanonicalBIntegrand_minus_chart
              hm hqs hsy]
            unfold unequalDampedHIntegrand
            ring
    _ =
      (1 - s) ^ 2
          / (1 - unequalFixedDifferenceFourT m * s)
        *
      ∫ y in (0 : ℝ)..1,
        unequalDampedHIntegrand
          (unequalFixedDifferenceFourMinusDensity m)
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourT m)
          (-unequalFixedDifferenceFourKappa m)
          (unequalFixedDifferenceFourC m)
          (unequalFixedDifferenceFourK m) s y := by
            rw [intervalIntegral.integral_const_mul]

/-- The direct canonical quadratic coefficient in the swapped chart. -/
theorem unequalFixedDifferenceFourCanonicalC_minus_chart
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourCanonicalC m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourQ m)
            (unequalFixedDifferenceFourT m) s)
      =
    unequalFixedDifferenceFourMinusC m s := by
  unfold unequalFixedDifferenceFourCanonicalC
  calc
    (∫ y,
      unequalFixedDifferenceFourCanonicalCIntegrand m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourQ m)
            (unequalFixedDifferenceFourT m) s)
        y
      ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
        =
      ∫ y in (0 : ℝ)..1,
        unequalFixedDifferenceFourMinusDensity m y
          *
        unequalFixedDifferenceFourCanonicalCIntegrand m
          (1 -
            unequalDampedTheta
              (unequalFixedDifferenceFourQ m)
              (unequalFixedDifferenceFourT m) s)
          y :=
      integral_betaMeasure_unequalFixedDifferenceFourMinus_eq_interval
        hm _
    _ =
      ∫ y in (0 : ℝ)..1,
        unequalFixedDifferenceFourMinusDensity m y
          * unequalFixedDifferenceFourMinusCIntegrand m s y := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hy' : y ∈ Icc (0 : ℝ) 1 := by
              simpa [uIcc_of_le] using hy
            have hqs :
                1 - unequalFixedDifferenceFourT m * s ≠ 0 :=
              ne_of_gt
                (one_sub_qs_pos
                  (unequalFixedDifferenceFourT_pos hm).le
                  (unequalFixedDifferenceFourT_le_one hm)
                  hs0 hs1)
            have hsy : unequalDampedDenom s y ≠ 0 :=
              ne_of_gt
                (unequalDampedDenom_pos
                  hs0 hs1 hy'.1 hy'.2)
            dsimp only
            rw [unequalFixedDifferenceFourCanonicalCIntegrand_minus_chart
              hm hqs hsy]
    _ =
      ∫ y, unequalFixedDifferenceFourMinusCIntegrand m s y
        ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1) := by
          symm
          exact
            integral_betaMeasure_unequalFixedDifferenceFourMinus_eq_interval
              hm _
    _ = unequalFixedDifferenceFourMinusC m s := rfl

/-! ## Global canonical identities and reduced-risk inequality -/

/-- Global right-chart identity for the canonical linear coefficient. -/
theorem unequalFixedDifferenceFourCanonicalB_eq_plus
    {m : ℕ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ)
    (hθpivot : unequalFixedDifferenceFourT m ≤ θ)
    (hθ1 : θ < 1) :
    unequalFixedDifferenceFourCanonicalB m θ
      =
    unequalFixedDifferenceFourPlusB m
      (unequalFixedDifferenceFourCanonicalPlusS m θ) := by
  have hs0 :=
    unequalFixedDifferenceFourCanonicalPlusS_nonneg
      hm hθpivot hθ0
  have hs1 :=
    unequalFixedDifferenceFourCanonicalPlusS_lt_one
      hm hθ0 hθ1
  calc
    unequalFixedDifferenceFourCanonicalB m θ
        =
      unequalFixedDifferenceFourCanonicalB m
        (unequalDampedTheta
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourCanonicalPlusS m θ)) := by
            rw [unequalFixedDifferenceFourTheta_plusS hm hθ0]
    _ =
      unequalFixedDifferenceFourPlusB m
        (unequalFixedDifferenceFourCanonicalPlusS m θ) :=
      unequalFixedDifferenceFourCanonicalB_plus_chart hm hs0 hs1

/-- Global right-chart identity for the canonical quadratic coefficient. -/
theorem unequalFixedDifferenceFourCanonicalC_eq_plus
    {m : ℕ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ)
    (hθpivot : unequalFixedDifferenceFourT m ≤ θ)
    (hθ1 : θ < 1) :
    unequalFixedDifferenceFourCanonicalC m θ
      =
    unequalFixedDifferenceFourPlusC m
      (unequalFixedDifferenceFourCanonicalPlusS m θ) := by
  have hs0 :=
    unequalFixedDifferenceFourCanonicalPlusS_nonneg
      hm hθpivot hθ0
  have hs1 :=
    unequalFixedDifferenceFourCanonicalPlusS_lt_one
      hm hθ0 hθ1
  calc
    unequalFixedDifferenceFourCanonicalC m θ
        =
      unequalFixedDifferenceFourCanonicalC m
        (unequalDampedTheta
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourCanonicalPlusS m θ)) := by
            rw [unequalFixedDifferenceFourTheta_plusS hm hθ0]
    _ =
      unequalFixedDifferenceFourPlusC m
        (unequalFixedDifferenceFourCanonicalPlusS m θ) :=
      unequalFixedDifferenceFourCanonicalC_plus_chart hm hs0 hs1

/-- Global swapped-chart identity for the canonical linear coefficient. -/
theorem unequalFixedDifferenceFourCanonicalB_eq_minus
    {m : ℕ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ)
    (hθpivot : θ ≤ unequalFixedDifferenceFourT m)
    (hθ1 : θ < 1) :
    unequalFixedDifferenceFourCanonicalB m θ
      =
    unequalFixedDifferenceFourMinusB m
      (unequalFixedDifferenceFourCanonicalMinusS m θ) := by
  have hs0 :=
    unequalFixedDifferenceFourCanonicalMinusS_nonneg
      hm hθpivot hθ1
  have hs1 :=
    unequalFixedDifferenceFourCanonicalMinusS_lt_one
      hm hθ0 hθ1
  calc
    unequalFixedDifferenceFourCanonicalB m θ
        =
      unequalFixedDifferenceFourCanonicalB m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourQ m)
            (unequalFixedDifferenceFourT m)
            (unequalFixedDifferenceFourCanonicalMinusS m θ)) := by
              rw [unequalFixedDifferenceFourTheta_minusS hm hθ1]
              ring
    _ =
      unequalFixedDifferenceFourMinusB m
        (unequalFixedDifferenceFourCanonicalMinusS m θ) :=
      unequalFixedDifferenceFourCanonicalB_minus_chart hm hs0 hs1

/-- Global swapped-chart identity for the canonical quadratic coefficient. -/
theorem unequalFixedDifferenceFourCanonicalC_eq_minus
    {m : ℕ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ)
    (hθpivot : θ ≤ unequalFixedDifferenceFourT m)
    (hθ1 : θ < 1) :
    unequalFixedDifferenceFourCanonicalC m θ
      =
    unequalFixedDifferenceFourMinusC m
      (unequalFixedDifferenceFourCanonicalMinusS m θ) := by
  have hs0 :=
    unequalFixedDifferenceFourCanonicalMinusS_nonneg
      hm hθpivot hθ1
  have hs1 :=
    unequalFixedDifferenceFourCanonicalMinusS_lt_one
      hm hθ0 hθ1
  calc
    unequalFixedDifferenceFourCanonicalC m θ
        =
      unequalFixedDifferenceFourCanonicalC m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourQ m)
            (unequalFixedDifferenceFourT m)
            (unequalFixedDifferenceFourCanonicalMinusS m θ)) := by
              rw [unequalFixedDifferenceFourTheta_minusS hm hθ1]
              ring
    _ =
      unequalFixedDifferenceFourMinusC m
        (unequalFixedDifferenceFourCanonicalMinusS m θ) :=
      unequalFixedDifferenceFourCanonicalC_minus_chart hm hs0 hs1

/--
The family perturbation has strictly negative canonical reduced risk at
every interior oracle weight.
-/
theorem unequalFixedDifferenceFourCanonicalReducedRisk_neg
    {m : ℕ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    2 * unequalFixedDifferenceFourEpsilon m
          * unequalFixedDifferenceFourCanonicalB m θ
      + unequalFixedDifferenceFourEpsilon m ^ 2
          * unequalFixedDifferenceFourCanonicalC m θ
      < 0 := by
  by_cases hside :
      unequalFixedDifferenceFourT m ≤ θ
  · rw [unequalFixedDifferenceFourCanonicalB_eq_plus
          hm hθ0 hside hθ1,
      unequalFixedDifferenceFourCanonicalC_eq_plus
          hm hθ0 hside hθ1]
    exact unequalFixedDifferenceFourPlusReducedRisk_neg
      hm
      (unequalFixedDifferenceFourCanonicalPlusS_nonneg
        hm hside hθ0)
      (unequalFixedDifferenceFourCanonicalPlusS_lt_one
        hm hθ0 hθ1)
  · have hside' :
        θ ≤ unequalFixedDifferenceFourT m :=
      le_of_not_ge hside
    rw [unequalFixedDifferenceFourCanonicalB_eq_minus
          hm hθ0 hside' hθ1,
      unequalFixedDifferenceFourCanonicalC_eq_minus
          hm hθ0 hside' hθ1]
    exact unequalFixedDifferenceFourMinusReducedRisk_neg
      hm
      (unequalFixedDifferenceFourCanonicalMinusS_nonneg
        hm hside' hθ1)
      (unequalFixedDifferenceFourCanonicalMinusS_lt_one
        hm hθ0 hθ1)

end

end GraybillDeal
