import GraybillDeal.UnequalFixedDifferenceFourRealCanonical
import GraybillDeal.UnequalFixedDifferenceFourRealReduced

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
def unequalFixedDifferenceFourRealCanonicalBIntegrand
    (m : ℝ) (θ p : ℝ) : ℝ :=
  (unequalFixedDifferenceFourRealCanonicalR m θ p - θ)
    * unequalDampedPhi
        (unequalFixedDifferenceFourRealT m)
        (unequalFixedDifferenceFourRealKappa m)
        (unequalFixedDifferenceFourRealCanonicalR m θ p)
    * (unequalFixedDifferenceFourRealC m
      - unequalFixedDifferenceFourRealK m
        / unequalFixedDifferenceFourRealCanonicalDenom m θ p)

/-- Direct canonical integrand for the quadratic reduced-risk coefficient. -/
def unequalFixedDifferenceFourRealCanonicalCIntegrand
    (m : ℝ) (θ p : ℝ) : ℝ :=
  unequalDampedPhi
      (unequalFixedDifferenceFourRealT m)
      (unequalFixedDifferenceFourRealKappa m)
      (unequalFixedDifferenceFourRealCanonicalR m θ p) ^ 2
    * unequalFixedDifferenceFourRealCKernel m
        ((unequalFixedDifferenceFourRealCanonicalDenom m θ p)⁻¹)

/-- Direct canonical linear coefficient under `Beta(m-1,m+1)`. -/
def unequalFixedDifferenceFourRealCanonicalB
    (m : ℝ) (θ : ℝ) : ℝ :=
  ∫ p, unequalFixedDifferenceFourRealCanonicalBIntegrand m θ p
    ∂betaMeasure (m - 1) (m + 1)

/-- Direct canonical quadratic coefficient under `Beta(m-1,m+1)`. -/
def unequalFixedDifferenceFourRealCanonicalC
    (m : ℝ) (θ : ℝ) : ℝ :=
  ∫ p, unequalFixedDifferenceFourRealCanonicalCIntegrand m θ p
    ∂betaMeasure (m - 1) (m + 1)

theorem measurable_unequalFixedDifferenceFourRealCanonicalBIntegrand
    (m : ℝ) (θ : ℝ) :
    Measurable (unequalFixedDifferenceFourRealCanonicalBIntegrand m θ) := by
  unfold unequalFixedDifferenceFourRealCanonicalBIntegrand
    unequalFixedDifferenceFourRealCanonicalR
    unequalFixedDifferenceFourRealCanonicalDenom
    unequalDampedPhi unequalDampedInner
  fun_prop

theorem measurable_unequalFixedDifferenceFourRealCanonicalCIntegrand
    (m : ℝ) (θ : ℝ) :
    Measurable (unequalFixedDifferenceFourRealCanonicalCIntegrand m θ) := by
  unfold unequalFixedDifferenceFourRealCanonicalCIntegrand
    unequalFixedDifferenceFourRealCanonicalR
    unequalFixedDifferenceFourRealCanonicalDenom
    unequalFixedDifferenceFourRealCKernel
    unequalDampedPhi unequalDampedInner
  fun_prop

/-! ## Family beta interval and complement identities -/

/--
Integration under the right-chart `Beta(m+1,m-1)` law is interval
integration against the polynomial density used by the analytic proof.
-/
theorem integral_betaMeasure_unequalFixedDifferenceFourRealPlus_eq_interval
    {m : ℝ} (hm : 7 ≤ m) (f : ℝ → ℝ) :
    (∫ y, f y ∂betaMeasure (m + 1) (m - 1))
      =
    ∫ y in (0 : ℝ)..1,
      unequalFixedDifferenceFourRealPlusDensity m y * f y := by
  have ha : 0 < m + 1 := by linarith
  have hb : 0 < m - 1 := by linarith
  rw [integral_betaMeasure_eq_interval_of_shapes_pos ha hb]
  apply intervalIntegral.integral_congr_uIoo
  intro y _
  unfold unequalFixedDifferenceFourRealPlusDensity
  dsimp only
  congr 1 <;> ring

/--
Integration under the left-chart `Beta(m-1,m+1)` law is interval
integration against the corresponding polynomial density.
-/
theorem integral_betaMeasure_unequalFixedDifferenceFourRealMinus_eq_interval
    {m : ℝ} (hm : 7 ≤ m) (f : ℝ → ℝ) :
    (∫ y, f y ∂betaMeasure (m - 1) (m + 1))
      =
    ∫ y in (0 : ℝ)..1,
      unequalFixedDifferenceFourRealMinusDensity m y * f y := by
  have ha : 0 < m - 1 := by linarith
  have hb : 0 < m + 1 := by linarith
  rw [integral_betaMeasure_eq_interval_of_shapes_pos ha hb]
  apply intervalIntegral.integral_congr_uIoo
  intro y _
  unfold unequalFixedDifferenceFourRealMinusDensity
  dsimp only
  congr 1 <;> ring

theorem unequalFixedDifferenceFourRealMinusDensity_eq_complementPlus
    (m : ℝ) (p : ℝ) :
    unequalFixedDifferenceFourRealMinusDensity m p
      = unequalFixedDifferenceFourRealPlusDensity m (1 - p) := by
  unfold unequalFixedDifferenceFourRealMinusDensity
    unequalFixedDifferenceFourRealPlusDensity
  rw [beta_symm_real (m - 1) (m + 1)]
  ring

/--
Complementing `Beta(m-1,m+1)` gives `Beta(m+1,m-1)`, stated directly at
the level of expectations.
-/
theorem integral_betaMeasure_unequalFixedDifferenceFourReal_complement
    {m : ℝ} (hm : 7 ≤ m) (f : ℝ → ℝ) :
    (∫ p, f p ∂betaMeasure (m - 1) (m + 1))
      =
    ∫ y, f (1 - y)
      ∂betaMeasure (m + 1) (m - 1) := by
  rw [integral_betaMeasure_unequalFixedDifferenceFourRealMinus_eq_interval
      hm,
    integral_betaMeasure_unequalFixedDifferenceFourRealPlus_eq_interval
      hm]
  calc
    (∫ p in (0 : ℝ)..1,
      unequalFixedDifferenceFourRealMinusDensity m p * f p)
        =
      ∫ p in (0 : ℝ)..1,
        (fun y =>
          unequalFixedDifferenceFourRealPlusDensity m y
            * f (1 - y)) (1 - p) := by
              apply intervalIntegral.integral_congr
              intro p _
              dsimp only
              rw [←
                unequalFixedDifferenceFourRealMinusDensity_eq_complementPlus
                  m p]
              ring
    _ =
      ∫ y in (0 : ℝ)..1,
        unequalFixedDifferenceFourRealPlusDensity m y
          * f (1 - y) := by
            simpa using
              (intervalIntegral.integral_comp_sub_left
                (fun y : ℝ =>
                  unequalFixedDifferenceFourRealPlusDensity m y
                    * f (1 - y))
                (a := (0 : ℝ)) (b := 1) 1)

/-! ## The two global chart parameters -/

/-- Right-chart coordinate for oracle weights above the beta pivot. -/
def unequalFixedDifferenceFourRealCanonicalPlusS
    (m : ℝ) (θ : ℝ) : ℝ :=
  (θ - unequalFixedDifferenceFourRealT m)
    / (unequalFixedDifferenceFourRealQ m * θ)

/-- Left-chart coordinate for oracle weights below the beta pivot. -/
def unequalFixedDifferenceFourRealCanonicalMinusS
    (m : ℝ) (θ : ℝ) : ℝ :=
  (unequalFixedDifferenceFourRealT m - θ)
    / (unequalFixedDifferenceFourRealT m * (1 - θ))

theorem unequalFixedDifferenceFourRealCanonicalPlusS_nonneg
    {m : ℝ} (hm : 7 ≤ m)
    {θ : ℝ} (hθpivot : unequalFixedDifferenceFourRealT m ≤ θ)
    (hθ0 : 0 < θ) :
    0 ≤ unequalFixedDifferenceFourRealCanonicalPlusS m θ := by
  unfold unequalFixedDifferenceFourRealCanonicalPlusS
  exact div_nonneg (sub_nonneg.mpr hθpivot)
    (mul_nonneg (unequalFixedDifferenceFourRealQ_pos hm).le hθ0.le)

theorem unequalFixedDifferenceFourRealCanonicalPlusS_lt_one
    {m : ℝ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    unequalFixedDifferenceFourRealCanonicalPlusS m θ < 1 := by
  have ht := unequalFixedDifferenceFourRealT_pos hm
  have ht := unequalFixedDifferenceFourRealT_pos hm
  have hq := unequalFixedDifferenceFourRealQ_pos hm
  have htq := unequalFixedDifferenceFourRealT_add_Q hm
  unfold unequalFixedDifferenceFourRealCanonicalPlusS
  rw [div_lt_one (mul_pos hq hθ0)]
  nlinarith

theorem unequalFixedDifferenceFourRealCanonicalMinusS_nonneg
    {m : ℝ} (hm : 7 ≤ m)
    {θ : ℝ} (hθpivot : θ ≤ unequalFixedDifferenceFourRealT m)
    (hθ1 : θ < 1) :
    0 ≤ unequalFixedDifferenceFourRealCanonicalMinusS m θ := by
  unfold unequalFixedDifferenceFourRealCanonicalMinusS
  exact div_nonneg (sub_nonneg.mpr hθpivot)
    (mul_nonneg (unequalFixedDifferenceFourRealT_pos hm).le
      (sub_nonneg.mpr hθ1.le))

theorem unequalFixedDifferenceFourRealCanonicalMinusS_lt_one
    {m : ℝ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    unequalFixedDifferenceFourRealCanonicalMinusS m θ < 1 := by
  have ht := unequalFixedDifferenceFourRealT_pos hm
  have hq := unequalFixedDifferenceFourRealQ_pos hm
  have htq := unequalFixedDifferenceFourRealT_add_Q hm
  unfold unequalFixedDifferenceFourRealCanonicalMinusS
  rw [div_lt_one (mul_pos ht (sub_pos.mpr hθ1))]
  nlinarith

theorem unequalFixedDifferenceFourRealTheta_plusS
    {m : ℝ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) :
    unequalDampedTheta
        (unequalFixedDifferenceFourRealT m)
        (unequalFixedDifferenceFourRealQ m)
        (unequalFixedDifferenceFourRealCanonicalPlusS m θ)
      = θ := by
  have ht := unequalFixedDifferenceFourRealT_pos hm
  have hq := unequalFixedDifferenceFourRealQ_pos hm
  have htq := unequalFixedDifferenceFourRealT_add_Q hm
  unfold unequalDampedTheta
    unequalFixedDifferenceFourRealCanonicalPlusS
  field_simp [ht.ne', hq.ne', hθ0.ne']
  nlinarith

theorem unequalFixedDifferenceFourRealTheta_minusS
    {m : ℝ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ1 : θ < 1) :
    unequalDampedTheta
        (unequalFixedDifferenceFourRealQ m)
        (unequalFixedDifferenceFourRealT m)
        (unequalFixedDifferenceFourRealCanonicalMinusS m θ)
      = 1 - θ := by
  have ht := unequalFixedDifferenceFourRealT_pos hm
  have hq := unequalFixedDifferenceFourRealQ_pos hm
  have htq := unequalFixedDifferenceFourRealT_add_Q hm
  have h1θ : 1 - θ ≠ 0 := ne_of_gt (sub_pos.mpr hθ1)
  unfold unequalDampedTheta
    unequalFixedDifferenceFourRealCanonicalMinusS
  have hden :
      1 -
          unequalFixedDifferenceFourRealT m
            * ((unequalFixedDifferenceFourRealT m - θ)
              / (unequalFixedDifferenceFourRealT m * (1 - θ)))
        =
      unequalFixedDifferenceFourRealQ m / (1 - θ) := by
    field_simp [ht.ne', h1θ]
    nlinarith
  rw [hden]
  field_simp [hq.ne', h1θ]

/-! ## Pointwise chart algebra -/

/-- The canonical denominator in the right chart. -/
theorem unequalFixedDifferenceFourRealCanonicalDenom_plus_chart
    {m : ℝ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourRealQ m * s ≠ 0) :
    unequalFixedDifferenceFourRealCanonicalDenom m
        (unequalDampedTheta
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealQ m) s)
        (1 - y)
      =
    unequalDampedDenom s y
      / (1 - unequalFixedDifferenceFourRealQ m * s) := by
  have ht := unequalFixedDifferenceFourRealT_pos hm
  have hq := unequalFixedDifferenceFourRealQ_pos hm
  have htq := unequalFixedDifferenceFourRealT_add_Q hm
  unfold unequalFixedDifferenceFourRealCanonicalDenom
    unequalDampedTheta unequalDampedDenom
  field_simp [ht.ne', hq.ne', hqs]
  rw [show unequalFixedDifferenceFourRealQ m
      = 1 - unequalFixedDifferenceFourRealT m by linarith]
  ring

/-- The canonical Graybill--Deal weight in the right chart. -/
theorem unequalFixedDifferenceFourRealCanonicalR_plus_chart
    {m : ℝ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourRealQ m * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalFixedDifferenceFourRealCanonicalR m
        (unequalDampedTheta
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealQ m) s)
        (1 - y)
      =
    unequalDampedR s y := by
  have ht := unequalFixedDifferenceFourRealT_pos hm
  rw [unequalFixedDifferenceFourRealCanonicalR,
    unequalFixedDifferenceFourRealCanonicalDenom_plus_chart hm hqs]
  unfold unequalDampedTheta unequalDampedR
  field_simp [ht.ne', hqs, hsy]

/-- The reciprocal canonical denominator in the right chart. -/
theorem unequalFixedDifferenceFourRealCanonicalDenom_inv_plus_chart
    {m : ℝ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourRealQ m * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    (unequalFixedDifferenceFourRealCanonicalDenom m
        (unequalDampedTheta
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealQ m) s)
        (1 - y))⁻¹
      =
    unequalDampedU (unequalFixedDifferenceFourRealQ m) s y := by
  rw [unequalFixedDifferenceFourRealCanonicalDenom_plus_chart hm hqs]
  unfold unequalDampedU
  field_simp [hqs, hsy]

/-- The canonical denominator in the sample-swapped chart. -/
theorem unequalFixedDifferenceFourRealCanonicalDenom_minus_chart
    {m : ℝ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourRealT m * s ≠ 0) :
    unequalFixedDifferenceFourRealCanonicalDenom m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourRealQ m)
            (unequalFixedDifferenceFourRealT m) s)
        y
      =
    unequalDampedDenom s y
      / (1 - unequalFixedDifferenceFourRealT m * s) := by
  have ht := unequalFixedDifferenceFourRealT_pos hm
  have hq := unequalFixedDifferenceFourRealQ_pos hm
  have htq := unequalFixedDifferenceFourRealT_add_Q hm
  unfold unequalFixedDifferenceFourRealCanonicalDenom
    unequalDampedTheta unequalDampedDenom
  field_simp [ht.ne', hq.ne', hqs]
  rw [show unequalFixedDifferenceFourRealQ m
      = 1 - unequalFixedDifferenceFourRealT m by linarith]
  ring

/-- Complementing the canonical weight gives the swapped chart weight. -/
theorem one_sub_unequalFixedDifferenceFourRealCanonicalR_minus_chart
    {m : ℝ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourRealT m * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    1 -
        unequalFixedDifferenceFourRealCanonicalR m
          (1 -
            unequalDampedTheta
              (unequalFixedDifferenceFourRealQ m)
              (unequalFixedDifferenceFourRealT m) s)
          y
      =
    unequalDampedR s y := by
  have ht := unequalFixedDifferenceFourRealT_pos hm
  have hq := unequalFixedDifferenceFourRealQ_pos hm
  have htq := unequalFixedDifferenceFourRealT_add_Q hm
  rw [unequalFixedDifferenceFourRealCanonicalR,
    unequalFixedDifferenceFourRealCanonicalDenom_minus_chart hm hqs]
  unfold unequalDampedTheta unequalDampedR
  unfold unequalDampedDenom at hsy ⊢
  field_simp [ht.ne', hq.ne', hqs, hsy]
  rw [show unequalFixedDifferenceFourRealQ m
      = 1 - unequalFixedDifferenceFourRealT m by linarith]
  ring

/-- The reciprocal canonical denominator in the swapped chart. -/
theorem unequalFixedDifferenceFourRealCanonicalDenom_inv_minus_chart
    {m : ℝ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourRealT m * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    (unequalFixedDifferenceFourRealCanonicalDenom m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourRealQ m)
            (unequalFixedDifferenceFourRealT m) s)
        y)⁻¹
      =
    unequalDampedU (unequalFixedDifferenceFourRealT m) s y := by
  rw [unequalFixedDifferenceFourRealCanonicalDenom_minus_chart hm hqs]
  unfold unequalDampedU
  field_simp [hqs, hsy]

/-- The family direction is equivariant under sample swapping. -/
theorem unequalFixedDifferenceFourRealCanonicalPhi_swap
    {m : ℝ} (hm : 7 ≤ m) (r : ℝ) :
    unequalDampedPhi
        (unequalFixedDifferenceFourRealT m)
        (unequalFixedDifferenceFourRealKappa m) r
      =
    -unequalDampedPhi
        (unequalFixedDifferenceFourRealQ m)
        (-unequalFixedDifferenceFourRealKappa m) (1 - r) := by
  have htq := unequalFixedDifferenceFourRealT_add_Q hm
  unfold unequalDampedPhi unequalDampedInner
  rw [show unequalFixedDifferenceFourRealQ m
      = 1 - unequalFixedDifferenceFourRealT m by linarith]
  ring

/-- Pointwise right-chart identification of the direct linear integrand. -/
theorem unequalFixedDifferenceFourRealCanonicalBIntegrand_plus_chart
    {m : ℝ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourRealQ m * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalFixedDifferenceFourRealCanonicalBIntegrand m
        (unequalDampedTheta
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealQ m) s)
        (1 - y)
      =
    (1 - s) ^ 2
        / (1 - unequalFixedDifferenceFourRealQ m * s)
      *
    ((unequalFixedDifferenceFourRealQ m - y) * y * (1 - y)
        * unequalDampedF
            (unequalFixedDifferenceFourRealT m)
            (unequalFixedDifferenceFourRealQ m)
            (unequalFixedDifferenceFourRealKappa m) s y
        * unequalDampedPsiNumerator
            (unequalFixedDifferenceFourRealQ m)
            (unequalFixedDifferenceFourRealC m)
            (unequalFixedDifferenceFourRealK m) s y
      / unequalDampedDenom s y ^ 6) := by
  have htq := unequalFixedDifferenceFourRealT_add_Q hm
  unfold unequalFixedDifferenceFourRealCanonicalBIntegrand
  rw [unequalFixedDifferenceFourRealCanonicalR_plus_chart hm hqs hsy]
  rw [show
      unequalFixedDifferenceFourRealK m
          / unequalFixedDifferenceFourRealCanonicalDenom m
            (unequalDampedTheta
              (unequalFixedDifferenceFourRealT m)
              (unequalFixedDifferenceFourRealQ m) s)
            (1 - y)
        =
      unequalFixedDifferenceFourRealK m
        * unequalDampedU
            (unequalFixedDifferenceFourRealQ m) s y by
          rw [div_eq_mul_inv,
            unequalFixedDifferenceFourRealCanonicalDenom_inv_plus_chart
              hm hqs hsy]]
  exact unequalDampedB_integrand_factorization htq hqs hsy

/-- Pointwise swapped-chart identification of the direct linear integrand. -/
theorem unequalFixedDifferenceFourRealCanonicalBIntegrand_minus_chart
    {m : ℝ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourRealT m * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalFixedDifferenceFourRealCanonicalBIntegrand m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourRealQ m)
            (unequalFixedDifferenceFourRealT m) s)
        y
      =
    (1 - s) ^ 2
        / (1 - unequalFixedDifferenceFourRealT m * s)
      *
    ((unequalFixedDifferenceFourRealT m - y) * y * (1 - y)
        * unequalDampedF
            (unequalFixedDifferenceFourRealQ m)
            (unequalFixedDifferenceFourRealT m)
            (-unequalFixedDifferenceFourRealKappa m) s y
        * unequalDampedPsiNumerator
            (unequalFixedDifferenceFourRealT m)
            (unequalFixedDifferenceFourRealC m)
            (unequalFixedDifferenceFourRealK m) s y
      / unequalDampedDenom s y ^ 6) := by
  let r :=
    unequalFixedDifferenceFourRealCanonicalR m
      (1 -
        unequalDampedTheta
          (unequalFixedDifferenceFourRealQ m)
          (unequalFixedDifferenceFourRealT m) s)
      y
  have hr :
      1 - r = unequalDampedR s y :=
    one_sub_unequalFixedDifferenceFourRealCanonicalR_minus_chart
      hm hqs hsy
  have hr' : r = 1 - unequalDampedR s y := by
    linarith
  have hqt :
      unequalFixedDifferenceFourRealQ m
        + unequalFixedDifferenceFourRealT m = 1 := by
    have htq := unequalFixedDifferenceFourRealT_add_Q hm
    linarith
  unfold unequalFixedDifferenceFourRealCanonicalBIntegrand
  change
    (r -
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourRealQ m)
            (unequalFixedDifferenceFourRealT m) s))
      *
      unequalDampedPhi
        (unequalFixedDifferenceFourRealT m)
        (unequalFixedDifferenceFourRealKappa m) r
      *
      (unequalFixedDifferenceFourRealC m
        - unequalFixedDifferenceFourRealK m
          / unequalFixedDifferenceFourRealCanonicalDenom m
            (1 -
              unequalDampedTheta
                (unequalFixedDifferenceFourRealQ m)
                (unequalFixedDifferenceFourRealT m) s)
            y)
      = _
  rw [unequalFixedDifferenceFourRealCanonicalPhi_swap hm r]
  rw [show
      unequalFixedDifferenceFourRealK m
          / unequalFixedDifferenceFourRealCanonicalDenom m
            (1 -
              unequalDampedTheta
                (unequalFixedDifferenceFourRealQ m)
                (unequalFixedDifferenceFourRealT m) s)
            y
        =
      unequalFixedDifferenceFourRealK m
        * unequalDampedU
            (unequalFixedDifferenceFourRealT m) s y by
          rw [div_eq_mul_inv,
            unequalFixedDifferenceFourRealCanonicalDenom_inv_minus_chart
              hm hqs hsy]]
  rw [hr, hr']
  convert
    unequalDampedB_integrand_factorization
      (t := unequalFixedDifferenceFourRealQ m)
      (q := unequalFixedDifferenceFourRealT m)
      (κ := -unequalFixedDifferenceFourRealKappa m)
      (c := unequalFixedDifferenceFourRealC m)
      (k := unequalFixedDifferenceFourRealK m)
      hqt hqs hsy using 1 <;>
    ring

/-- Pointwise right-chart identification of the direct quadratic integrand. -/
theorem unequalFixedDifferenceFourRealCanonicalCIntegrand_plus_chart
    {m : ℝ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourRealQ m * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalFixedDifferenceFourRealCanonicalCIntegrand m
        (unequalDampedTheta
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealQ m) s)
        (1 - y)
      =
    unequalFixedDifferenceFourRealPlusCIntegrand m s y := by
  unfold unequalFixedDifferenceFourRealCanonicalCIntegrand
    unequalFixedDifferenceFourRealPlusCIntegrand
  rw [unequalFixedDifferenceFourRealCanonicalR_plus_chart hm hqs hsy,
    unequalFixedDifferenceFourRealCanonicalDenom_inv_plus_chart
      hm hqs hsy]

/-- Pointwise swapped-chart identification of the direct quadratic integrand. -/
theorem unequalFixedDifferenceFourRealCanonicalCIntegrand_minus_chart
    {m : ℝ} (hm : 7 ≤ m)
    {s y : ℝ}
    (hqs : 1 - unequalFixedDifferenceFourRealT m * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalFixedDifferenceFourRealCanonicalCIntegrand m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourRealQ m)
            (unequalFixedDifferenceFourRealT m) s)
        y
      =
    unequalFixedDifferenceFourRealMinusCIntegrand m s y := by
  let r :=
    unequalFixedDifferenceFourRealCanonicalR m
      (1 -
        unequalDampedTheta
          (unequalFixedDifferenceFourRealQ m)
          (unequalFixedDifferenceFourRealT m) s)
      y
  have hr :
      1 - r = unequalDampedR s y :=
    one_sub_unequalFixedDifferenceFourRealCanonicalR_minus_chart
      hm hqs hsy
  unfold unequalFixedDifferenceFourRealCanonicalCIntegrand
    unequalFixedDifferenceFourRealMinusCIntegrand
  change
    unequalDampedPhi
        (unequalFixedDifferenceFourRealT m)
        (unequalFixedDifferenceFourRealKappa m) r ^ 2
      *
      unequalFixedDifferenceFourRealCKernel m
        ((unequalFixedDifferenceFourRealCanonicalDenom m
          (1 -
            unequalDampedTheta
              (unequalFixedDifferenceFourRealQ m)
              (unequalFixedDifferenceFourRealT m) s)
          y)⁻¹)
      = _
  rw [unequalFixedDifferenceFourRealCanonicalPhi_swap hm r,
    unequalFixedDifferenceFourRealCanonicalDenom_inv_minus_chart
      hm hqs hsy,
    ← hr]
  ring

/-! ## Integral chart identities -/

/-- The direct canonical linear coefficient in the right chart. -/
theorem unequalFixedDifferenceFourRealCanonicalB_plus_chart
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourRealCanonicalB m
        (unequalDampedTheta
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealQ m) s)
      =
    unequalFixedDifferenceFourRealPlusB m s := by
  unfold unequalFixedDifferenceFourRealCanonicalB
  rw [integral_betaMeasure_unequalFixedDifferenceFourReal_complement hm]
  unfold unequalFixedDifferenceFourRealPlusB
    unequalFixedDifferenceFourRealPlusAnalyticH
    unequalFixedDifferenceFourRealPlusH
  calc
    (∫ y,
      unequalFixedDifferenceFourRealCanonicalBIntegrand m
        (unequalDampedTheta
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealQ m) s)
        (1 - y)
      ∂betaMeasure (m + 1) (m - 1))
        =
      ∫ y in (0 : ℝ)..1,
        unequalFixedDifferenceFourRealPlusDensity m y
          *
        unequalFixedDifferenceFourRealCanonicalBIntegrand m
          (unequalDampedTheta
            (unequalFixedDifferenceFourRealT m)
            (unequalFixedDifferenceFourRealQ m) s)
          (1 - y) :=
      integral_betaMeasure_unequalFixedDifferenceFourRealPlus_eq_interval
        hm _
    _ =
      ∫ y in (0 : ℝ)..1,
        (1 - s) ^ 2
            / (1 - unequalFixedDifferenceFourRealQ m * s)
          *
        unequalDampedHIntegrand
          (unequalFixedDifferenceFourRealPlusDensity m)
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealQ m)
          (unequalFixedDifferenceFourRealKappa m)
          (unequalFixedDifferenceFourRealC m)
          (unequalFixedDifferenceFourRealK m) s y := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hy' : y ∈ Icc (0 : ℝ) 1 := by
              simpa [uIcc_of_le] using hy
            have hqs :
                1 - unequalFixedDifferenceFourRealQ m * s ≠ 0 :=
              ne_of_gt
                (one_sub_qs_pos
                  (unequalFixedDifferenceFourRealQ_pos hm).le
                  (unequalFixedDifferenceFourRealQ_le_one hm)
                  hs0 hs1)
            have hsy : unequalDampedDenom s y ≠ 0 :=
              ne_of_gt
                (unequalDampedDenom_pos
                  hs0 hs1 hy'.1 hy'.2)
            dsimp only
            rw [unequalFixedDifferenceFourRealCanonicalBIntegrand_plus_chart
              hm hqs hsy]
            unfold unequalDampedHIntegrand
            ring
    _ =
      (1 - s) ^ 2
          / (1 - unequalFixedDifferenceFourRealQ m * s)
        *
      ∫ y in (0 : ℝ)..1,
        unequalDampedHIntegrand
          (unequalFixedDifferenceFourRealPlusDensity m)
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealQ m)
          (unequalFixedDifferenceFourRealKappa m)
          (unequalFixedDifferenceFourRealC m)
          (unequalFixedDifferenceFourRealK m) s y := by
            rw [intervalIntegral.integral_const_mul]

/-- The direct canonical quadratic coefficient in the right chart. -/
theorem unequalFixedDifferenceFourRealCanonicalC_plus_chart
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourRealCanonicalC m
        (unequalDampedTheta
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealQ m) s)
      =
    unequalFixedDifferenceFourRealPlusC m s := by
  unfold unequalFixedDifferenceFourRealCanonicalC
  rw [integral_betaMeasure_unequalFixedDifferenceFourReal_complement hm]
  calc
    (∫ y,
      unequalFixedDifferenceFourRealCanonicalCIntegrand m
        (unequalDampedTheta
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealQ m) s)
        (1 - y)
      ∂betaMeasure (m + 1) (m - 1))
        =
      ∫ y in (0 : ℝ)..1,
        unequalFixedDifferenceFourRealPlusDensity m y
          *
        unequalFixedDifferenceFourRealCanonicalCIntegrand m
          (unequalDampedTheta
            (unequalFixedDifferenceFourRealT m)
            (unequalFixedDifferenceFourRealQ m) s)
          (1 - y) :=
      integral_betaMeasure_unequalFixedDifferenceFourRealPlus_eq_interval
        hm _
    _ =
      ∫ y in (0 : ℝ)..1,
        unequalFixedDifferenceFourRealPlusDensity m y
          * unequalFixedDifferenceFourRealPlusCIntegrand m s y := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hy' : y ∈ Icc (0 : ℝ) 1 := by
              simpa [uIcc_of_le] using hy
            have hqs :
                1 - unequalFixedDifferenceFourRealQ m * s ≠ 0 :=
              ne_of_gt
                (one_sub_qs_pos
                  (unequalFixedDifferenceFourRealQ_pos hm).le
                  (unequalFixedDifferenceFourRealQ_le_one hm)
                  hs0 hs1)
            have hsy : unequalDampedDenom s y ≠ 0 :=
              ne_of_gt
                (unequalDampedDenom_pos
                  hs0 hs1 hy'.1 hy'.2)
            dsimp only
            rw [unequalFixedDifferenceFourRealCanonicalCIntegrand_plus_chart
              hm hqs hsy]
    _ =
      ∫ y, unequalFixedDifferenceFourRealPlusCIntegrand m s y
        ∂betaMeasure (m + 1) (m - 1) := by
          symm
          exact
            integral_betaMeasure_unequalFixedDifferenceFourRealPlus_eq_interval
              hm _
    _ = unequalFixedDifferenceFourRealPlusC m s := rfl

/-- The direct canonical linear coefficient in the sample-swapped chart. -/
theorem unequalFixedDifferenceFourRealCanonicalB_minus_chart
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourRealCanonicalB m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourRealQ m)
            (unequalFixedDifferenceFourRealT m) s)
      =
    unequalFixedDifferenceFourRealMinusB m s := by
  unfold unequalFixedDifferenceFourRealCanonicalB
    unequalFixedDifferenceFourRealMinusB
    unequalFixedDifferenceFourRealMinusAnalyticH
    unequalFixedDifferenceFourRealMinusH
  calc
    (∫ y,
      unequalFixedDifferenceFourRealCanonicalBIntegrand m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourRealQ m)
            (unequalFixedDifferenceFourRealT m) s)
        y
      ∂betaMeasure (m - 1) (m + 1))
        =
      ∫ y in (0 : ℝ)..1,
        unequalFixedDifferenceFourRealMinusDensity m y
          *
        unequalFixedDifferenceFourRealCanonicalBIntegrand m
          (1 -
            unequalDampedTheta
              (unequalFixedDifferenceFourRealQ m)
              (unequalFixedDifferenceFourRealT m) s)
          y :=
      integral_betaMeasure_unequalFixedDifferenceFourRealMinus_eq_interval
        hm _
    _ =
      ∫ y in (0 : ℝ)..1,
        (1 - s) ^ 2
            / (1 - unequalFixedDifferenceFourRealT m * s)
          *
        unequalDampedHIntegrand
          (unequalFixedDifferenceFourRealMinusDensity m)
          (unequalFixedDifferenceFourRealQ m)
          (unequalFixedDifferenceFourRealT m)
          (-unequalFixedDifferenceFourRealKappa m)
          (unequalFixedDifferenceFourRealC m)
          (unequalFixedDifferenceFourRealK m) s y := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hy' : y ∈ Icc (0 : ℝ) 1 := by
              simpa [uIcc_of_le] using hy
            have hqs :
                1 - unequalFixedDifferenceFourRealT m * s ≠ 0 :=
              ne_of_gt
                (one_sub_qs_pos
                  (unequalFixedDifferenceFourRealT_pos hm).le
                  (unequalFixedDifferenceFourRealT_le_one hm)
                  hs0 hs1)
            have hsy : unequalDampedDenom s y ≠ 0 :=
              ne_of_gt
                (unequalDampedDenom_pos
                  hs0 hs1 hy'.1 hy'.2)
            dsimp only
            rw [unequalFixedDifferenceFourRealCanonicalBIntegrand_minus_chart
              hm hqs hsy]
            unfold unequalDampedHIntegrand
            ring
    _ =
      (1 - s) ^ 2
          / (1 - unequalFixedDifferenceFourRealT m * s)
        *
      ∫ y in (0 : ℝ)..1,
        unequalDampedHIntegrand
          (unequalFixedDifferenceFourRealMinusDensity m)
          (unequalFixedDifferenceFourRealQ m)
          (unequalFixedDifferenceFourRealT m)
          (-unequalFixedDifferenceFourRealKappa m)
          (unequalFixedDifferenceFourRealC m)
          (unequalFixedDifferenceFourRealK m) s y := by
            rw [intervalIntegral.integral_const_mul]

/-- The direct canonical quadratic coefficient in the swapped chart. -/
theorem unequalFixedDifferenceFourRealCanonicalC_minus_chart
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourRealCanonicalC m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourRealQ m)
            (unequalFixedDifferenceFourRealT m) s)
      =
    unequalFixedDifferenceFourRealMinusC m s := by
  unfold unequalFixedDifferenceFourRealCanonicalC
  calc
    (∫ y,
      unequalFixedDifferenceFourRealCanonicalCIntegrand m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourRealQ m)
            (unequalFixedDifferenceFourRealT m) s)
        y
      ∂betaMeasure (m - 1) (m + 1))
        =
      ∫ y in (0 : ℝ)..1,
        unequalFixedDifferenceFourRealMinusDensity m y
          *
        unequalFixedDifferenceFourRealCanonicalCIntegrand m
          (1 -
            unequalDampedTheta
              (unequalFixedDifferenceFourRealQ m)
              (unequalFixedDifferenceFourRealT m) s)
          y :=
      integral_betaMeasure_unequalFixedDifferenceFourRealMinus_eq_interval
        hm _
    _ =
      ∫ y in (0 : ℝ)..1,
        unequalFixedDifferenceFourRealMinusDensity m y
          * unequalFixedDifferenceFourRealMinusCIntegrand m s y := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hy' : y ∈ Icc (0 : ℝ) 1 := by
              simpa [uIcc_of_le] using hy
            have hqs :
                1 - unequalFixedDifferenceFourRealT m * s ≠ 0 :=
              ne_of_gt
                (one_sub_qs_pos
                  (unequalFixedDifferenceFourRealT_pos hm).le
                  (unequalFixedDifferenceFourRealT_le_one hm)
                  hs0 hs1)
            have hsy : unequalDampedDenom s y ≠ 0 :=
              ne_of_gt
                (unequalDampedDenom_pos
                  hs0 hs1 hy'.1 hy'.2)
            dsimp only
            rw [unequalFixedDifferenceFourRealCanonicalCIntegrand_minus_chart
              hm hqs hsy]
    _ =
      ∫ y, unequalFixedDifferenceFourRealMinusCIntegrand m s y
        ∂betaMeasure (m - 1) (m + 1) := by
          symm
          exact
            integral_betaMeasure_unequalFixedDifferenceFourRealMinus_eq_interval
              hm _
    _ = unequalFixedDifferenceFourRealMinusC m s := rfl

/-! ## Global canonical identities and reduced-risk inequality -/

/-- Global right-chart identity for the canonical linear coefficient. -/
theorem unequalFixedDifferenceFourRealCanonicalB_eq_plus
    {m : ℝ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ)
    (hθpivot : unequalFixedDifferenceFourRealT m ≤ θ)
    (hθ1 : θ < 1) :
    unequalFixedDifferenceFourRealCanonicalB m θ
      =
    unequalFixedDifferenceFourRealPlusB m
      (unequalFixedDifferenceFourRealCanonicalPlusS m θ) := by
  have hs0 :=
    unequalFixedDifferenceFourRealCanonicalPlusS_nonneg
      hm hθpivot hθ0
  have hs1 :=
    unequalFixedDifferenceFourRealCanonicalPlusS_lt_one
      hm hθ0 hθ1
  calc
    unequalFixedDifferenceFourRealCanonicalB m θ
        =
      unequalFixedDifferenceFourRealCanonicalB m
        (unequalDampedTheta
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealQ m)
          (unequalFixedDifferenceFourRealCanonicalPlusS m θ)) := by
            rw [unequalFixedDifferenceFourRealTheta_plusS hm hθ0]
    _ =
      unequalFixedDifferenceFourRealPlusB m
        (unequalFixedDifferenceFourRealCanonicalPlusS m θ) :=
      unequalFixedDifferenceFourRealCanonicalB_plus_chart hm hs0 hs1

/-- Global right-chart identity for the canonical quadratic coefficient. -/
theorem unequalFixedDifferenceFourRealCanonicalC_eq_plus
    {m : ℝ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ)
    (hθpivot : unequalFixedDifferenceFourRealT m ≤ θ)
    (hθ1 : θ < 1) :
    unequalFixedDifferenceFourRealCanonicalC m θ
      =
    unequalFixedDifferenceFourRealPlusC m
      (unequalFixedDifferenceFourRealCanonicalPlusS m θ) := by
  have hs0 :=
    unequalFixedDifferenceFourRealCanonicalPlusS_nonneg
      hm hθpivot hθ0
  have hs1 :=
    unequalFixedDifferenceFourRealCanonicalPlusS_lt_one
      hm hθ0 hθ1
  calc
    unequalFixedDifferenceFourRealCanonicalC m θ
        =
      unequalFixedDifferenceFourRealCanonicalC m
        (unequalDampedTheta
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealQ m)
          (unequalFixedDifferenceFourRealCanonicalPlusS m θ)) := by
            rw [unequalFixedDifferenceFourRealTheta_plusS hm hθ0]
    _ =
      unequalFixedDifferenceFourRealPlusC m
        (unequalFixedDifferenceFourRealCanonicalPlusS m θ) :=
      unequalFixedDifferenceFourRealCanonicalC_plus_chart hm hs0 hs1

/-- Global swapped-chart identity for the canonical linear coefficient. -/
theorem unequalFixedDifferenceFourRealCanonicalB_eq_minus
    {m : ℝ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ)
    (hθpivot : θ ≤ unequalFixedDifferenceFourRealT m)
    (hθ1 : θ < 1) :
    unequalFixedDifferenceFourRealCanonicalB m θ
      =
    unequalFixedDifferenceFourRealMinusB m
      (unequalFixedDifferenceFourRealCanonicalMinusS m θ) := by
  have hs0 :=
    unequalFixedDifferenceFourRealCanonicalMinusS_nonneg
      hm hθpivot hθ1
  have hs1 :=
    unequalFixedDifferenceFourRealCanonicalMinusS_lt_one
      hm hθ0 hθ1
  calc
    unequalFixedDifferenceFourRealCanonicalB m θ
        =
      unequalFixedDifferenceFourRealCanonicalB m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourRealQ m)
            (unequalFixedDifferenceFourRealT m)
            (unequalFixedDifferenceFourRealCanonicalMinusS m θ)) := by
              rw [unequalFixedDifferenceFourRealTheta_minusS hm hθ1]
              ring
    _ =
      unequalFixedDifferenceFourRealMinusB m
        (unequalFixedDifferenceFourRealCanonicalMinusS m θ) :=
      unequalFixedDifferenceFourRealCanonicalB_minus_chart hm hs0 hs1

/-- Global swapped-chart identity for the canonical quadratic coefficient. -/
theorem unequalFixedDifferenceFourRealCanonicalC_eq_minus
    {m : ℝ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ)
    (hθpivot : θ ≤ unequalFixedDifferenceFourRealT m)
    (hθ1 : θ < 1) :
    unequalFixedDifferenceFourRealCanonicalC m θ
      =
    unequalFixedDifferenceFourRealMinusC m
      (unequalFixedDifferenceFourRealCanonicalMinusS m θ) := by
  have hs0 :=
    unequalFixedDifferenceFourRealCanonicalMinusS_nonneg
      hm hθpivot hθ1
  have hs1 :=
    unequalFixedDifferenceFourRealCanonicalMinusS_lt_one
      hm hθ0 hθ1
  calc
    unequalFixedDifferenceFourRealCanonicalC m θ
        =
      unequalFixedDifferenceFourRealCanonicalC m
        (1 -
          unequalDampedTheta
            (unequalFixedDifferenceFourRealQ m)
            (unequalFixedDifferenceFourRealT m)
            (unequalFixedDifferenceFourRealCanonicalMinusS m θ)) := by
              rw [unequalFixedDifferenceFourRealTheta_minusS hm hθ1]
              ring
    _ =
      unequalFixedDifferenceFourRealMinusC m
        (unequalFixedDifferenceFourRealCanonicalMinusS m θ) :=
      unequalFixedDifferenceFourRealCanonicalC_minus_chart hm hs0 hs1

/--
The family perturbation has strictly negative canonical reduced risk at
every interior oracle weight.
-/
theorem unequalFixedDifferenceFourRealCanonicalReducedRisk_neg
    {m : ℝ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    2 * unequalFixedDifferenceFourRealEpsilon m
          * unequalFixedDifferenceFourRealCanonicalB m θ
      + unequalFixedDifferenceFourRealEpsilon m ^ 2
          * unequalFixedDifferenceFourRealCanonicalC m θ
      < 0 := by
  by_cases hside :
      unequalFixedDifferenceFourRealT m ≤ θ
  · rw [unequalFixedDifferenceFourRealCanonicalB_eq_plus
          hm hθ0 hside hθ1,
      unequalFixedDifferenceFourRealCanonicalC_eq_plus
          hm hθ0 hside hθ1]
    exact unequalFixedDifferenceFourRealPlusReducedRisk_neg
      hm
      (unequalFixedDifferenceFourRealCanonicalPlusS_nonneg
        hm hside hθ0)
      (unequalFixedDifferenceFourRealCanonicalPlusS_lt_one
        hm hθ0 hθ1)
  · have hside' :
        θ ≤ unequalFixedDifferenceFourRealT m :=
      le_of_not_ge hside
    rw [unequalFixedDifferenceFourRealCanonicalB_eq_minus
          hm hθ0 hside' hθ1,
      unequalFixedDifferenceFourRealCanonicalC_eq_minus
          hm hθ0 hside' hθ1]
    exact unequalFixedDifferenceFourRealMinusReducedRisk_neg
      hm
      (unequalFixedDifferenceFourRealCanonicalMinusS_nonneg
        hm hside' hθ1)
      (unequalFixedDifferenceFourRealCanonicalMinusS_lt_one
        hm hθ0 hθ1)

end

end GraybillDeal
