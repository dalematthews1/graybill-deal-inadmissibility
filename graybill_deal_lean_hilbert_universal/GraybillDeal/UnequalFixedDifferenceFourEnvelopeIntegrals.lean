import GraybillDeal.UnequalFixedDifferenceFourCoordinates
import GraybillDeal.UnequalFixedDifferenceFourBetaRatios
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Distributions.Beta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-!
# Quadratic envelope integrals for the fixed-difference-four family

This file evaluates the inverse-beta moments used by the quadratic
`C`-envelope for

`(n₁,n₂) = (2m-1,2m+3)`, `m ≥ 7`.

The right chart uses `Y ~ Beta(m+1,m-1)` and needs the moments
`E[Y²/(1-Y)²]` and `E[Y²/(1-Y)⁴]`.  The left chart uses the swapped law
`Y ~ Beta(m-1,m+1)`.  The apparent singularities are integrable because
all shifted second beta parameters remain positive when `m ≥ 7`.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- The inverse-beta monomial used by both quadratic envelopes. -/
def unequalFD4InverseBetaMomentIntegrand (d y : ℝ) : ℝ :=
  y ^ (2 : ℝ) / (1 - y) ^ d

/--
The common family envelope, written as a linear combination of the two
inverse-beta monomials.  This form makes its expectation linear without
introducing any endpoint division identities into the integration proof.
-/
def unequalFixedDifferenceFourEnvelopeFactor (m : ℕ) (y : ℝ) : ℝ :=
  unequalFixedDifferenceFourQ m ^ 2
    * (unequalFixedDifferenceFourC m ^ 2
        * unequalFD4InverseBetaMomentIntegrand 2 y
      + unequalFixedDifferenceFourEll m
        * unequalFD4InverseBetaMomentIntegrand 4 y)

/--
On the open beta support, the linear-combination envelope is exactly the
product-form envelope supplied by the coordinate theorem.
-/
theorem unequalFixedDifferenceFourEnvelopeFactor_eq
    (m : ℕ) {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    unequalFixedDifferenceFourEnvelopeFactor m y
      =
    unequalFixedDifferenceFourQ m ^ 2
      * (y ^ 2 / (1 - y) ^ 2)
      * (unequalFixedDifferenceFourC m ^ 2
        + unequalFixedDifferenceFourEll m / (1 - y) ^ 2) := by
  have hy : 1 - y ≠ 0 := ne_of_gt (sub_pos.mpr hy1)
  unfold unequalFixedDifferenceFourEnvelopeFactor
    unequalFD4InverseBetaMomentIntegrand
  rw [Real.rpow_two, Real.rpow_two]
  rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
  field_simp [hy]

private theorem betaMeasure_unequalFD4_ae_mem_Ioo
    {a b : ℝ} :
    ∀ᵐ y : ℝ ∂betaMeasure a b, y ∈ Ioo (0 : ℝ) 1 := by
  unfold betaMeasure betaPDF
  rw [ae_withDensity_iff
    ((measurable_betaPDFReal a b).ennreal_ofReal)]
  filter_upwards [] with y hy
  by_contra hmem
  have hzero : betaPDF a b y = 0 := by
    rcases not_and_or.mp (by simpa only [mem_Ioo] using hmem) with hy0 | hy1
    · exact betaPDF_eq_zero_of_nonpos (le_of_not_gt hy0)
    · exact betaPDF_eq_zero_of_one_le (le_of_not_gt hy1)
  exact hy hzero

/-! ## The sample-swapped pointwise envelope -/

/--
The swapped inner direction has the same uniform absolute bound as the
right-chart direction.  This follows by the involution `r ↦ 1-r`.
-/
theorem abs_unequalFixedDifferenceFourSwappedInner_le_Q
    {m : ℕ} (hm : 7 ≤ m) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) :
    |unequalDampedInner
        (unequalFixedDifferenceFourQ m)
        (-unequalFixedDifferenceFourKappa m) r|
      ≤ unequalFixedDifferenceFourQ m := by
  have hr' : 1 - r ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hr.1, hr.2]
  have h :=
    abs_unequalFixedDifferenceFourInner_le_Q hm hr'
  have heq :
      unequalDampedInner
          (unequalFixedDifferenceFourQ m)
          (-unequalFixedDifferenceFourKappa m) r
        =
      -unequalDampedInner
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourKappa m) (1 - r) := by
    have htq := unequalFixedDifferenceFourT_add_Q hm
    unfold unequalDampedInner
    rw [show unequalFixedDifferenceFourQ m
        = 1 - unequalFixedDifferenceFourT m by linarith]
    ring
  rw [heq, abs_neg]
  exact h

/--
The endpoint-damped direction on the swapped chart obeys the same
`q² y²/(1-y)²` envelope.
-/
theorem unequalFixedDifferenceFourSwappedPhi_sq_le_envelope
    {m : ℕ} (hm : 7 ≤ m)
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    unequalDampedPhi
        (unequalFixedDifferenceFourQ m)
        (-unequalFixedDifferenceFourKappa m)
        (unequalDampedR s y) ^ 2
      ≤
    (1 - s) ^ 2 * unequalFixedDifferenceFourQ m ^ 2
      * (y ^ 2 / (1 - y) ^ 2) := by
  have hr := unequalDampedR_mem_Icc hs0 hs1 hy0 hy1.le
  have hrprod0 :
      0 ≤ unequalDampedR s y * (1 - unequalDampedR s y) :=
    mul_nonneg hr.1 (sub_nonneg.mpr hr.2)
  have henv0 : 0 ≤ (1 - s) * y / (1 - y) := by
    positivity
  have hrprod :=
    unequalDampedR_mul_one_sub_le hs0 hs1 hy0 hy1
  have hrprod_sq :
      (unequalDampedR s y * (1 - unequalDampedR s y)) ^ 2
        ≤ ((1 - s) * y / (1 - y)) ^ 2 :=
    (sq_le_sq₀ hrprod0 henv0).2 hrprod
  have hinner :=
    abs_unequalFixedDifferenceFourSwappedInner_le_Q hm hr
  have hinner_sq :
      unequalDampedInner
          (unequalFixedDifferenceFourQ m)
          (-unequalFixedDifferenceFourKappa m)
          (unequalDampedR s y) ^ 2
        ≤ unequalFixedDifferenceFourQ m ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_pos (unequalFixedDifferenceFourQ_pos hm)] using hinner
  rw [unequalDampedPhi]
  calc
    (unequalDampedR s y * (1 - unequalDampedR s y)
        * unequalDampedInner
          (unequalFixedDifferenceFourQ m)
          (-unequalFixedDifferenceFourKappa m)
          (unequalDampedR s y)) ^ 2
        =
      (unequalDampedR s y * (1 - unequalDampedR s y)) ^ 2
        * unequalDampedInner
          (unequalFixedDifferenceFourQ m)
          (-unequalFixedDifferenceFourKappa m)
          (unequalDampedR s y) ^ 2 := by
            ring
    _ ≤
      ((1 - s) * y / (1 - y)) ^ 2
        * unequalFixedDifferenceFourQ m ^ 2 :=
      mul_le_mul hrprod_sq hinner_sq
        (sq_nonneg _) (sq_nonneg _)
    _ =
      (1 - s) ^ 2 * unequalFixedDifferenceFourQ m ^ 2
        * (y ^ 2 / (1 - y) ^ 2) := by
          field_simp [ne_of_gt (sub_pos.mpr hy1)]

/-- The sample-swapped family pointwise quadratic envelope. -/
theorem unequalFixedDifferenceFourSwappedC_pointwise_le_envelope
    {m : ℕ} (hm : 7 ≤ m)
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    unequalDampedPhi
        (unequalFixedDifferenceFourQ m)
        (-unequalFixedDifferenceFourKappa m)
        (unequalDampedR s y) ^ 2
      * unequalFixedDifferenceFourCKernel m
          (unequalDampedU
            (unequalFixedDifferenceFourT m) s y)
      ≤
    (1 - s) ^ 2 * unequalFixedDifferenceFourQ m ^ 2
      * (y ^ 2 / (1 - y) ^ 2)
      * (unequalFixedDifferenceFourC m ^ 2
        + unequalFixedDifferenceFourEll m / (1 - y) ^ 2) := by
  have ht0 := (unequalFixedDifferenceFourT_pos hm).le
  have ht1 := unequalFixedDifferenceFourT_le_one hm
  have hu :=
    unequalDampedU_pos ht0 ht1 hs0 hs1 hy0 hy1.le
  have hu_sq :=
    unequalDampedU_sq_le ht0 ht1 hs0 hs1 hy0 hy1
  have hk :=
    unequalFixedDifferenceFourCKernel_le hm hu.le
  have hEll := (unequalFixedDifferenceFourEll_pos hm).le
  have hy : 0 < 1 - y := sub_pos.mpr hy1
  have hk' :
      unequalFixedDifferenceFourC m ^ 2
          + unequalFixedDifferenceFourEll m
            * unequalDampedU
                (unequalFixedDifferenceFourT m) s y ^ 2
        ≤ unequalFixedDifferenceFourC m ^ 2
          + unequalFixedDifferenceFourEll m / (1 - y) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hu_sq hEll
    have heq :
        unequalFixedDifferenceFourEll m * (1 / (1 - y)) ^ 2
          = unequalFixedDifferenceFourEll m / (1 - y) ^ 2 := by
      field_simp [ne_of_gt hy]
    rw [← heq]
    linarith
  have hphi :=
    unequalFixedDifferenceFourSwappedPhi_sq_le_envelope
      hm hs0 hs1 hy0 hy1
  have hupper0 :
      0 ≤ unequalFixedDifferenceFourC m ^ 2
        + unequalFixedDifferenceFourEll m / (1 - y) ^ 2 := by
    positivity
  calc
    unequalDampedPhi
          (unequalFixedDifferenceFourQ m)
          (-unequalFixedDifferenceFourKappa m)
          (unequalDampedR s y) ^ 2
        * unequalFixedDifferenceFourCKernel m
            (unequalDampedU
              (unequalFixedDifferenceFourT m) s y)
        ≤
      unequalDampedPhi
          (unequalFixedDifferenceFourQ m)
          (-unequalFixedDifferenceFourKappa m)
          (unequalDampedR s y) ^ 2
        * (unequalFixedDifferenceFourC m ^ 2
          + unequalFixedDifferenceFourEll m
            * unequalDampedU
                (unequalFixedDifferenceFourT m) s y ^ 2) :=
      mul_le_mul_of_nonneg_left hk (sq_nonneg _)
    _ ≤
      unequalDampedPhi
          (unequalFixedDifferenceFourQ m)
          (-unequalFixedDifferenceFourKappa m)
          (unequalDampedR s y) ^ 2
        * (unequalFixedDifferenceFourC m ^ 2
          + unequalFixedDifferenceFourEll m / (1 - y) ^ 2) :=
      mul_le_mul_of_nonneg_left hk' (sq_nonneg _)
    _ ≤
      ((1 - s) ^ 2 * unequalFixedDifferenceFourQ m ^ 2
        * (y ^ 2 / (1 - y) ^ 2))
        * (unequalFixedDifferenceFourC m ^ 2
          + unequalFixedDifferenceFourEll m / (1 - y) ^ 2) :=
      mul_le_mul_of_nonneg_right hphi hupper0

private theorem betaPDF_toReal_mul_inverseBetaMoment
    {α β d y : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hα₂ : 0 < α + 2) (hβd : 0 < β - d) :
    unequalFD4InverseBetaMomentIntegrand d y
        * (betaPDF α β y).toReal
      =
    (beta (α + 2) (β - d) / beta α β)
        * (betaPDF (α + 2) (β - d) y).toReal := by
  by_cases hy : 0 < y ∧ y < 1
  · have hy₁ : 0 < 1 - y := sub_pos.mpr hy.2
    have hbeta : beta α β ≠ 0 := (beta_pos hα hβ).ne'
    have hbetaShift :
        beta (α + 2) (β - d) ≠ 0 :=
      (beta_pos hα₂ hβd).ne'
    rw [betaPDF, betaPDF, ENNReal.toReal_ofReal
      (le_of_lt (betaPDFReal_pos hy.1 hy.2 hα hβ)),
      ENNReal.toReal_ofReal
        (le_of_lt (betaPDFReal_pos hy.1 hy.2 hα₂ hβd)),
      betaPDFReal, betaPDFReal, if_pos hy, if_pos hy]
    have hyPow :
        y ^ (α - 1) * y ^ (2 : ℝ) = y ^ (α + 2 - 1) := by
      rw [← Real.rpow_add hy.1]
      congr 1
      ring
    have hOnePow :
        (1 - y) ^ (β - d - 1) * (1 - y) ^ d
          = (1 - y) ^ (β - 1) := by
      rw [← Real.rpow_add hy₁]
      congr 1
      ring
    unfold unequalFD4InverseBetaMomentIntegrand
    field_simp [hbeta, hbetaShift,
      (Real.rpow_pos_of_pos hy.1 d).ne',
      (Real.rpow_pos_of_pos hy₁ d).ne']
    calc
      y ^ (2 : ℝ) * y ^ (α - 1) * (1 - y) ^ (β - 1)
          =
        (y ^ (α - 1) * y ^ (2 : ℝ))
          * (1 - y) ^ (β - 1) := by ring
      _ =
        y ^ (α + 2 - 1) * (1 - y) ^ (β - 1) := by
          rw [hyPow]
      _ =
        (1 - y) ^ d * y ^ (α + 2 - 1)
          * (1 - y) ^ (β - d - 1) := by
          rw [← hOnePow]
          ring
  · have hshift : ¬(0 < y ∧ y < 1) := hy
    simp [betaPDF, betaPDFReal, hshift]

private theorem integrable_betaPDF_toReal
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Integrable (fun y => (betaPDF α β y).toReal) volume := by
  letI : IsProbabilityMeasure (betaMeasure α β) :=
    isProbabilityMeasureBeta hα hβ
  have hone :
      Integrable (fun _ : ℝ => (1 : ℝ)) (betaMeasure α β) :=
    integrable_const 1
  unfold betaMeasure at hone
  unfold betaPDF at hone
  rw [integrable_withDensity_iff
      ((measurable_betaPDFReal α β).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hone
  simpa only [betaPDF, one_mul] using hone

private theorem integral_betaPDF_toReal
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (∫ y, (betaPDF α β y).toReal) = 1 := by
  letI : IsProbabilityMeasure (betaMeasure α β) :=
    isProbabilityMeasureBeta hα hβ
  have hone :
      (∫ _ : ℝ, (1 : ℝ) ∂betaMeasure α β) = 1 := by
    simp
  unfold betaMeasure at hone
  unfold betaPDF at hone
  rw [integral_withDensity_eq_integral_toReal_smul
      ((measurable_betaPDFReal α β).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hone
  simpa only [betaPDF, smul_eq_mul, one_mul, mul_one] using hone

/--
Generic inverse-beta moment identity:

`E[Y²/(1-Y)^d] = B(α+2,β-d)/B(α,β)`.
-/
theorem integral_unequalFD4InverseBetaMomentIntegrand
    {α β d : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hα₂ : 0 < α + 2) (hβd : 0 < β - d) :
    (∫ y, unequalFD4InverseBetaMomentIntegrand d y
        ∂betaMeasure α β)
      =
    beta (α + 2) (β - d) / beta α β := by
  rw [betaMeasure]
  unfold betaPDF
  rw [
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_betaPDFReal α β).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  change
    (∫ y, (betaPDF α β y).toReal
      * unequalFD4InverseBetaMomentIntegrand d y)
      =
    beta (α + 2) (β - d) / beta α β
  calc
    (∫ y, (betaPDF α β y).toReal
        * unequalFD4InverseBetaMomentIntegrand d y)
        =
      ∫ y, (beta (α + 2) (β - d) / beta α β)
        * (betaPDF (α + 2) (β - d) y).toReal := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [mul_comm]
          exact
            betaPDF_toReal_mul_inverseBetaMoment
              hα hβ hα₂ hβd
    _ =
      (beta (α + 2) (β - d) / beta α β)
        * ∫ y, (betaPDF (α + 2) (β - d) y).toReal := by
          rw [integral_const_mul]
    _ = beta (α + 2) (β - d) / beta α β := by
      rw [integral_betaPDF_toReal hα₂ hβd, mul_one]

/-- Integrability companion to the generic inverse-beta moment identity. -/
theorem integrable_unequalFD4InverseBetaMomentIntegrand
    {α β d : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hα₂ : 0 < α + 2) (hβd : 0 < β - d) :
    Integrable (unequalFD4InverseBetaMomentIntegrand d)
      (betaMeasure α β) := by
  unfold betaMeasure
  unfold betaPDF
  rw [integrable_withDensity_iff
      ((measurable_betaPDFReal α β).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hshift :=
    (integrable_betaPDF_toReal hα₂ hβd).const_mul
      (beta (α + 2) (β - d) / beta α β)
  apply hshift.congr
  filter_upwards [] with y
  change
    (beta (α + 2) (β - d) / beta α β)
        * (betaPDF (α + 2) (β - d) y).toReal
      =
    unequalFD4InverseBetaMomentIntegrand d y
      * (betaPDF α β y).toReal
  exact
    (betaPDF_toReal_mul_inverseBetaMoment
      hα hβ hα₂ hβd).symm

/-! ## Exact envelope expectations before rational simplification -/

/-- The family envelope is integrable under the right-chart beta law. -/
theorem integrable_unequalFixedDifferenceFourEnvelopeFactor_plus
    {m : ℕ} (hm : 7 ≤ m) :
    Integrable (unequalFixedDifferenceFourEnvelopeFactor m)
      (betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1)) := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have h2 :=
    integrable_unequalFD4InverseBetaMomentIntegrand
      (α := (m : ℝ) + 1) (β := (m : ℝ) - 1) (d := 2)
      (by linarith) (by linarith) (by linarith) (by linarith)
  have h4 :=
    integrable_unequalFD4InverseBetaMomentIntegrand
      (α := (m : ℝ) + 1) (β := (m : ℝ) - 1) (d := 4)
      (by linarith) (by linarith) (by linarith) (by linarith)
  change Integrable
    (fun y => unequalFixedDifferenceFourQ m ^ 2
      * (unequalFixedDifferenceFourC m ^ 2
          * unequalFD4InverseBetaMomentIntegrand 2 y
        + unequalFixedDifferenceFourEll m
          * unequalFD4InverseBetaMomentIntegrand 4 y))
    (betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1))
  simpa only [Pi.add_apply] using
    ((h2.const_mul (unequalFixedDifferenceFourC m ^ 2)).add
      (h4.const_mul (unequalFixedDifferenceFourEll m))).const_mul
        (unequalFixedDifferenceFourQ m ^ 2)

/-- The family envelope is integrable under the sample-swapped beta law. -/
theorem integrable_unequalFixedDifferenceFourEnvelopeFactor_minus
    {m : ℕ} (hm : 7 ≤ m) :
    Integrable (unequalFixedDifferenceFourEnvelopeFactor m)
      (betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1)) := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have h2 :=
    integrable_unequalFD4InverseBetaMomentIntegrand
      (α := (m : ℝ) - 1) (β := (m : ℝ) + 1) (d := 2)
      (by linarith) (by linarith) (by linarith) (by linarith)
  have h4 :=
    integrable_unequalFD4InverseBetaMomentIntegrand
      (α := (m : ℝ) - 1) (β := (m : ℝ) + 1) (d := 4)
      (by linarith) (by linarith) (by linarith) (by linarith)
  change Integrable
    (fun y => unequalFixedDifferenceFourQ m ^ 2
      * (unequalFixedDifferenceFourC m ^ 2
          * unequalFD4InverseBetaMomentIntegrand 2 y
        + unequalFixedDifferenceFourEll m
          * unequalFD4InverseBetaMomentIntegrand 4 y))
    (betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
  simpa only [Pi.add_apply] using
    ((h2.const_mul (unequalFixedDifferenceFourC m ^ 2)).add
      (h4.const_mul (unequalFixedDifferenceFourEll m))).const_mul
        (unequalFixedDifferenceFourQ m ^ 2)

/--
The right-chart envelope expectation as the two shifted beta ratios.
The following beta-ratio module can simplify this expression directly to
`unequalFixedDifferenceFourMPlus m`.
-/
theorem integral_unequalFixedDifferenceFourEnvelopeFactor_plus_betaRatios
    {m : ℕ} (hm : 7 ≤ m) :
    (∫ y, unequalFixedDifferenceFourEnvelopeFactor m y
      ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1))
      =
    unequalFixedDifferenceFourQ m ^ 2
      * (unequalFixedDifferenceFourC m ^ 2
          * (beta ((m : ℝ) + 3) ((m : ℝ) - 3)
              / beta ((m : ℝ) + 1) ((m : ℝ) - 1))
        + unequalFixedDifferenceFourEll m
          * (beta ((m : ℝ) + 3) ((m : ℝ) - 5)
              / beta ((m : ℝ) + 1) ((m : ℝ) - 1))) := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have h2int :=
    integrable_unequalFD4InverseBetaMomentIntegrand
      (α := (m : ℝ) + 1) (β := (m : ℝ) - 1) (d := 2)
      (by linarith) (by linarith) (by linarith) (by linarith)
  have h4int :=
    integrable_unequalFD4InverseBetaMomentIntegrand
      (α := (m : ℝ) + 1) (β := (m : ℝ) - 1) (d := 4)
      (by linarith) (by linarith) (by linarith) (by linarith)
  change
    (∫ y, unequalFixedDifferenceFourQ m ^ 2
      * (unequalFixedDifferenceFourC m ^ 2
          * unequalFD4InverseBetaMomentIntegrand 2 y
        + unequalFixedDifferenceFourEll m
          * unequalFD4InverseBetaMomentIntegrand 4 y)
      ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1)) = _
  rw [integral_const_mul,
    integral_add
      (h2int.const_mul (unequalFixedDifferenceFourC m ^ 2))
      (h4int.const_mul (unequalFixedDifferenceFourEll m)),
    integral_const_mul, integral_const_mul,
    integral_unequalFD4InverseBetaMomentIntegrand
      (α := (m : ℝ) + 1) (β := (m : ℝ) - 1) (d := 2)
      (by linarith) (by linarith) (by linarith) (by linarith),
    integral_unequalFD4InverseBetaMomentIntegrand
      (α := (m : ℝ) + 1) (β := (m : ℝ) - 1) (d := 4)
      (by linarith) (by linarith) (by linarith) (by linarith)]
  congr 4 <;> ring

/--
The swapped-chart envelope expectation as the two shifted beta ratios.
The following beta-ratio module can simplify this expression directly to
`unequalFixedDifferenceFourMMinus m`.
-/
theorem integral_unequalFixedDifferenceFourEnvelopeFactor_minus_betaRatios
    {m : ℕ} (hm : 7 ≤ m) :
    (∫ y, unequalFixedDifferenceFourEnvelopeFactor m y
      ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
      =
    unequalFixedDifferenceFourQ m ^ 2
      * (unequalFixedDifferenceFourC m ^ 2
          * (beta ((m : ℝ) + 1) ((m : ℝ) - 1)
              / beta ((m : ℝ) - 1) ((m : ℝ) + 1))
        + unequalFixedDifferenceFourEll m
          * (beta ((m : ℝ) + 1) ((m : ℝ) - 3)
              / beta ((m : ℝ) - 1) ((m : ℝ) + 1))) := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have h2int :=
    integrable_unequalFD4InverseBetaMomentIntegrand
      (α := (m : ℝ) - 1) (β := (m : ℝ) + 1) (d := 2)
      (by linarith) (by linarith) (by linarith) (by linarith)
  have h4int :=
    integrable_unequalFD4InverseBetaMomentIntegrand
      (α := (m : ℝ) - 1) (β := (m : ℝ) + 1) (d := 4)
      (by linarith) (by linarith) (by linarith) (by linarith)
  change
    (∫ y, unequalFixedDifferenceFourQ m ^ 2
      * (unequalFixedDifferenceFourC m ^ 2
          * unequalFD4InverseBetaMomentIntegrand 2 y
        + unequalFixedDifferenceFourEll m
          * unequalFD4InverseBetaMomentIntegrand 4 y)
      ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1)) = _
  rw [integral_const_mul,
    integral_add
      (h2int.const_mul (unequalFixedDifferenceFourC m ^ 2))
      (h4int.const_mul (unequalFixedDifferenceFourEll m)),
    integral_const_mul, integral_const_mul,
    integral_unequalFD4InverseBetaMomentIntegrand
      (α := (m : ℝ) - 1) (β := (m : ℝ) + 1) (d := 2)
      (by linarith) (by linarith) (by linarith) (by linarith),
    integral_unequalFD4InverseBetaMomentIntegrand
      (α := (m : ℝ) - 1) (β := (m : ℝ) + 1) (d := 4)
      (by linarith) (by linarith) (by linarith) (by linarith)]
  congr 4 <;> ring

/-- Exact right-chart envelope expectation. -/
theorem integral_unequalFixedDifferenceFourEnvelopeFactor_plus
    {m : ℕ} (hm : 7 ≤ m) :
    (∫ y, unequalFixedDifferenceFourEnvelopeFactor m y
      ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1))
      = unequalFixedDifferenceFourMPlus m := by
  rw [integral_unequalFixedDifferenceFourEnvelopeFactor_plus_betaRatios hm]
  have hp3arg :
      (m : ℝ) + 3 = (m : ℝ) + 1 + 2 := by ring
  have hm3arg :
      (m : ℝ) - 3 = (m : ℝ) - 1 - 2 := by ring
  have hm5arg :
      (m : ℝ) - 5 = (m : ℝ) - 1 - 4 := by ring
  rw [hp3arg, hm3arg, hm5arg,
    unequalFixedDifferenceFourPlusBetaRatioTwo hm,
    unequalFixedDifferenceFourPlusBetaRatioFour hm]
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hm1 : (m : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hm2 : (m : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
  have hm3 : (m : ℝ) - 3 ≠ 0 := ne_of_gt (by linarith)
  have hm4 : (m : ℝ) - 4 ≠ 0 := ne_of_gt (by linarith)
  have hm5ne : (m : ℝ) - 5 ≠ 0 := ne_of_gt (by linarith)
  have h2m1 : 2 * (m : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2m1' : -1 + (m : ℝ) * 2 ≠ 0 := by linarith
  have h2m1'' : (m : ℝ) * 2 - 1 ≠ 0 := by linarith
  have hEllMoment :
      unequalFixedDifferenceFourEll m
          * ((((m : ℝ) + 1) * ((m : ℝ) + 2)
              * (2 * (m : ℝ) - 1) * (2 * (m : ℝ) - 2))
            / (((m : ℝ) - 2) * ((m : ℝ) - 3)
              * ((m : ℝ) - 4) * ((m : ℝ) - 5)))
        =
      (((m : ℝ) + 1) * ((m : ℝ) + 2)
          / (((m : ℝ) - 2) * ((m : ℝ) - 3)))
        * (60 * (m : ℝ) ^ 2
          / (((m : ℝ) - 4) * ((m : ℝ) - 5))) := by
    unfold unequalFixedDifferenceFourEll
    field_simp [hm1, hm2, hm3, hm4, hm5ne, h2m1, h2m1']
    ring
  rw [hEllMoment]
  unfold unequalFixedDifferenceFourMPlus
  ring

/-- Exact sample-swapped envelope expectation. -/
theorem integral_unequalFixedDifferenceFourEnvelopeFactor_minus
    {m : ℕ} (hm : 7 ≤ m) :
    (∫ y, unequalFixedDifferenceFourEnvelopeFactor m y
      ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
      = unequalFixedDifferenceFourMMinus m := by
  rw [integral_unequalFixedDifferenceFourEnvelopeFactor_minus_betaRatios hm]
  have hratio2 :
      beta ((m : ℝ) + 1) ((m : ℝ) - 1)
          / beta ((m : ℝ) - 1) ((m : ℝ) + 1)
        = 1 := by
    convert unequalFixedDifferenceFourMinusBetaRatioTwo hm using 1 <;> ring
  have hratio4 :
      beta ((m : ℝ) + 1) ((m : ℝ) - 3)
          / beta ((m : ℝ) - 1) ((m : ℝ) + 1)
        =
      ((2 * (m : ℝ) - 1) * (2 * (m : ℝ) - 2))
        / (((m : ℝ) - 2) * ((m : ℝ) - 3)) := by
    convert unequalFixedDifferenceFourMinusBetaRatioFour hm using 1 <;> ring
  rw [hratio2, hratio4]
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hm1ne : (m : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hm2 : (m : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
  have hm3 : (m : ℝ) - 3 ≠ 0 := ne_of_gt (by linarith)
  have h2m1 : 2 * (m : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2m1' : -1 + (m : ℝ) * 2 ≠ 0 := by linarith
  have h2m1'' : (m : ℝ) * 2 - 1 ≠ 0 := by linarith
  have hEllMoment :
      unequalFixedDifferenceFourEll m
          * (((2 * (m : ℝ) - 1) * (2 * (m : ℝ) - 2))
            / (((m : ℝ) - 2) * ((m : ℝ) - 3)))
        =
      60 * (m : ℝ) ^ 2
        / (((m : ℝ) - 2) * ((m : ℝ) - 3)) := by
    unfold unequalFixedDifferenceFourEll
    field_simp [hm1ne, hm2, hm3, h2m1, h2m1']
    ring
  rw [hEllMoment]
  unfold unequalFixedDifferenceFourMMinus
  ring

/-! ## Integrating the two pointwise `C` bounds -/

/-- The quadratic-kernel leading coefficient strictly dominates its square
linear coefficient throughout the family. -/
theorem unequalFixedDifferenceFourK_sq_lt_Ell
    {m : ℕ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourK m ^ 2
      < unequalFixedDifferenceFourEll m := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith
  have h2m1 : 0 < 2 * (m : ℝ) - 1 := by linarith
  have hm1 : 0 < (m : ℝ) - 1 := by linarith
  unfold unequalFixedDifferenceFourK unequalFixedDifferenceFourEll
  rw [div_pow]
  rw [div_lt_div_iff₀ (sq_pos_of_pos h2m1) (mul_pos hm1 h2m1)]
  have hpos :
      0 <
        6 * (m : ℝ) ^ 2
          * (2 * (m : ℝ) - 1) * (4 * (m : ℝ) + 1) := by
    positivity
  nlinarith

/-- The family quadratic kernel is everywhere nonnegative. -/
theorem unequalFixedDifferenceFourCKernel_nonneg
    {m : ℕ} (hm : 7 ≤ m) (u : ℝ) :
    0 ≤ unequalFixedDifferenceFourCKernel m u := by
  have hEll := unequalFixedDifferenceFourEll_pos hm
  have hgap := (unequalFixedDifferenceFourK_sq_lt_Ell hm).le
  have hid :
      unequalFixedDifferenceFourEll m
          * unequalFixedDifferenceFourCKernel m u
        =
      (unequalFixedDifferenceFourEll m * u
          - unequalFixedDifferenceFourK m
            * unequalFixedDifferenceFourC m) ^ 2
        + unequalFixedDifferenceFourC m ^ 2
          * (unequalFixedDifferenceFourEll m
            - unequalFixedDifferenceFourK m ^ 2) := by
    unfold unequalFixedDifferenceFourCKernel
    ring
  have hrhs :
      0 ≤
      (unequalFixedDifferenceFourEll m * u
          - unequalFixedDifferenceFourK m
            * unequalFixedDifferenceFourC m) ^ 2
        + unequalFixedDifferenceFourC m ^ 2
          * (unequalFixedDifferenceFourEll m
            - unequalFixedDifferenceFourK m ^ 2) :=
    add_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hgap))
  nlinarith

/-- The right-chart reduced quadratic integrand. -/
def unequalFixedDifferenceFourPlusCIntegrand
    (m : ℕ) (s y : ℝ) : ℝ :=
  unequalDampedPhi
      (unequalFixedDifferenceFourT m)
      (unequalFixedDifferenceFourKappa m)
      (unequalDampedR s y) ^ 2
    * unequalFixedDifferenceFourCKernel m
        (unequalDampedU (unequalFixedDifferenceFourQ m) s y)

/-- The sample-swapped reduced quadratic integrand. -/
def unequalFixedDifferenceFourMinusCIntegrand
    (m : ℕ) (s y : ℝ) : ℝ :=
  unequalDampedPhi
      (unequalFixedDifferenceFourQ m)
      (-unequalFixedDifferenceFourKappa m)
      (unequalDampedR s y) ^ 2
    * unequalFixedDifferenceFourCKernel m
        (unequalDampedU (unequalFixedDifferenceFourT m) s y)

theorem measurable_unequalFixedDifferenceFourPlusCIntegrand
    (m : ℕ) (s : ℝ) :
    Measurable (unequalFixedDifferenceFourPlusCIntegrand m s) := by
  unfold unequalFixedDifferenceFourPlusCIntegrand
    unequalFixedDifferenceFourCKernel unequalDampedPhi
    unequalDampedInner unequalDampedR unequalDampedU unequalDampedDenom
  fun_prop

theorem measurable_unequalFixedDifferenceFourMinusCIntegrand
    (m : ℕ) (s : ℝ) :
    Measurable (unequalFixedDifferenceFourMinusCIntegrand m s) := by
  unfold unequalFixedDifferenceFourMinusCIntegrand
    unequalFixedDifferenceFourCKernel unequalDampedPhi
    unequalDampedInner unequalDampedR unequalDampedU unequalDampedDenom
  fun_prop

theorem unequalFixedDifferenceFourPlusCIntegrand_nonneg
    {m : ℕ} (hm : 7 ≤ m) (s y : ℝ) :
    0 ≤ unequalFixedDifferenceFourPlusCIntegrand m s y := by
  exact mul_nonneg (sq_nonneg _)
    (unequalFixedDifferenceFourCKernel_nonneg hm _)

theorem unequalFixedDifferenceFourMinusCIntegrand_nonneg
    {m : ℕ} (hm : 7 ≤ m) (s y : ℝ) :
    0 ≤ unequalFixedDifferenceFourMinusCIntegrand m s y := by
  exact mul_nonneg (sq_nonneg _)
    (unequalFixedDifferenceFourCKernel_nonneg hm _)

theorem integrable_unequalFixedDifferenceFourPlusCIntegrand
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Integrable (unequalFixedDifferenceFourPlusCIntegrand m s)
      (betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1)) := by
  have henv :=
    (integrable_unequalFixedDifferenceFourEnvelopeFactor_plus hm).const_mul
      ((1 - s) ^ 2)
  apply henv.mono_nonneg
    (measurable_unequalFixedDifferenceFourPlusCIntegrand m s).aestronglyMeasurable
  · exact ae_of_all _ (unequalFixedDifferenceFourPlusCIntegrand_nonneg hm s)
  · filter_upwards [betaMeasure_unequalFD4_ae_mem_Ioo] with y hy
    have hpoint :=
      unequalFixedDifferenceFourC_pointwise_le_envelope
        hm hs0 hs1 hy.1.le hy.2
    rw [unequalFixedDifferenceFourEnvelopeFactor_eq m hy.1 hy.2]
    simpa only [unequalFixedDifferenceFourPlusCIntegrand, mul_assoc] using hpoint

theorem integrable_unequalFixedDifferenceFourMinusCIntegrand
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Integrable (unequalFixedDifferenceFourMinusCIntegrand m s)
      (betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1)) := by
  have henv :=
    (integrable_unequalFixedDifferenceFourEnvelopeFactor_minus hm).const_mul
      ((1 - s) ^ 2)
  apply henv.mono_nonneg
    (measurable_unequalFixedDifferenceFourMinusCIntegrand m s).aestronglyMeasurable
  · exact ae_of_all _ (unequalFixedDifferenceFourMinusCIntegrand_nonneg hm s)
  · filter_upwards [betaMeasure_unequalFD4_ae_mem_Ioo] with y hy
    have hpoint :=
      unequalFixedDifferenceFourSwappedC_pointwise_le_envelope
        hm hs0 hs1 hy.1.le hy.2
    rw [unequalFixedDifferenceFourEnvelopeFactor_eq m hy.1 hy.2]
    simpa only [unequalFixedDifferenceFourMinusCIntegrand, mul_assoc] using hpoint

/--
Integrated right-chart pointwise comparison, isolated from the final
closed-form beta-ratio simplification.
-/
theorem integral_unequalFixedDifferenceFourPlusC_le_envelopeIntegral
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ y, unequalFixedDifferenceFourPlusCIntegrand m s y
      ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1))
      ≤
    (1 - s) ^ 2
      * ∫ y, unequalFixedDifferenceFourEnvelopeFactor m y
        ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1) := by
  have hraw :=
    integrable_unequalFixedDifferenceFourPlusCIntegrand hm hs0 hs1
  have henv :=
    (integrable_unequalFixedDifferenceFourEnvelopeFactor_plus hm).const_mul
      ((1 - s) ^ 2)
  calc
    (∫ y, unequalFixedDifferenceFourPlusCIntegrand m s y
      ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1))
        ≤
      ∫ y, (1 - s) ^ 2
        * unequalFixedDifferenceFourEnvelopeFactor m y
        ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1) := by
          apply integral_mono_ae hraw henv
          filter_upwards [betaMeasure_unequalFD4_ae_mem_Ioo] with y hy
          have hpoint :=
            unequalFixedDifferenceFourC_pointwise_le_envelope
              hm hs0 hs1 hy.1.le hy.2
          rw [unequalFixedDifferenceFourEnvelopeFactor_eq m hy.1 hy.2]
          simpa only [unequalFixedDifferenceFourPlusCIntegrand, mul_assoc] using hpoint
    _ =
      (1 - s) ^ 2
        * ∫ y, unequalFixedDifferenceFourEnvelopeFactor m y
          ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1) := by
            rw [integral_const_mul]

/--
Integrated swapped-chart pointwise comparison, isolated from the final
closed-form beta-ratio simplification.
-/
theorem integral_unequalFixedDifferenceFourMinusC_le_envelopeIntegral
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ y, unequalFixedDifferenceFourMinusCIntegrand m s y
      ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
      ≤
    (1 - s) ^ 2
      * ∫ y, unequalFixedDifferenceFourEnvelopeFactor m y
        ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1) := by
  have hraw :=
    integrable_unequalFixedDifferenceFourMinusCIntegrand hm hs0 hs1
  have henv :=
    (integrable_unequalFixedDifferenceFourEnvelopeFactor_minus hm).const_mul
      ((1 - s) ^ 2)
  calc
    (∫ y, unequalFixedDifferenceFourMinusCIntegrand m s y
      ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
        ≤
      ∫ y, (1 - s) ^ 2
        * unequalFixedDifferenceFourEnvelopeFactor m y
        ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1) := by
          apply integral_mono_ae hraw henv
          filter_upwards [betaMeasure_unequalFD4_ae_mem_Ioo] with y hy
          have hpoint :=
            unequalFixedDifferenceFourSwappedC_pointwise_le_envelope
              hm hs0 hs1 hy.1.le hy.2
          rw [unequalFixedDifferenceFourEnvelopeFactor_eq m hy.1 hy.2]
          simpa only [unequalFixedDifferenceFourMinusCIntegrand, mul_assoc] using hpoint
    _ =
      (1 - s) ^ 2
        * ∫ y, unequalFixedDifferenceFourEnvelopeFactor m y
          ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1) := by
            rw [integral_const_mul]

/--
The right-chart quadratic coefficient is bounded by the exact family
constant `M₊`.
-/
theorem integral_unequalFixedDifferenceFourPlusC_le
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ y, unequalFixedDifferenceFourPlusCIntegrand m s y
      ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1))
      ≤ unequalFixedDifferenceFourMPlus m * (1 - s) ^ 2 := by
  calc
    (∫ y, unequalFixedDifferenceFourPlusCIntegrand m s y
      ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1))
        ≤
      (1 - s) ^ 2
        * ∫ y, unequalFixedDifferenceFourEnvelopeFactor m y
          ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1) :=
      integral_unequalFixedDifferenceFourPlusC_le_envelopeIntegral
        hm hs0 hs1
    _ = unequalFixedDifferenceFourMPlus m * (1 - s) ^ 2 := by
      rw [integral_unequalFixedDifferenceFourEnvelopeFactor_plus hm]
      ring

/--
The swapped-chart quadratic coefficient first has its sharper exact
constant `M₋`.
-/
theorem integral_unequalFixedDifferenceFourMinusC_le_MMinus
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ y, unequalFixedDifferenceFourMinusCIntegrand m s y
      ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
      ≤ unequalFixedDifferenceFourMMinus m * (1 - s) ^ 2 := by
  calc
    (∫ y, unequalFixedDifferenceFourMinusCIntegrand m s y
      ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
        ≤
      (1 - s) ^ 2
        * ∫ y, unequalFixedDifferenceFourEnvelopeFactor m y
          ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1) :=
      integral_unequalFixedDifferenceFourMinusC_le_envelopeIntegral
        hm hs0 hs1
    _ = unequalFixedDifferenceFourMMinus m * (1 - s) ^ 2 := by
      rw [integral_unequalFixedDifferenceFourEnvelopeFactor_minus hm]
      ring

/-- The common right-chart constant `M₊` also bounds the swapped chart. -/
theorem integral_unequalFixedDifferenceFourMinusC_le
    {m : ℕ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ y, unequalFixedDifferenceFourMinusCIntegrand m s y
      ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
      ≤ unequalFixedDifferenceFourMPlus m * (1 - s) ^ 2 := by
  calc
    (∫ y, unequalFixedDifferenceFourMinusCIntegrand m s y
      ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
        ≤ unequalFixedDifferenceFourMMinus m * (1 - s) ^ 2 :=
      integral_unequalFixedDifferenceFourMinusC_le_MMinus hm hs0 hs1
    _ ≤ unequalFixedDifferenceFourMPlus m * (1 - s) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (unequalFixedDifferenceFourMMinus_lt_MPlus hm).le
        (sq_nonneg (1 - s))

end

end GraybillDeal
