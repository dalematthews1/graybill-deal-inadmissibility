import GraybillDeal.UnequalFixedDifferenceFourEnvelopeIntegrals
import GraybillDeal.UnequalFixedDifferenceFourRealCoordinates
import GraybillDeal.UnequalFixedDifferenceFourRealMoments

/-!
# Real-parameter quadratic envelope integrals

This is the real-parameter companion to
`UnequalFixedDifferenceFourEnvelopeIntegrals`.  It integrates the two
pointwise quadratic envelopes from
`UnequalFixedDifferenceFourRealCoordinates` against the beta laws with
shapes `(m+1,m-1)` and `(m-1,m+1)`, for every real `m ≥ 7`.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- The common real-parameter quadratic envelope. -/
def unequalFixedDifferenceFourRealEnvelopeFactor (m y : ℝ) : ℝ :=
  unequalFixedDifferenceFourRealQ m ^ 2
    * (unequalFixedDifferenceFourRealC m ^ 2
        * unequalFD4InverseBetaMomentIntegrand 2 y
      + unequalFixedDifferenceFourRealEll m
        * unequalFD4InverseBetaMomentIntegrand 4 y)

/-- Product form of the real-parameter envelope on the open beta support. -/
theorem unequalFixedDifferenceFourRealEnvelopeFactor_eq
    (m : ℝ) {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    unequalFixedDifferenceFourRealEnvelopeFactor m y
      =
    unequalFixedDifferenceFourRealQ m ^ 2
      * (y ^ 2 / (1 - y) ^ 2)
      * (unequalFixedDifferenceFourRealC m ^ 2
        + unequalFixedDifferenceFourRealEll m / (1 - y) ^ 2) := by
  have hy : 1 - y ≠ 0 := ne_of_gt (sub_pos.mpr hy1)
  unfold unequalFixedDifferenceFourRealEnvelopeFactor
    unequalFD4InverseBetaMomentIntegrand
  rw [Real.rpow_two, Real.rpow_two]
  rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
  field_simp [hy]

private theorem betaMeasure_unequalFD4Real_ae_mem_Ioo
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

/-! ## Swapped-chart pointwise bounds -/

theorem abs_unequalFixedDifferenceFourRealSwappedInner_le_Q
    {m : ℝ} (hm : 7 ≤ m) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) :
    |unequalDampedInner
        (unequalFixedDifferenceFourRealQ m)
        (-unequalFixedDifferenceFourRealKappa m) r|
      ≤ unequalFixedDifferenceFourRealQ m := by
  have hr' : 1 - r ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hr.1, hr.2]
  have h :=
    abs_unequalFixedDifferenceFourRealInner_le_Q hm hr'
  have heq :
      unequalDampedInner
          (unequalFixedDifferenceFourRealQ m)
          (-unequalFixedDifferenceFourRealKappa m) r
        =
      -unequalDampedInner
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealKappa m) (1 - r) := by
    have htq := unequalFixedDifferenceFourRealT_add_Q hm
    unfold unequalDampedInner
    rw [show unequalFixedDifferenceFourRealQ m
        = 1 - unequalFixedDifferenceFourRealT m by linarith]
    ring
  rw [heq, abs_neg]
  exact h

theorem unequalFixedDifferenceFourRealSwappedPhi_sq_le_envelope
    {m : ℝ} (hm : 7 ≤ m)
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    unequalDampedPhi
        (unequalFixedDifferenceFourRealQ m)
        (-unequalFixedDifferenceFourRealKappa m)
        (unequalDampedR s y) ^ 2
      ≤
    (1 - s) ^ 2 * unequalFixedDifferenceFourRealQ m ^ 2
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
    abs_unequalFixedDifferenceFourRealSwappedInner_le_Q hm hr
  have hinner_sq :
      unequalDampedInner
          (unequalFixedDifferenceFourRealQ m)
          (-unequalFixedDifferenceFourRealKappa m)
          (unequalDampedR s y) ^ 2
        ≤ unequalFixedDifferenceFourRealQ m ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_pos (unequalFixedDifferenceFourRealQ_pos hm)] using hinner
  rw [unequalDampedPhi]
  calc
    (unequalDampedR s y * (1 - unequalDampedR s y)
        * unequalDampedInner
          (unequalFixedDifferenceFourRealQ m)
          (-unequalFixedDifferenceFourRealKappa m)
          (unequalDampedR s y)) ^ 2
        =
      (unequalDampedR s y * (1 - unequalDampedR s y)) ^ 2
        * unequalDampedInner
          (unequalFixedDifferenceFourRealQ m)
          (-unequalFixedDifferenceFourRealKappa m)
          (unequalDampedR s y) ^ 2 := by
            ring
    _ ≤
      ((1 - s) * y / (1 - y)) ^ 2
        * unequalFixedDifferenceFourRealQ m ^ 2 :=
      mul_le_mul hrprod_sq hinner_sq
        (sq_nonneg _) (sq_nonneg _)
    _ =
      (1 - s) ^ 2 * unequalFixedDifferenceFourRealQ m ^ 2
        * (y ^ 2 / (1 - y) ^ 2) := by
          field_simp [ne_of_gt (sub_pos.mpr hy1)]

theorem unequalFixedDifferenceFourRealSwappedC_pointwise_le_envelope
    {m : ℝ} (hm : 7 ≤ m)
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    unequalDampedPhi
        (unequalFixedDifferenceFourRealQ m)
        (-unequalFixedDifferenceFourRealKappa m)
        (unequalDampedR s y) ^ 2
      * unequalFixedDifferenceFourRealCKernel m
          (unequalDampedU
            (unequalFixedDifferenceFourRealT m) s y)
      ≤
    (1 - s) ^ 2 * unequalFixedDifferenceFourRealQ m ^ 2
      * (y ^ 2 / (1 - y) ^ 2)
      * (unequalFixedDifferenceFourRealC m ^ 2
        + unequalFixedDifferenceFourRealEll m / (1 - y) ^ 2) := by
  have ht0 := (unequalFixedDifferenceFourRealT_pos hm).le
  have ht1 := unequalFixedDifferenceFourRealT_le_one hm
  have hu :=
    unequalDampedU_pos ht0 ht1 hs0 hs1 hy0 hy1.le
  have hu_sq :=
    unequalDampedU_sq_le ht0 ht1 hs0 hs1 hy0 hy1
  have hk :=
    unequalFixedDifferenceFourRealCKernel_le hm hu.le
  have hEll := (unequalFixedDifferenceFourRealEll_pos hm).le
  have hy : 0 < 1 - y := sub_pos.mpr hy1
  have hk' :
      unequalFixedDifferenceFourRealC m ^ 2
          + unequalFixedDifferenceFourRealEll m
            * unequalDampedU
                (unequalFixedDifferenceFourRealT m) s y ^ 2
        ≤ unequalFixedDifferenceFourRealC m ^ 2
          + unequalFixedDifferenceFourRealEll m / (1 - y) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hu_sq hEll
    have heq :
        unequalFixedDifferenceFourRealEll m * (1 / (1 - y)) ^ 2
          = unequalFixedDifferenceFourRealEll m / (1 - y) ^ 2 := by
      field_simp [ne_of_gt hy]
    rw [← heq]
    linarith
  have hphi :=
    unequalFixedDifferenceFourRealSwappedPhi_sq_le_envelope
      hm hs0 hs1 hy0 hy1
  have hupper0 :
      0 ≤ unequalFixedDifferenceFourRealC m ^ 2
        + unequalFixedDifferenceFourRealEll m / (1 - y) ^ 2 := by
    positivity
  calc
    unequalDampedPhi
          (unequalFixedDifferenceFourRealQ m)
          (-unequalFixedDifferenceFourRealKappa m)
          (unequalDampedR s y) ^ 2
        * unequalFixedDifferenceFourRealCKernel m
            (unequalDampedU
              (unequalFixedDifferenceFourRealT m) s y)
        ≤
      unequalDampedPhi
          (unequalFixedDifferenceFourRealQ m)
          (-unequalFixedDifferenceFourRealKappa m)
          (unequalDampedR s y) ^ 2
        * (unequalFixedDifferenceFourRealC m ^ 2
          + unequalFixedDifferenceFourRealEll m
            * unequalDampedU
                (unequalFixedDifferenceFourRealT m) s y ^ 2) :=
      mul_le_mul_of_nonneg_left hk (sq_nonneg _)
    _ ≤
      unequalDampedPhi
          (unequalFixedDifferenceFourRealQ m)
          (-unequalFixedDifferenceFourRealKappa m)
          (unequalDampedR s y) ^ 2
        * (unequalFixedDifferenceFourRealC m ^ 2
          + unequalFixedDifferenceFourRealEll m / (1 - y) ^ 2) :=
      mul_le_mul_of_nonneg_left hk' (sq_nonneg _)
    _ ≤
      ((1 - s) ^ 2 * unequalFixedDifferenceFourRealQ m ^ 2
        * (y ^ 2 / (1 - y) ^ 2))
        * (unequalFixedDifferenceFourRealC m ^ 2
          + unequalFixedDifferenceFourRealEll m / (1 - y) ^ 2) :=
      mul_le_mul_of_nonneg_right hphi hupper0

/-! ## Real-parameter beta ratios -/

private theorem unequalFixedDifferenceFourRealPlusBetaRatioTwo
    {m : ℝ} (hm : 7 ≤ m) :
    beta (m + 1 + 2) (m - 1 - 2)
        / beta (m + 1) (m - 1)
      =
    ((m + 1) * (m + 2)) / ((m - 2) * (m - 3)) := by
  have hbase : beta (m + 1) (m - 3) ≠ 0 :=
    (beta_pos (by linarith) (by linarith)).ne'
  have hleft1 :=
    beta_add_one_left
      (a := m + 1) (b := m - 3) (by linarith) (by linarith)
  have hleft2 :=
    beta_add_one_left
      (a := m + 2) (b := m - 3) (by linarith) (by linarith)
  have hright1 :=
    beta_add_one_right
      (a := m + 1) (b := m - 3) (by linarith) (by linarith)
  have hright2 :=
    beta_add_one_right
      (a := m + 1) (b := m - 2) (by linarith) (by linarith)
  have hm2 : m - 2 ≠ 0 := ne_of_gt (by linarith)
  have hm3 : m - 3 ≠ 0 := ne_of_gt (by linarith)
  have h2m1 : 2 * m - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2m2 : 2 * m - 2 ≠ 0 := ne_of_gt (by linarith)
  have hprod12 : 2 - m * 6 + m ^ 2 * 4 ≠ 0 := by
    rw [show 2 - m * 6 + m ^ 2 * 4
      = (2 * m - 1) * (2 * m - 2) by ring]
    exact mul_ne_zero h2m1 h2m2
  rw [show m + 1 + 2 = (m + 2) + 1 by ring,
    show m - 1 - 2 = m - 3 by ring,
    hleft2,
    show beta (m + 2) (m - 3)
        = beta ((m + 1) + 1) (m - 3) by ring,
    hleft1,
    show m - 1 = (m - 2) + 1 by ring,
    hright2,
    show beta (m + 1) (m - 2)
        = beta (m + 1) ((m - 3) + 1) by ring,
    hright1]
  field_simp [hbase, hm2, hm3, h2m1, h2m2, hprod12]
  apply (div_eq_iff (mul_ne_zero (by linarith) (by linarith))).2
  ring

private theorem unequalFixedDifferenceFourRealPlusBetaRatioFour
    {m : ℝ} (hm : 7 ≤ m) :
    beta (m + 1 + 2) (m - 1 - 4)
        / beta (m + 1) (m - 1)
      =
    ((m + 1) * (m + 2) * (2 * m - 1) * (2 * m - 2))
      / ((m - 2) * (m - 3) * (m - 4) * (m - 5)) := by
  have hbase : beta (m + 1) (m - 5) ≠ 0 :=
    (beta_pos (by linarith) (by linarith)).ne'
  have hl1 :=
    beta_add_one_left
      (a := m + 1) (b := m - 5) (by linarith) (by linarith)
  have hl2 :=
    beta_add_one_left
      (a := m + 2) (b := m - 5) (by linarith) (by linarith)
  have hr1 :=
    beta_add_one_right
      (a := m + 1) (b := m - 5) (by linarith) (by linarith)
  have hr2 :=
    beta_add_one_right
      (a := m + 1) (b := m - 4) (by linarith) (by linarith)
  have hr3 :=
    beta_add_one_right
      (a := m + 1) (b := m - 3) (by linarith) (by linarith)
  have hr4 :=
    beta_add_one_right
      (a := m + 1) (b := m - 2) (by linarith) (by linarith)
  have hm2 : m - 2 ≠ 0 := ne_of_gt (by linarith)
  have hm3 : m - 3 ≠ 0 := ne_of_gt (by linarith)
  have hm4 : m - 4 ≠ 0 := ne_of_gt (by linarith)
  have hm5 : m - 5 ≠ 0 := ne_of_gt (by linarith)
  have h2m1 : 2 * m - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2m2 : 2 * m - 2 ≠ 0 := ne_of_gt (by linarith)
  have h2m3 : 2 * m - 3 ≠ 0 := ne_of_gt (by linarith)
  have h2m4 : 2 * m - 4 ≠ 0 := ne_of_gt (by linarith)
  have hprod12 : 2 - m * 6 + m ^ 2 * 4 ≠ 0 := by
    rw [show 2 - m * 6 + m ^ 2 * 4
      = (2 * m - 1) * (2 * m - 2) by ring]
    exact mul_ne_zero h2m1 h2m2
  have hprod34 : 12 - m * 14 + m ^ 2 * 4 ≠ 0 := by
    rw [show 12 - m * 14 + m ^ 2 * 4
      = (2 * m - 3) * (2 * m - 4) by ring]
    exact mul_ne_zero h2m3 h2m4
  rw [show m + 1 + 2 = (m + 2) + 1 by ring,
    show m - 1 - 4 = m - 5 by ring,
    hl2,
    show beta (m + 2) (m - 5)
        = beta ((m + 1) + 1) (m - 5) by ring,
    hl1,
    show m - 1 = (m - 2) + 1 by ring,
    hr4,
    show beta (m + 1) (m - 2)
        = beta (m + 1) ((m - 3) + 1) by ring,
    hr3,
    show beta (m + 1) (m - 3)
        = beta (m + 1) ((m - 4) + 1) by ring,
    hr2,
    show beta (m + 1) (m - 4)
        = beta (m + 1) ((m - 5) + 1) by ring,
    hr1]
  field_simp [hbase, hm2, hm3, hm4, hm5,
    h2m1, h2m2, h2m3, h2m4, hprod12, hprod34]
  apply (div_eq_iff (mul_ne_zero (by linarith) (by linarith))).2
  ring

private theorem unequalFixedDifferenceFourRealMinusBetaRatioTwo
    {m : ℝ} (hm : 7 ≤ m) :
    beta (m - 1 + 2) (m + 1 - 2)
        / beta (m - 1) (m + 1)
      = 1 := by
  have hbeta : beta (m - 1) (m + 1) ≠ 0 :=
    (beta_pos (by linarith) (by linarith)).ne'
  rw [show m - 1 + 2 = m + 1 by ring,
    show m + 1 - 2 = m - 1 by ring,
    beta_symm_real (m + 1) (m - 1)]
  exact div_self hbeta

private theorem unequalFixedDifferenceFourRealMinusBetaRatioFour
    {m : ℝ} (hm : 7 ≤ m) :
    beta (m - 1 + 2) (m + 1 - 4)
        / beta (m - 1) (m + 1)
      =
    ((2 * m - 1) * (2 * m - 2))
      / ((m - 2) * (m - 3)) := by
  have hbase : beta (m + 1) (m - 3) ≠ 0 :=
    (beta_pos (by linarith) (by linarith)).ne'
  have hr1 :=
    beta_add_one_right
      (a := m + 1) (b := m - 3) (by linarith) (by linarith)
  have hr2 :=
    beta_add_one_right
      (a := m + 1) (b := m - 2) (by linarith) (by linarith)
  have hm2 : m - 2 ≠ 0 := ne_of_gt (by linarith)
  have hm3 : m - 3 ≠ 0 := ne_of_gt (by linarith)
  have h2m1 : 2 * m - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2m2 : 2 * m - 2 ≠ 0 := ne_of_gt (by linarith)
  have hprod12 : 2 - m * 6 + m ^ 2 * 4 ≠ 0 := by
    rw [show 2 - m * 6 + m ^ 2 * 4
      = (2 * m - 1) * (2 * m - 2) by ring]
    exact mul_ne_zero h2m1 h2m2
  rw [show m - 1 + 2 = m + 1 by ring,
    show m + 1 - 4 = m - 3 by ring,
    beta_symm_real (m - 1) (m + 1),
    show m - 1 = (m - 2) + 1 by ring,
    hr2,
    show beta (m + 1) (m - 2)
        = beta (m + 1) ((m - 3) + 1) by ring,
    hr1]
  field_simp [hbase, hm2, hm3, h2m1, h2m2, hprod12]
  ring

/-! ## Exact envelope expectations -/

theorem integrable_unequalFixedDifferenceFourRealEnvelopeFactor_plus
    {m : ℝ} (hm : 7 ≤ m) :
    Integrable (unequalFixedDifferenceFourRealEnvelopeFactor m)
      (betaMeasure (m + 1) (m - 1)) := by
  have h2 :=
    integrable_unequalFD4InverseBetaMomentIntegrand
      (α := m + 1) (β := m - 1) (d := 2)
      (by linarith) (by linarith) (by linarith) (by linarith)
  have h4 :=
    integrable_unequalFD4InverseBetaMomentIntegrand
      (α := m + 1) (β := m - 1) (d := 4)
      (by linarith) (by linarith) (by linarith) (by linarith)
  change Integrable
    (fun y => unequalFixedDifferenceFourRealQ m ^ 2
      * (unequalFixedDifferenceFourRealC m ^ 2
          * unequalFD4InverseBetaMomentIntegrand 2 y
        + unequalFixedDifferenceFourRealEll m
          * unequalFD4InverseBetaMomentIntegrand 4 y))
    (betaMeasure (m + 1) (m - 1))
  simpa only [Pi.add_apply] using
    ((h2.const_mul (unequalFixedDifferenceFourRealC m ^ 2)).add
      (h4.const_mul (unequalFixedDifferenceFourRealEll m))).const_mul
        (unequalFixedDifferenceFourRealQ m ^ 2)

theorem integrable_unequalFixedDifferenceFourRealEnvelopeFactor_minus
    {m : ℝ} (hm : 7 ≤ m) :
    Integrable (unequalFixedDifferenceFourRealEnvelopeFactor m)
      (betaMeasure (m - 1) (m + 1)) := by
  have h2 :=
    integrable_unequalFD4InverseBetaMomentIntegrand
      (α := m - 1) (β := m + 1) (d := 2)
      (by linarith) (by linarith) (by linarith) (by linarith)
  have h4 :=
    integrable_unequalFD4InverseBetaMomentIntegrand
      (α := m - 1) (β := m + 1) (d := 4)
      (by linarith) (by linarith) (by linarith) (by linarith)
  change Integrable
    (fun y => unequalFixedDifferenceFourRealQ m ^ 2
      * (unequalFixedDifferenceFourRealC m ^ 2
          * unequalFD4InverseBetaMomentIntegrand 2 y
        + unequalFixedDifferenceFourRealEll m
          * unequalFD4InverseBetaMomentIntegrand 4 y))
    (betaMeasure (m - 1) (m + 1))
  simpa only [Pi.add_apply] using
    ((h2.const_mul (unequalFixedDifferenceFourRealC m ^ 2)).add
      (h4.const_mul (unequalFixedDifferenceFourRealEll m))).const_mul
        (unequalFixedDifferenceFourRealQ m ^ 2)

theorem integral_unequalFixedDifferenceFourRealEnvelopeFactor_plus_betaRatios
    {m : ℝ} (hm : 7 ≤ m) :
    (∫ y, unequalFixedDifferenceFourRealEnvelopeFactor m y
      ∂betaMeasure (m + 1) (m - 1))
      =
    unequalFixedDifferenceFourRealQ m ^ 2
      * (unequalFixedDifferenceFourRealC m ^ 2
          * (beta (m + 3) (m - 3) / beta (m + 1) (m - 1))
        + unequalFixedDifferenceFourRealEll m
          * (beta (m + 3) (m - 5)
              / beta (m + 1) (m - 1))) := by
  have h2int :=
    integrable_unequalFD4InverseBetaMomentIntegrand
      (α := m + 1) (β := m - 1) (d := 2)
      (by linarith) (by linarith) (by linarith) (by linarith)
  have h4int :=
    integrable_unequalFD4InverseBetaMomentIntegrand
      (α := m + 1) (β := m - 1) (d := 4)
      (by linarith) (by linarith) (by linarith) (by linarith)
  change
    (∫ y, unequalFixedDifferenceFourRealQ m ^ 2
      * (unequalFixedDifferenceFourRealC m ^ 2
          * unequalFD4InverseBetaMomentIntegrand 2 y
        + unequalFixedDifferenceFourRealEll m
          * unequalFD4InverseBetaMomentIntegrand 4 y)
      ∂betaMeasure (m + 1) (m - 1)) = _
  rw [integral_const_mul,
    integral_add
      (h2int.const_mul (unequalFixedDifferenceFourRealC m ^ 2))
      (h4int.const_mul (unequalFixedDifferenceFourRealEll m)),
    integral_const_mul, integral_const_mul,
    integral_unequalFD4InverseBetaMomentIntegrand
      (α := m + 1) (β := m - 1) (d := 2)
      (by linarith) (by linarith) (by linarith) (by linarith),
    integral_unequalFD4InverseBetaMomentIntegrand
      (α := m + 1) (β := m - 1) (d := 4)
      (by linarith) (by linarith) (by linarith) (by linarith)]
  congr 4 <;> ring

theorem integral_unequalFixedDifferenceFourRealEnvelopeFactor_minus_betaRatios
    {m : ℝ} (hm : 7 ≤ m) :
    (∫ y, unequalFixedDifferenceFourRealEnvelopeFactor m y
      ∂betaMeasure (m - 1) (m + 1))
      =
    unequalFixedDifferenceFourRealQ m ^ 2
      * (unequalFixedDifferenceFourRealC m ^ 2
          * (beta (m + 1) (m - 1) / beta (m - 1) (m + 1))
        + unequalFixedDifferenceFourRealEll m
          * (beta (m + 1) (m - 3)
              / beta (m - 1) (m + 1))) := by
  have h2int :=
    integrable_unequalFD4InverseBetaMomentIntegrand
      (α := m - 1) (β := m + 1) (d := 2)
      (by linarith) (by linarith) (by linarith) (by linarith)
  have h4int :=
    integrable_unequalFD4InverseBetaMomentIntegrand
      (α := m - 1) (β := m + 1) (d := 4)
      (by linarith) (by linarith) (by linarith) (by linarith)
  change
    (∫ y, unequalFixedDifferenceFourRealQ m ^ 2
      * (unequalFixedDifferenceFourRealC m ^ 2
          * unequalFD4InverseBetaMomentIntegrand 2 y
        + unequalFixedDifferenceFourRealEll m
          * unequalFD4InverseBetaMomentIntegrand 4 y)
      ∂betaMeasure (m - 1) (m + 1)) = _
  rw [integral_const_mul,
    integral_add
      (h2int.const_mul (unequalFixedDifferenceFourRealC m ^ 2))
      (h4int.const_mul (unequalFixedDifferenceFourRealEll m)),
    integral_const_mul, integral_const_mul,
    integral_unequalFD4InverseBetaMomentIntegrand
      (α := m - 1) (β := m + 1) (d := 2)
      (by linarith) (by linarith) (by linarith) (by linarith),
    integral_unequalFD4InverseBetaMomentIntegrand
      (α := m - 1) (β := m + 1) (d := 4)
      (by linarith) (by linarith) (by linarith) (by linarith)]
  congr 4 <;> ring

theorem integral_unequalFixedDifferenceFourRealEnvelopeFactor_plus
    {m : ℝ} (hm : 7 ≤ m) :
    (∫ y, unequalFixedDifferenceFourRealEnvelopeFactor m y
      ∂betaMeasure (m + 1) (m - 1))
      = unequalFixedDifferenceFourRealMPlus m := by
  rw [integral_unequalFixedDifferenceFourRealEnvelopeFactor_plus_betaRatios hm]
  have hp3arg : m + 3 = m + 1 + 2 := by ring
  have hm3arg : m - 3 = m - 1 - 2 := by ring
  have hm5arg : m - 5 = m - 1 - 4 := by ring
  rw [hp3arg, hm3arg, hm5arg,
    unequalFixedDifferenceFourRealPlusBetaRatioTwo hm,
    unequalFixedDifferenceFourRealPlusBetaRatioFour hm]
  have hm1 : m - 1 ≠ 0 := ne_of_gt (by linarith)
  have hm2 : m - 2 ≠ 0 := ne_of_gt (by linarith)
  have hm3 : m - 3 ≠ 0 := ne_of_gt (by linarith)
  have hm4 : m - 4 ≠ 0 := ne_of_gt (by linarith)
  have hm5ne : m - 5 ≠ 0 := ne_of_gt (by linarith)
  have h2m1 : 2 * m - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2m1' : -1 + m * 2 ≠ 0 := by linarith
  have h2m1'' : m * 2 - 1 ≠ 0 := by linarith
  have hEllMoment :
      unequalFixedDifferenceFourRealEll m
          * (((m + 1) * (m + 2) * (2 * m - 1) * (2 * m - 2))
            / ((m - 2) * (m - 3) * (m - 4) * (m - 5)))
        =
      ((m + 1) * (m + 2) / ((m - 2) * (m - 3)))
        * (60 * m ^ 2 / ((m - 4) * (m - 5))) := by
    unfold unequalFixedDifferenceFourRealEll
    field_simp [hm1, hm2, hm3, hm4, hm5ne,
      h2m1, h2m1', h2m1'']
    ring
  rw [hEllMoment]
  unfold unequalFixedDifferenceFourRealMPlus
  ring

theorem integral_unequalFixedDifferenceFourRealEnvelopeFactor_minus
    {m : ℝ} (hm : 7 ≤ m) :
    (∫ y, unequalFixedDifferenceFourRealEnvelopeFactor m y
      ∂betaMeasure (m - 1) (m + 1))
      = unequalFixedDifferenceFourRealMMinus m := by
  rw [integral_unequalFixedDifferenceFourRealEnvelopeFactor_minus_betaRatios hm]
  have hratio2 :
      beta (m + 1) (m - 1) / beta (m - 1) (m + 1) = 1 := by
    convert unequalFixedDifferenceFourRealMinusBetaRatioTwo hm using 1 <;> ring
  have hratio4 :
      beta (m + 1) (m - 3) / beta (m - 1) (m + 1)
        =
      ((2 * m - 1) * (2 * m - 2)) / ((m - 2) * (m - 3)) := by
    convert unequalFixedDifferenceFourRealMinusBetaRatioFour hm using 1 <;> ring
  rw [hratio2, hratio4]
  have hm1 : m - 1 ≠ 0 := ne_of_gt (by linarith)
  have hm2 : m - 2 ≠ 0 := ne_of_gt (by linarith)
  have hm3 : m - 3 ≠ 0 := ne_of_gt (by linarith)
  have h2m1 : 2 * m - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2m1' : -1 + m * 2 ≠ 0 := by linarith
  have h2m1'' : m * 2 - 1 ≠ 0 := by linarith
  have hEllMoment :
      unequalFixedDifferenceFourRealEll m
          * (((2 * m - 1) * (2 * m - 2))
            / ((m - 2) * (m - 3)))
        =
      60 * m ^ 2 / ((m - 2) * (m - 3)) := by
    unfold unequalFixedDifferenceFourRealEll
    field_simp [hm1, hm2, hm3, h2m1, h2m1', h2m1'']
    ring
  rw [hEllMoment]
  unfold unequalFixedDifferenceFourRealMMinus
  ring

/-! ## Integrating the pointwise `C` bounds -/

theorem unequalFixedDifferenceFourRealK_sq_lt_Ell
    {m : ℝ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourRealK m ^ 2
      < unequalFixedDifferenceFourRealEll m := by
  have hm0 : 0 < m := by linarith
  have h2m1 : 0 < 2 * m - 1 := by linarith
  have hm1 : 0 < m - 1 := by linarith
  unfold unequalFixedDifferenceFourRealK
    unequalFixedDifferenceFourRealEll
  rw [div_pow]
  rw [div_lt_div_iff₀ (sq_pos_of_pos h2m1) (mul_pos hm1 h2m1)]
  have hpos :
      0 < 6 * m ^ 2 * (2 * m - 1) * (4 * m + 1) := by
    positivity
  nlinarith

theorem unequalFixedDifferenceFourRealCKernel_nonneg
    {m : ℝ} (hm : 7 ≤ m) (u : ℝ) :
    0 ≤ unequalFixedDifferenceFourRealCKernel m u := by
  have hEll := unequalFixedDifferenceFourRealEll_pos hm
  have hgap := (unequalFixedDifferenceFourRealK_sq_lt_Ell hm).le
  have hid :
      unequalFixedDifferenceFourRealEll m
          * unequalFixedDifferenceFourRealCKernel m u
        =
      (unequalFixedDifferenceFourRealEll m * u
          - unequalFixedDifferenceFourRealK m
            * unequalFixedDifferenceFourRealC m) ^ 2
        + unequalFixedDifferenceFourRealC m ^ 2
          * (unequalFixedDifferenceFourRealEll m
            - unequalFixedDifferenceFourRealK m ^ 2) := by
    unfold unequalFixedDifferenceFourRealCKernel
    ring
  have hrhs :
      0 ≤
      (unequalFixedDifferenceFourRealEll m * u
          - unequalFixedDifferenceFourRealK m
            * unequalFixedDifferenceFourRealC m) ^ 2
        + unequalFixedDifferenceFourRealC m ^ 2
          * (unequalFixedDifferenceFourRealEll m
            - unequalFixedDifferenceFourRealK m ^ 2) :=
    add_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hgap))
  nlinarith

def unequalFixedDifferenceFourRealPlusCIntegrand
    (m s y : ℝ) : ℝ :=
  unequalDampedPhi
      (unequalFixedDifferenceFourRealT m)
      (unequalFixedDifferenceFourRealKappa m)
      (unequalDampedR s y) ^ 2
    * unequalFixedDifferenceFourRealCKernel m
        (unequalDampedU (unequalFixedDifferenceFourRealQ m) s y)

def unequalFixedDifferenceFourRealMinusCIntegrand
    (m s y : ℝ) : ℝ :=
  unequalDampedPhi
      (unequalFixedDifferenceFourRealQ m)
      (-unequalFixedDifferenceFourRealKappa m)
      (unequalDampedR s y) ^ 2
    * unequalFixedDifferenceFourRealCKernel m
        (unequalDampedU (unequalFixedDifferenceFourRealT m) s y)

theorem measurable_unequalFixedDifferenceFourRealPlusCIntegrand
    (m s : ℝ) :
    Measurable (unequalFixedDifferenceFourRealPlusCIntegrand m s) := by
  unfold unequalFixedDifferenceFourRealPlusCIntegrand
    unequalFixedDifferenceFourRealCKernel unequalDampedPhi
    unequalDampedInner unequalDampedR unequalDampedU unequalDampedDenom
  fun_prop

theorem measurable_unequalFixedDifferenceFourRealMinusCIntegrand
    (m s : ℝ) :
    Measurable (unequalFixedDifferenceFourRealMinusCIntegrand m s) := by
  unfold unequalFixedDifferenceFourRealMinusCIntegrand
    unequalFixedDifferenceFourRealCKernel unequalDampedPhi
    unequalDampedInner unequalDampedR unequalDampedU unequalDampedDenom
  fun_prop

theorem unequalFixedDifferenceFourRealPlusCIntegrand_nonneg
    {m : ℝ} (hm : 7 ≤ m) (s y : ℝ) :
    0 ≤ unequalFixedDifferenceFourRealPlusCIntegrand m s y := by
  exact mul_nonneg (sq_nonneg _)
    (unequalFixedDifferenceFourRealCKernel_nonneg hm _)

theorem unequalFixedDifferenceFourRealMinusCIntegrand_nonneg
    {m : ℝ} (hm : 7 ≤ m) (s y : ℝ) :
    0 ≤ unequalFixedDifferenceFourRealMinusCIntegrand m s y := by
  exact mul_nonneg (sq_nonneg _)
    (unequalFixedDifferenceFourRealCKernel_nonneg hm _)

theorem integrable_unequalFixedDifferenceFourRealPlusCIntegrand
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Integrable (unequalFixedDifferenceFourRealPlusCIntegrand m s)
      (betaMeasure (m + 1) (m - 1)) := by
  have henv :=
    (integrable_unequalFixedDifferenceFourRealEnvelopeFactor_plus hm).const_mul
      ((1 - s) ^ 2)
  apply henv.mono_nonneg
    (measurable_unequalFixedDifferenceFourRealPlusCIntegrand m s).aestronglyMeasurable
  · exact ae_of_all _
      (unequalFixedDifferenceFourRealPlusCIntegrand_nonneg hm s)
  · filter_upwards [betaMeasure_unequalFD4Real_ae_mem_Ioo] with y hy
    have hpoint :=
      unequalFixedDifferenceFourRealC_pointwise_le_envelope
        hm hs0 hs1 hy.1.le hy.2
    rw [unequalFixedDifferenceFourRealEnvelopeFactor_eq m hy.1 hy.2]
    simpa only [unequalFixedDifferenceFourRealPlusCIntegrand, mul_assoc]
      using hpoint

theorem integrable_unequalFixedDifferenceFourRealMinusCIntegrand
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Integrable (unequalFixedDifferenceFourRealMinusCIntegrand m s)
      (betaMeasure (m - 1) (m + 1)) := by
  have henv :=
    (integrable_unequalFixedDifferenceFourRealEnvelopeFactor_minus hm).const_mul
      ((1 - s) ^ 2)
  apply henv.mono_nonneg
    (measurable_unequalFixedDifferenceFourRealMinusCIntegrand m s).aestronglyMeasurable
  · exact ae_of_all _
      (unequalFixedDifferenceFourRealMinusCIntegrand_nonneg hm s)
  · filter_upwards [betaMeasure_unequalFD4Real_ae_mem_Ioo] with y hy
    have hpoint :=
      unequalFixedDifferenceFourRealSwappedC_pointwise_le_envelope
        hm hs0 hs1 hy.1.le hy.2
    rw [unequalFixedDifferenceFourRealEnvelopeFactor_eq m hy.1 hy.2]
    simpa only [unequalFixedDifferenceFourRealMinusCIntegrand, mul_assoc]
      using hpoint

theorem integral_unequalFixedDifferenceFourRealPlusC_le_envelopeIntegral
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ y, unequalFixedDifferenceFourRealPlusCIntegrand m s y
      ∂betaMeasure (m + 1) (m - 1))
      ≤
    (1 - s) ^ 2
      * ∫ y, unequalFixedDifferenceFourRealEnvelopeFactor m y
        ∂betaMeasure (m + 1) (m - 1) := by
  have hraw :=
    integrable_unequalFixedDifferenceFourRealPlusCIntegrand hm hs0 hs1
  have henv :=
    (integrable_unequalFixedDifferenceFourRealEnvelopeFactor_plus hm).const_mul
      ((1 - s) ^ 2)
  calc
    (∫ y, unequalFixedDifferenceFourRealPlusCIntegrand m s y
      ∂betaMeasure (m + 1) (m - 1))
        ≤
      ∫ y, (1 - s) ^ 2
        * unequalFixedDifferenceFourRealEnvelopeFactor m y
        ∂betaMeasure (m + 1) (m - 1) := by
          apply integral_mono_ae hraw henv
          filter_upwards [betaMeasure_unequalFD4Real_ae_mem_Ioo] with y hy
          have hpoint :=
            unequalFixedDifferenceFourRealC_pointwise_le_envelope
              hm hs0 hs1 hy.1.le hy.2
          rw [unequalFixedDifferenceFourRealEnvelopeFactor_eq m hy.1 hy.2]
          simpa only [unequalFixedDifferenceFourRealPlusCIntegrand, mul_assoc]
            using hpoint
    _ =
      (1 - s) ^ 2
        * ∫ y, unequalFixedDifferenceFourRealEnvelopeFactor m y
          ∂betaMeasure (m + 1) (m - 1) := by
            rw [integral_const_mul]

theorem integral_unequalFixedDifferenceFourRealMinusC_le_envelopeIntegral
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ y, unequalFixedDifferenceFourRealMinusCIntegrand m s y
      ∂betaMeasure (m - 1) (m + 1))
      ≤
    (1 - s) ^ 2
      * ∫ y, unequalFixedDifferenceFourRealEnvelopeFactor m y
        ∂betaMeasure (m - 1) (m + 1) := by
  have hraw :=
    integrable_unequalFixedDifferenceFourRealMinusCIntegrand hm hs0 hs1
  have henv :=
    (integrable_unequalFixedDifferenceFourRealEnvelopeFactor_minus hm).const_mul
      ((1 - s) ^ 2)
  calc
    (∫ y, unequalFixedDifferenceFourRealMinusCIntegrand m s y
      ∂betaMeasure (m - 1) (m + 1))
        ≤
      ∫ y, (1 - s) ^ 2
        * unequalFixedDifferenceFourRealEnvelopeFactor m y
        ∂betaMeasure (m - 1) (m + 1) := by
          apply integral_mono_ae hraw henv
          filter_upwards [betaMeasure_unequalFD4Real_ae_mem_Ioo] with y hy
          have hpoint :=
            unequalFixedDifferenceFourRealSwappedC_pointwise_le_envelope
              hm hs0 hs1 hy.1.le hy.2
          rw [unequalFixedDifferenceFourRealEnvelopeFactor_eq m hy.1 hy.2]
          simpa only [unequalFixedDifferenceFourRealMinusCIntegrand, mul_assoc]
            using hpoint
    _ =
      (1 - s) ^ 2
        * ∫ y, unequalFixedDifferenceFourRealEnvelopeFactor m y
          ∂betaMeasure (m - 1) (m + 1) := by
            rw [integral_const_mul]

/-- Exact right-chart quadratic envelope. -/
theorem integral_unequalFixedDifferenceFourRealPlusC_le
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ y, unequalFixedDifferenceFourRealPlusCIntegrand m s y
      ∂betaMeasure (m + 1) (m - 1))
      ≤ unequalFixedDifferenceFourRealMPlus m * (1 - s) ^ 2 := by
  calc
    (∫ y, unequalFixedDifferenceFourRealPlusCIntegrand m s y
      ∂betaMeasure (m + 1) (m - 1))
        ≤
      (1 - s) ^ 2
        * ∫ y, unequalFixedDifferenceFourRealEnvelopeFactor m y
          ∂betaMeasure (m + 1) (m - 1) :=
      integral_unequalFixedDifferenceFourRealPlusC_le_envelopeIntegral
        hm hs0 hs1
    _ = unequalFixedDifferenceFourRealMPlus m * (1 - s) ^ 2 := by
      rw [integral_unequalFixedDifferenceFourRealEnvelopeFactor_plus hm]
      ring

/-- Exact sharper swapped-chart quadratic envelope. -/
theorem integral_unequalFixedDifferenceFourRealMinusC_le_MMinus
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ y, unequalFixedDifferenceFourRealMinusCIntegrand m s y
      ∂betaMeasure (m - 1) (m + 1))
      ≤ unequalFixedDifferenceFourRealMMinus m * (1 - s) ^ 2 := by
  calc
    (∫ y, unequalFixedDifferenceFourRealMinusCIntegrand m s y
      ∂betaMeasure (m - 1) (m + 1))
        ≤
      (1 - s) ^ 2
        * ∫ y, unequalFixedDifferenceFourRealEnvelopeFactor m y
          ∂betaMeasure (m - 1) (m + 1) :=
      integral_unequalFixedDifferenceFourRealMinusC_le_envelopeIntegral
        hm hs0 hs1
    _ = unequalFixedDifferenceFourRealMMinus m * (1 - s) ^ 2 := by
      rw [integral_unequalFixedDifferenceFourRealEnvelopeFactor_minus hm]
      ring

/-- The common right-chart constant also bounds the swapped chart. -/
theorem integral_unequalFixedDifferenceFourRealMinusC_le
    {m : ℝ} (hm : 7 ≤ m)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ y, unequalFixedDifferenceFourRealMinusCIntegrand m s y
      ∂betaMeasure (m - 1) (m + 1))
      ≤ unequalFixedDifferenceFourRealMPlus m * (1 - s) ^ 2 := by
  calc
    (∫ y, unequalFixedDifferenceFourRealMinusCIntegrand m s y
      ∂betaMeasure (m - 1) (m + 1))
        ≤ unequalFixedDifferenceFourRealMMinus m * (1 - s) ^ 2 :=
      integral_unequalFixedDifferenceFourRealMinusC_le_MMinus hm hs0 hs1
    _ ≤ unequalFixedDifferenceFourRealMPlus m * (1 - s) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (unequalFixedDifferenceFourRealMMinus_lt_MPlus hm).le
        (sq_nonneg (1 - s))

end

end GraybillDeal
