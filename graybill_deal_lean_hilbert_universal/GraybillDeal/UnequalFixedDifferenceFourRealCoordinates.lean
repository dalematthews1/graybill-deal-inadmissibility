import GraybillDeal.UnequalDampedCoordinates
import GraybillDeal.UnequalFixedDifferenceFourRealAlgebra

/-!
# Real-parameter one-sided coordinates for the difference-four family

This module specializes the generic one-sided coordinate algebra to a real
family parameter `m ≥ 7`.  It is the real-parameter counterpart of
`UnequalFixedDifferenceFourCoordinates` and supplies the pointwise quadratic
envelopes needed before integrating against the two beta laws.
-/

namespace GraybillDeal

noncomputable section

/-- The family coefficient `k = 6m/(2m-1)`. -/
def unequalFixedDifferenceFourRealK (m : ℝ) : ℝ :=
  6 * m / (2 * m - 1)

/-- The family coefficient `ℓ = 30m²/((m-1)(2m-1))`. -/
def unequalFixedDifferenceFourRealEll (m : ℝ) : ℝ :=
  30 * m ^ 2 / ((m - 1) * (2 * m - 1))

/-- The quadratic kernel in the real-parameter reduced `C` coefficient. -/
def unequalFixedDifferenceFourRealCKernel (m u : ℝ) : ℝ :=
  unequalFixedDifferenceFourRealC m ^ 2
    - 2 * unequalFixedDifferenceFourRealK m
        * unequalFixedDifferenceFourRealC m * u
    + unequalFixedDifferenceFourRealEll m * u ^ 2

theorem unequalFixedDifferenceFourRealT_add_Q
    {m : ℝ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourRealT m
        + unequalFixedDifferenceFourRealQ m = 1 := by
  have hm0 : m ≠ 0 := by linarith
  unfold unequalFixedDifferenceFourRealT unequalFixedDifferenceFourRealQ
  field_simp [hm0]
  ring

theorem unequalFixedDifferenceFourRealT_lt_Q
    {m : ℝ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourRealT m
      < unequalFixedDifferenceFourRealQ m := by
  have hden : 0 < 2 * m := by linarith
  unfold unequalFixedDifferenceFourRealT unequalFixedDifferenceFourRealQ
  exact (div_lt_div_iff₀ hden hden).2 (by nlinarith)

theorem unequalFixedDifferenceFourRealT_le_one
    {m : ℝ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourRealT m ≤ 1 := by
  have ht := unequalFixedDifferenceFourRealT_pos hm
  have hsum := unequalFixedDifferenceFourRealT_add_Q hm
  have hq := unequalFixedDifferenceFourRealQ_pos hm
  linarith

theorem unequalFixedDifferenceFourRealQ_le_one
    {m : ℝ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourRealQ m ≤ 1 := by
  have ht := unequalFixedDifferenceFourRealT_pos hm
  have hsum := unequalFixedDifferenceFourRealT_add_Q hm
  linarith

theorem unequalFixedDifferenceFourRealK_pos
    {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourRealK m := by
  unfold unequalFixedDifferenceFourRealK
  exact div_pos (by positivity) (by linarith)

theorem unequalFixedDifferenceFourRealEll_pos
    {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourRealEll m := by
  unfold unequalFixedDifferenceFourRealEll
  exact div_pos
    (mul_pos (by norm_num) (sq_pos_of_pos (by linarith)))
    (mul_pos (by linarith) (by linarith))

/-- The affine constant satisfies `c-k = 1/(2m)`. -/
theorem unequalFixedDifferenceFourRealC_sub_K
    {m : ℝ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourRealC m
        - unequalFixedDifferenceFourRealK m
      = 1 / (2 * m) := by
  have hm0 : m ≠ 0 := by linarith
  have h2m1 : 2 * m - 1 ≠ 0 := by linarith
  have h2m1' : -1 + m * 2 ≠ 0 := by linarith
  have h2m1'' : m * 2 - 1 ≠ 0 := by linarith
  have h2m : 2 * m ≠ 0 := mul_ne_zero (by norm_num) hm0
  have hden : 2 * m * (2 * m - 1) ≠ 0 :=
    mul_ne_zero h2m h2m1
  unfold unequalFixedDifferenceFourRealC
    unequalFixedDifferenceFourRealK
  field_simp [hm0, h2m1, h2m1', h2m1'', h2m, hden]
  ring

/--
The asymmetric inner factor is uniformly bounded by the larger pivot
`q = (m+1)/(2m)` on the entire weight interval.
-/
theorem abs_unequalFixedDifferenceFourRealInner_le_Q
    {m : ℝ} (hm : 7 ≤ m) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    |unequalDampedInner
        (unequalFixedDifferenceFourRealT m)
        (unequalFixedDifferenceFourRealKappa m) r|
      ≤ unequalFixedDifferenceFourRealQ m := by
  have htq := unequalFixedDifferenceFourRealT_add_Q hm
  have htqOrder := unequalFixedDifferenceFourRealT_lt_Q hm
  have hκ0 := (unequalFixedDifferenceFourRealKappa_pos hm).le
  have hκ1 := (unequalFixedDifferenceFourRealKappa_lt_one hm).le
  have hrprod : 0 ≤ r * (1 - r) :=
    mul_nonneg hr.1 (sub_nonneg.mpr hr.2)
  have hκprod :
      unequalFixedDifferenceFourRealKappa m * (r * (1 - r))
        ≤ 1 * (r * (1 - r)) :=
    mul_le_mul_of_nonneg_right hκ1 hrprod
  have hκprod' :
      unequalFixedDifferenceFourRealKappa m * r * (1 - r)
        ≤ r * (1 - r) := by
    simpa [mul_assoc] using hκprod
  have hrprod_le : r * (1 - r) ≤ r := by
    nlinarith [sq_nonneg r]
  have hupper :
      unequalDampedInner
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealKappa m) r
        ≤ unequalFixedDifferenceFourRealQ m := by
    unfold unequalDampedInner
    have hleT :
        unequalFixedDifferenceFourRealT m - r
              + unequalFixedDifferenceFourRealKappa m * r * (1 - r)
          ≤ unequalFixedDifferenceFourRealT m := by
      linarith
    exact hleT.trans htqOrder.le
  have hlower :
      -unequalFixedDifferenceFourRealQ m
        ≤ unequalDampedInner
            (unequalFixedDifferenceFourRealT m)
            (unequalFixedDifferenceFourRealKappa m) r := by
    have hone :
        0 ≤
          (1 - r)
            * (1 + unequalFixedDifferenceFourRealKappa m * r) := by
      have hκr :
          0 ≤ unequalFixedDifferenceFourRealKappa m * r :=
        mul_nonneg hκ0 hr.1
      exact mul_nonneg (sub_nonneg.mpr hr.2) (by linarith)
    unfold unequalDampedInner
    nlinarith
  exact abs_le.2 ⟨hlower, hupper⟩

/--
Dropping the nonpositive linear term gives the real-parameter quadratic
kernel upper bound.
-/
theorem unequalFixedDifferenceFourRealCKernel_le
    {m : ℝ} (hm : 7 ≤ m) {u : ℝ} (hu : 0 ≤ u) :
    unequalFixedDifferenceFourRealCKernel m u
      ≤ unequalFixedDifferenceFourRealC m ^ 2
        + unequalFixedDifferenceFourRealEll m * u ^ 2 := by
  have hk := unequalFixedDifferenceFourRealK_pos hm
  have hc := unequalFixedDifferenceFourRealC_pos hm
  unfold unequalFixedDifferenceFourRealCKernel
  nlinarith [mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hk.le) hc.le)
    hu]

/--
Real-parameter endpoint envelope for the squared perturbation direction.
-/
theorem unequalFixedDifferenceFourRealPhi_sq_le_envelope
    {m : ℝ} (hm : 7 ≤ m)
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    unequalDampedPhi
        (unequalFixedDifferenceFourRealT m)
        (unequalFixedDifferenceFourRealKappa m)
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
    abs_unequalFixedDifferenceFourRealInner_le_Q hm hr
  have hinner_sq :
      unequalDampedInner
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealKappa m)
          (unequalDampedR s y) ^ 2
        ≤ unequalFixedDifferenceFourRealQ m ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_pos (unequalFixedDifferenceFourRealQ_pos hm)] using hinner
  rw [unequalDampedPhi]
  calc
    (unequalDampedR s y * (1 - unequalDampedR s y)
        * unequalDampedInner
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealKappa m)
          (unequalDampedR s y)) ^ 2
        =
      (unequalDampedR s y * (1 - unequalDampedR s y)) ^ 2
        * unequalDampedInner
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealKappa m)
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

/-- The real-parameter pointwise quadratic envelope before beta integration. -/
theorem unequalFixedDifferenceFourRealC_pointwise_le_envelope
    {m : ℝ} (hm : 7 ≤ m)
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    unequalDampedPhi
        (unequalFixedDifferenceFourRealT m)
        (unequalFixedDifferenceFourRealKappa m)
        (unequalDampedR s y) ^ 2
      * unequalFixedDifferenceFourRealCKernel m
          (unequalDampedU
            (unequalFixedDifferenceFourRealQ m) s y)
      ≤
    (1 - s) ^ 2 * unequalFixedDifferenceFourRealQ m ^ 2
      * (y ^ 2 / (1 - y) ^ 2)
      * (unequalFixedDifferenceFourRealC m ^ 2
        + unequalFixedDifferenceFourRealEll m / (1 - y) ^ 2) := by
  have hq0 := (unequalFixedDifferenceFourRealQ_pos hm).le
  have hq1 := unequalFixedDifferenceFourRealQ_le_one hm
  have hu :=
    unequalDampedU_pos hq0 hq1 hs0 hs1 hy0 hy1.le
  have hu_sq :=
    unequalDampedU_sq_le hq0 hq1 hs0 hs1 hy0 hy1
  have hk := unequalFixedDifferenceFourRealCKernel_le hm hu.le
  have hEll := (unequalFixedDifferenceFourRealEll_pos hm).le
  have hy : 0 < 1 - y := sub_pos.mpr hy1
  have hk' :
      unequalFixedDifferenceFourRealC m ^ 2
          + unequalFixedDifferenceFourRealEll m
            * unequalDampedU
                (unequalFixedDifferenceFourRealQ m) s y ^ 2
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
    unequalFixedDifferenceFourRealPhi_sq_le_envelope
      hm hs0 hs1 hy0 hy1
  have hupper0 :
      0 ≤ unequalFixedDifferenceFourRealC m ^ 2
        + unequalFixedDifferenceFourRealEll m / (1 - y) ^ 2 := by
    positivity
  calc
    unequalDampedPhi
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealKappa m)
          (unequalDampedR s y) ^ 2
        * unequalFixedDifferenceFourRealCKernel m
            (unequalDampedU
              (unequalFixedDifferenceFourRealQ m) s y)
        ≤
      unequalDampedPhi
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealKappa m)
          (unequalDampedR s y) ^ 2
        * (unequalFixedDifferenceFourRealC m ^ 2
          + unequalFixedDifferenceFourRealEll m
            * unequalDampedU
                (unequalFixedDifferenceFourRealQ m) s y ^ 2) :=
      mul_le_mul_of_nonneg_left hk (sq_nonneg _)
    _ ≤
      unequalDampedPhi
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealKappa m)
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

end

end GraybillDeal
