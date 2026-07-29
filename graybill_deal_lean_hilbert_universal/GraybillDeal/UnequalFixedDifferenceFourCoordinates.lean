import GraybillDeal.UnequalDampedCoordinates
import GraybillDeal.UnequalFixedDifferenceFourAlgebra

/-!
# One-sided coordinates for the fixed-difference-four family

This module specializes the generic one-sided coordinate algebra to

`(n₁,n₂) = (2m-1,2m+3)`, `m ≥ 7`.

It records the remaining reduced-risk constants and proves the pointwise
quadratic envelope needed before integrating against the two beta laws.
-/

namespace GraybillDeal

noncomputable section

/-- The family coefficient `k = 6m/(2m-1)`. -/
def unequalFixedDifferenceFourK (m : ℕ) : ℝ :=
  6 * (m : ℝ) / (2 * (m : ℝ) - 1)

/-- The family coefficient `ℓ = 30m²/((m-1)(2m-1))`. -/
def unequalFixedDifferenceFourEll (m : ℕ) : ℝ :=
  30 * (m : ℝ) ^ 2
    / (((m : ℝ) - 1) * (2 * (m : ℝ) - 1))

/-- The quadratic kernel in the family reduced `C` coefficient. -/
def unequalFixedDifferenceFourCKernel (m : ℕ) (u : ℝ) : ℝ :=
  unequalFixedDifferenceFourC m ^ 2
    - 2 * unequalFixedDifferenceFourK m
        * unequalFixedDifferenceFourC m * u
    + unequalFixedDifferenceFourEll m * u ^ 2

private theorem unequalFD4Coordinates_cast_seven_le
    {m : ℕ} (hm : 7 ≤ m) :
    (7 : ℝ) ≤ (m : ℝ) := by
  exact_mod_cast hm

theorem unequalFixedDifferenceFourT_add_Q
    {m : ℕ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourT m
        + unequalFixedDifferenceFourQ m = 1 := by
  have hmR := unequalFD4Coordinates_cast_seven_le hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  unfold unequalFixedDifferenceFourT unequalFixedDifferenceFourQ
  field_simp [hm0]
  ring

theorem unequalFixedDifferenceFourT_lt_Q
    {m : ℕ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourT m
      < unequalFixedDifferenceFourQ m := by
  have hmR := unequalFD4Coordinates_cast_seven_le hm
  have hden : 0 < 2 * (m : ℝ) := by linarith
  unfold unequalFixedDifferenceFourT unequalFixedDifferenceFourQ
  exact (div_lt_div_iff₀ hden hden).2 (by nlinarith)

theorem unequalFixedDifferenceFourT_le_one
    {m : ℕ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourT m ≤ 1 := by
  have ht := unequalFixedDifferenceFourT_pos hm
  have hsum := unequalFixedDifferenceFourT_add_Q hm
  have hq := unequalFixedDifferenceFourQ_pos hm
  linarith

theorem unequalFixedDifferenceFourQ_le_one
    {m : ℕ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourQ m ≤ 1 := by
  have ht := unequalFixedDifferenceFourT_pos hm
  have hsum := unequalFixedDifferenceFourT_add_Q hm
  linarith

theorem unequalFixedDifferenceFourK_pos
    {m : ℕ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourK m := by
  have hmR := unequalFD4Coordinates_cast_seven_le hm
  unfold unequalFixedDifferenceFourK
  exact div_pos (by positivity) (by linarith)

theorem unequalFixedDifferenceFourEll_pos
    {m : ℕ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourEll m := by
  have hmR := unequalFD4Coordinates_cast_seven_le hm
  unfold unequalFixedDifferenceFourEll
  exact div_pos
    (mul_pos (by norm_num) (sq_pos_of_pos (by linarith)))
    (mul_pos (by linarith) (by linarith))

/-- The affine constant satisfies `c-k = 1/(2m)`. -/
theorem unequalFixedDifferenceFourC_sub_K
    {m : ℕ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourC m
        - unequalFixedDifferenceFourK m
      = 1 / (2 * (m : ℝ)) := by
  have hmR := unequalFD4Coordinates_cast_seven_le hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have h2m1 : 2 * (m : ℝ) - 1 ≠ 0 := by linarith
  have h2m1' : -1 + (m : ℝ) * 2 ≠ 0 := by linarith
  have h2m1'' : (m : ℝ) * 2 - 1 ≠ 0 := by linarith
  have h2m : 2 * (m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hm0
  have hden :
      2 * (m : ℝ) * (2 * (m : ℝ) - 1) ≠ 0 :=
    mul_ne_zero h2m h2m1
  unfold unequalFixedDifferenceFourC unequalFixedDifferenceFourK
  field_simp [hm0, h2m1, h2m1', h2m, hden]
  ring

/--
The asymmetric inner factor is uniformly bounded by the larger pivot
`q = (m+1)/(2m)` on the entire weight interval.
-/
theorem abs_unequalFixedDifferenceFourInner_le_Q
    {m : ℕ} (hm : 7 ≤ m) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    |unequalDampedInner
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourKappa m) r|
      ≤ unequalFixedDifferenceFourQ m := by
  have htq := unequalFixedDifferenceFourT_add_Q hm
  have htqOrder := unequalFixedDifferenceFourT_lt_Q hm
  have hκ0 := (unequalFixedDifferenceFourKappa_pos hm).le
  have hκ1 := (unequalFixedDifferenceFourKappa_lt_one hm).le
  have hrprod : 0 ≤ r * (1 - r) :=
    mul_nonneg hr.1 (sub_nonneg.mpr hr.2)
  have hκprod :
      unequalFixedDifferenceFourKappa m * (r * (1 - r))
        ≤ 1 * (r * (1 - r)) :=
    mul_le_mul_of_nonneg_right hκ1 hrprod
  have hκprod' :
      unequalFixedDifferenceFourKappa m * r * (1 - r)
        ≤ r * (1 - r) := by
    simpa [mul_assoc] using hκprod
  have hrprod_le : r * (1 - r) ≤ r := by
    nlinarith [sq_nonneg r]
  have hupper :
      unequalDampedInner
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourKappa m) r
        ≤ unequalFixedDifferenceFourQ m := by
    unfold unequalDampedInner
    have hleT :
        unequalFixedDifferenceFourT m - r
              + unequalFixedDifferenceFourKappa m * r * (1 - r)
          ≤ unequalFixedDifferenceFourT m := by
      linarith
    exact hleT.trans htqOrder.le
  have hlower :
      -unequalFixedDifferenceFourQ m
        ≤ unequalDampedInner
            (unequalFixedDifferenceFourT m)
            (unequalFixedDifferenceFourKappa m) r := by
    have hone :
        0 ≤
          (1 - r)
            * (1 + unequalFixedDifferenceFourKappa m * r) := by
      have hκr :
          0 ≤ unequalFixedDifferenceFourKappa m * r :=
        mul_nonneg hκ0 hr.1
      exact mul_nonneg (sub_nonneg.mpr hr.2)
        (by linarith)
    unfold unequalDampedInner
    nlinarith
  exact abs_le.2 ⟨hlower, hupper⟩

/--
Dropping the nonpositive linear term gives the family quadratic-kernel
upper bound.
-/
theorem unequalFixedDifferenceFourCKernel_le
    {m : ℕ} (hm : 7 ≤ m) {u : ℝ} (hu : 0 ≤ u) :
    unequalFixedDifferenceFourCKernel m u
      ≤ unequalFixedDifferenceFourC m ^ 2
        + unequalFixedDifferenceFourEll m * u ^ 2 := by
  have hk := unequalFixedDifferenceFourK_pos hm
  have hc := unequalFixedDifferenceFourC_pos hm
  unfold unequalFixedDifferenceFourCKernel
  nlinarith [mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hk.le) hc.le)
    hu]

/--
Family version of the endpoint envelope for the squared perturbation
direction.
-/
theorem unequalFixedDifferenceFourPhi_sq_le_envelope
    {m : ℕ} (hm : 7 ≤ m)
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    unequalDampedPhi
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourKappa m)
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
    abs_unequalFixedDifferenceFourInner_le_Q hm hr
  have hinner_sq :
      unequalDampedInner
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourKappa m)
          (unequalDampedR s y) ^ 2
        ≤ unequalFixedDifferenceFourQ m ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_pos (unequalFixedDifferenceFourQ_pos hm)] using hinner
  rw [unequalDampedPhi]
  calc
    (unequalDampedR s y * (1 - unequalDampedR s y)
        * unequalDampedInner
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourKappa m)
          (unequalDampedR s y)) ^ 2
        =
      (unequalDampedR s y * (1 - unequalDampedR s y)) ^ 2
        * unequalDampedInner
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourKappa m)
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

/-- The family pointwise quadratic envelope before beta integration. -/
theorem unequalFixedDifferenceFourC_pointwise_le_envelope
    {m : ℕ} (hm : 7 ≤ m)
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    unequalDampedPhi
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourKappa m)
        (unequalDampedR s y) ^ 2
      * unequalFixedDifferenceFourCKernel m
          (unequalDampedU
            (unequalFixedDifferenceFourQ m) s y)
      ≤
    (1 - s) ^ 2 * unequalFixedDifferenceFourQ m ^ 2
      * (y ^ 2 / (1 - y) ^ 2)
      * (unequalFixedDifferenceFourC m ^ 2
        + unequalFixedDifferenceFourEll m / (1 - y) ^ 2) := by
  have hq0 := (unequalFixedDifferenceFourQ_pos hm).le
  have hq1 := unequalFixedDifferenceFourQ_le_one hm
  have hu :=
    unequalDampedU_pos hq0 hq1 hs0 hs1 hy0 hy1.le
  have hu_sq :=
    unequalDampedU_sq_le hq0 hq1 hs0 hs1 hy0 hy1
  have hk :=
    unequalFixedDifferenceFourCKernel_le hm hu.le
  have hEll := (unequalFixedDifferenceFourEll_pos hm).le
  have hy : 0 < 1 - y := sub_pos.mpr hy1
  have hk' :
      unequalFixedDifferenceFourC m ^ 2
          + unequalFixedDifferenceFourEll m
            * unequalDampedU
                (unequalFixedDifferenceFourQ m) s y ^ 2
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
    unequalFixedDifferenceFourPhi_sq_le_envelope
      hm hs0 hs1 hy0 hy1
  have hupper0 :
      0 ≤ unequalFixedDifferenceFourC m ^ 2
        + unequalFixedDifferenceFourEll m / (1 - y) ^ 2 := by
    positivity
  calc
    unequalDampedPhi
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourKappa m)
          (unequalDampedR s y) ^ 2
        * unequalFixedDifferenceFourCKernel m
            (unequalDampedU
              (unequalFixedDifferenceFourQ m) s y)
        ≤
      unequalDampedPhi
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourKappa m)
          (unequalDampedR s y) ^ 2
        * (unequalFixedDifferenceFourC m ^ 2
          + unequalFixedDifferenceFourEll m
            * unequalDampedU
                (unequalFixedDifferenceFourQ m) s y ^ 2) :=
      mul_le_mul_of_nonneg_left hk (sq_nonneg _)
    _ ≤
      unequalDampedPhi
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourKappa m)
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

end

end GraybillDeal
