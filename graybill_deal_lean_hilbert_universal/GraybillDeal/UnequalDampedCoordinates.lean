import GraybillDeal.UnequalDampedAlgebra
import Mathlib.Tactic.FieldSimp

/-!
# One-sided coordinates for the damped unequal-size certificate

This file formalizes the Möbius coordinates used on the two sides of the
pivot in the fixed `(ν₁,ν₂) = (12,16)` certificate.

For `t + q = 1`, `0 ≤ s < 1`, and `0 ≤ y ≤ 1`, set

`θ = t / (1-q s)`, `r = (1-y)/(1-s y)`, and
`u = (1-q s)/(1-s y)`.

The generic algebraic lemmas are shared by the original side
`(t,q,κ) = (3/7,4/7,1045/5439)` and the swapped side
`(4/7,3/7,-1045/5439)`.
-/

namespace GraybillDeal

noncomputable section

/-- The common one-sided denominator `1-sy`. -/
def unequalDampedDenom (s y : ℝ) : ℝ :=
  1 - s * y

/-- The variance-ratio coordinate on one side of the pivot. -/
def unequalDampedTheta (t q s : ℝ) : ℝ :=
  t / (1 - q * s)

/-- The Graybill--Deal weight in the one-sided coordinate. -/
def unequalDampedR (s y : ℝ) : ℝ :=
  (1 - y) / unequalDampedDenom s y

/-- The reciprocal normalized residual scale `1/D`. -/
def unequalDampedU (q s y : ℝ) : ℝ :=
  (1 - q * s) / unequalDampedDenom s y

/-- The undamped inner factor in the endpoint-damped direction. -/
def unequalDampedInner (t κ r : ℝ) : ℝ :=
  t - r + κ * r * (1 - r)

/-- The generic endpoint-damped direction. -/
def unequalDampedPhi (t κ r : ℝ) : ℝ :=
  r * (1 - r) * unequalDampedInner t κ r

/-- The polynomial numerator of the inner factor. -/
def unequalDampedF (t q κ s y : ℝ) : ℝ :=
  (-q + (1 - t * s) * y) * unequalDampedDenom s y
    + κ * (1 - s) * y * (1 - y)

/-- The polynomial numerator of `c-k/D`. -/
def unequalDampedPsiNumerator (q c k s y : ℝ) : ℝ :=
  (c - k) + s * (k * q - c * y)

/-- The fixed quadratic kernel in the `(13,17)` reduced `C` coefficient. -/
def unequalDampedCKernel13_17 (u : ℝ) : ℝ :=
  unequalDampedC13_17 ^ 2
    - (84 * unequalDampedC13_17 / 13) * u
    + (245 / 13) * u ^ 2

theorem unequalDampedDenom_pos
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (_hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 < unequalDampedDenom s y := by
  have hsy : s * y ≤ s := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hy1)]
  simp only [unequalDampedDenom]
  linarith

theorem one_sub_qs_pos
    {q s : ℝ} (_hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    0 < 1 - q * s := by
  have hqs : q * s ≤ s := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hq1)]
  linarith

theorem unequalDampedU_pos
    {q s y : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 < unequalDampedU q s y :=
  div_pos
    (one_sub_qs_pos hq0 hq1 hs0 hs1)
    (unequalDampedDenom_pos hs0 hs1 hy0 hy1)

theorem unequalDampedR_mem_Icc
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    unequalDampedR s y ∈ Set.Icc (0 : ℝ) 1 := by
  have hd := unequalDampedDenom_pos hs0 hs1 hy0 hy1
  constructor
  · exact div_nonneg (sub_nonneg.mpr hy1) hd.le
  · rw [unequalDampedR, div_le_one hd]
    exact one_sub_sy_ge_one_sub_y hs1.le hy0

/-- Exact one-sided formula for `r-θ`. -/
theorem unequalDampedR_sub_theta
    {t q s y : ℝ} (htq : t + q = 1)
    (hqs : 1 - q * s ≠ 0) (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedR s y - unequalDampedTheta t q s
      =
    (1 - s) * (q - y)
      / ((1 - q * s) * unequalDampedDenom s y) := by
  rw [unequalDampedR, unequalDampedTheta,
    div_sub_div (1 - y) t hsy hqs]
  rw [show
    unequalDampedDenom s y * (1 - q * s)
      = (1 - q * s) * unequalDampedDenom s y by ring]
  congr 1
  simp only [unequalDampedDenom]
  rw [show t = 1 - q by linarith]
  ring

/-- Exact one-sided formula for `r(1-r)`. -/
theorem unequalDampedR_mul_one_sub
    {s y : ℝ} (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedR s y * (1 - unequalDampedR s y)
      =
    (1 - s) * y * (1 - y) / unequalDampedDenom s y ^ 2 := by
  apply (eq_div_iff (pow_ne_zero 2 hsy)).2
  rw [unequalDampedR]
  field_simp [hsy]
  simp only [unequalDampedDenom]
  ring

/-- The inner factor is `F/(1-sy)²`. -/
theorem unequalDampedInner_eq_F_div
    {t q κ s y : ℝ} (htq : t + q = 1)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedInner t κ (unequalDampedR s y)
      =
    unequalDampedF t q κ s y / unequalDampedDenom s y ^ 2 := by
  apply (eq_div_iff (pow_ne_zero 2 hsy)).2
  rw [unequalDampedInner, unequalDampedR]
  field_simp [hsy]
  simp only [unequalDampedF, unequalDampedDenom]
  rw [show q = 1 - t by linarith]
  ring

/-- The affine factor `c-ku` is `Ψ/(1-sy)`. -/
theorem unequalDampedC_sub_kU_eq_psi_div
    {q c k s y : ℝ} (hsy : unequalDampedDenom s y ≠ 0) :
    c - k * unequalDampedU q s y
      =
    unequalDampedPsiNumerator q c k s y
      / unequalDampedDenom s y := by
  apply (eq_div_iff hsy).2
  rw [unequalDampedU]
  field_simp [hsy]
  simp only [unequalDampedPsiNumerator, unequalDampedDenom]
  ring

/-- Exact factorization of the one-sided `B` integrand. -/
theorem unequalDampedB_integrand_factorization
    {t q κ c k s y : ℝ} (htq : t + q = 1)
    (hqs : 1 - q * s ≠ 0) (hsy : unequalDampedDenom s y ≠ 0) :
    (unequalDampedR s y - unequalDampedTheta t q s)
        * unequalDampedPhi t κ (unequalDampedR s y)
        * (c - k * unequalDampedU q s y)
      =
    (1 - s) ^ 2 / (1 - q * s)
      *
    ((q - y) * y * (1 - y)
        * unequalDampedF t q κ s y
        * unequalDampedPsiNumerator q c k s y
      / unequalDampedDenom s y ^ 6) := by
  rw [unequalDampedR_sub_theta htq hqs hsy,
    unequalDampedPhi, unequalDampedR_mul_one_sub hsy,
    unequalDampedInner_eq_F_div htq hsy,
    unequalDampedC_sub_kU_eq_psi_div hsy]
  field_simp [hqs, hsy]

/-- Generic exact factorization of a quadratic `C` integrand. -/
theorem unequalDampedC_integrand_factorization
    {t q κ c a₂ b₂ s y : ℝ} (htq : t + q = 1)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedPhi t κ (unequalDampedR s y) ^ 2
        * (c ^ 2 - a₂ * unequalDampedU q s y
          + b₂ * unequalDampedU q s y ^ 2)
      =
    (1 - s) ^ 2
      *
    (y ^ 2 * (1 - y) ^ 2 * unequalDampedF t q κ s y ^ 2
      / unequalDampedDenom s y ^ 8)
      * (c ^ 2 - a₂ * unequalDampedU q s y
          + b₂ * unequalDampedU q s y ^ 2) := by
  rw [unequalDampedPhi, unequalDampedR_mul_one_sub hsy,
    unequalDampedInner_eq_F_div htq hsy]
  field_simp [hsy]

/-- The reciprocal residual scale is bounded by `1/(1-y)`. -/
theorem unequalDampedU_le_one_div_one_sub_y
    {q s y : ℝ}
    (hq0 : 0 ≤ q) (_hq1 : q ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    unequalDampedU q s y ≤ 1 / (1 - y) := by
  have hd := unequalDampedDenom_pos hs0 hs1 hy0 hy1.le
  have hy : 0 < 1 - y := sub_pos.mpr hy1
  rw [unequalDampedU]
  exact (div_le_div_iff₀ hd hy).2
    (by
      simpa [unequalDampedDenom] using
        (one_sub_qs_mul_one_sub_y_le_one_sub_sy
          hq0 hs0 hs1.le hy0 hy1.le))

/-- A convenient square version of the reciprocal-scale bound. -/
theorem unequalDampedU_sq_le
    {q s y : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    unequalDampedU q s y ^ 2 ≤ (1 / (1 - y)) ^ 2 := by
  have hu := unequalDampedU_pos hq0 hq1 hs0 hs1 hy0 hy1.le
  exact (sq_le_sq₀ hu.le (by positivity)).2
    (unequalDampedU_le_one_div_one_sub_y
      hq0 hq1 hs0 hs1 hy0 hy1)

/--
The factor `r(1-r)` is bounded by its endpoint envelope in the one-sided
coordinate.
-/
theorem unequalDampedR_mul_one_sub_le
    {s y : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    unequalDampedR s y * (1 - unequalDampedR s y)
      ≤ (1 - s) * y / (1 - y) := by
  have hd := unequalDampedDenom_pos hs0 hs1 hy0 hy1.le
  have hne : unequalDampedDenom s y ≠ 0 := ne_of_gt hd
  have hy : 0 < 1 - y := sub_pos.mpr hy1
  have hbase : 1 - y ≤ unequalDampedDenom s y :=
    one_sub_sy_ge_one_sub_y hs1.le hy0
  have hsq :
      (1 - y) ^ 2 ≤ unequalDampedDenom s y ^ 2 :=
    (sq_le_sq₀ hy.le hd.le).2 hbase
  rw [unequalDampedR_mul_one_sub hne]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) hy).2
  have hfactor : 0 ≤ (1 - s) * y :=
    mul_nonneg (sub_nonneg.mpr hs1.le) hy0
  nlinarith

/--
If the inner direction is bounded by `4/7`, then the square of the full
damped direction has the endpoint envelope used in the `C` estimate.
-/
theorem unequalDampedPhi_sq_le_envelope
    {t κ s y : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hinner :
      |unequalDampedInner t κ (unequalDampedR s y)| ≤ 4 / 7) :
    unequalDampedPhi t κ (unequalDampedR s y) ^ 2
      ≤
    (1 - s) ^ 2 * (16 / 49)
      * (y ^ 2 / (1 - y) ^ 2) := by
  have hr := unequalDampedR_mem_Icc hs0 hs1 hy0 hy1.le
  have hrprod0 :
      0 ≤ unequalDampedR s y * (1 - unequalDampedR s y) :=
    mul_nonneg hr.1 (sub_nonneg.mpr hr.2)
  have henv0 : 0 ≤ (1 - s) * y / (1 - y) := by positivity
  have hrprod :=
    unequalDampedR_mul_one_sub_le hs0 hs1 hy0 hy1
  have hrprod_sq :
      (unequalDampedR s y * (1 - unequalDampedR s y)) ^ 2
        ≤ ((1 - s) * y / (1 - y)) ^ 2 :=
    (sq_le_sq₀ hrprod0 henv0).2 hrprod
  have hinner_sq :
      unequalDampedInner t κ (unequalDampedR s y) ^ 2
        ≤ (4 / 7 : ℝ) ^ 2 := by
    rw [sq_le_sq]
    norm_num
    exact hinner
  rw [unequalDampedPhi]
  calc
    (unequalDampedR s y * (1 - unequalDampedR s y)
        * unequalDampedInner t κ (unequalDampedR s y)) ^ 2
        =
      (unequalDampedR s y * (1 - unequalDampedR s y)) ^ 2
        * unequalDampedInner t κ (unequalDampedR s y) ^ 2 := by ring
    _ ≤
      ((1 - s) * y / (1 - y)) ^ 2 * (4 / 7 : ℝ) ^ 2 :=
        mul_le_mul hrprod_sq hinner_sq
          (sq_nonneg _) (sq_nonneg _)
    _ =
      (1 - s) ^ 2 * (16 / 49)
        * (y ^ 2 / (1 - y) ^ 2) := by
          field_simp [ne_of_gt (sub_pos.mpr hy1)]
          ring

/--
Generic pointwise `C` envelope, assuming the fixed `4/7` bound on the inner
direction.
-/
theorem unequalDampedC_pointwise_le_envelope
    {t q κ s y : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hinner :
      |unequalDampedInner t κ (unequalDampedR s y)| ≤ 4 / 7) :
    unequalDampedPhi t κ (unequalDampedR s y) ^ 2
        * unequalDampedCKernel13_17 (unequalDampedU q s y)
      ≤
    (1 - s) ^ 2 * (16 / 49)
      * (y ^ 2 / (1 - y) ^ 2)
      * (unequalDampedC13_17 ^ 2
        + (245 / 13) / (1 - y) ^ 2) := by
  have hu := unequalDampedU_pos hq0 hq1 hs0 hs1 hy0 hy1.le
  have hu_sq :=
    unequalDampedU_sq_le hq0 hq1 hs0 hs1 hy0 hy1
  have hk :
      unequalDampedCKernel13_17 (unequalDampedU q s y)
        ≤ unequalDampedC13_17 ^ 2
          + (245 / 13) * unequalDampedU q s y ^ 2 := by
    simpa [unequalDampedCKernel13_17] using
      (unequalDampedQuadraticKernel_le (u := unequalDampedU q s y) hu.le)
  have hcoef : 0 ≤ (245 / 13 : ℝ) := by norm_num
  have hy : 0 < 1 - y := sub_pos.mpr hy1
  have hk' :
      unequalDampedC13_17 ^ 2
          + (245 / 13) * unequalDampedU q s y ^ 2
        ≤ unequalDampedC13_17 ^ 2
          + (245 / 13) / (1 - y) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hu_sq hcoef
    have heq :
        (245 / 13 : ℝ) * (1 / (1 - y)) ^ 2
          = (245 / 13) / (1 - y) ^ 2 := by
      field_simp [ne_of_gt hy]
    rw [← heq]
    linarith
  have hphi :=
    unequalDampedPhi_sq_le_envelope hs0 hs1 hy0 hy1 hinner
  have hupper0 :
      0 ≤ unequalDampedC13_17 ^ 2
        + (245 / 13) / (1 - y) ^ 2 := by positivity
  calc
    unequalDampedPhi t κ (unequalDampedR s y) ^ 2
          * unequalDampedCKernel13_17 (unequalDampedU q s y)
        ≤
      unequalDampedPhi t κ (unequalDampedR s y) ^ 2
        * (unequalDampedC13_17 ^ 2
          + (245 / 13) * unequalDampedU q s y ^ 2) :=
            mul_le_mul_of_nonneg_left hk (sq_nonneg _)
    _ ≤
      unequalDampedPhi t κ (unequalDampedR s y) ^ 2
        * (unequalDampedC13_17 ^ 2
          + (245 / 13) / (1 - y) ^ 2) :=
            mul_le_mul_of_nonneg_left hk' (sq_nonneg _)
    _ ≤
      ((1 - s) ^ 2 * (16 / 49)
        * (y ^ 2 / (1 - y) ^ 2))
        * (unequalDampedC13_17 ^ 2
          + (245 / 13) / (1 - y) ^ 2) :=
            mul_le_mul_of_nonneg_right hphi hupper0

/-- The fixed `k=42/13` used on both one-sided charts. -/
def unequalDampedK13_17 : ℝ := 42 / 13

/-- The generic direction agrees with the fixed original-side definition. -/
theorem unequalDampedPhi_original_eq (r : ℝ) :
    unequalDampedPhi (3 / 7) unequalDampedKappa13_17 r
      = unequalDampedPhi13_17 r := by
  rfl

/-- Original-side specialization of the `r-θ` identity. -/
theorem unequalDampedR_sub_theta13_17
    {s y : ℝ}
    (hqs : 1 - (4 / 7 : ℝ) * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedR s y
        - unequalDampedTheta (3 / 7) (4 / 7) s
      =
    (1 - s) * ((4 / 7 : ℝ) - y)
      / ((1 - (4 / 7) * s) * unequalDampedDenom s y) := by
  exact unequalDampedR_sub_theta (by norm_num) hqs hsy

/-- Swapped-side specialization of the `r-θ` identity. -/
theorem unequalDampedR_sub_theta17_13
    {s y : ℝ}
    (hqs : 1 - (3 / 7 : ℝ) * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedR s y
        - unequalDampedTheta (4 / 7) (3 / 7) s
      =
    (1 - s) * ((3 / 7 : ℝ) - y)
      / ((1 - (3 / 7) * s) * unequalDampedDenom s y) := by
  exact unequalDampedR_sub_theta (by norm_num) hqs hsy

/-- Original-side specialization of the inner `F` identity. -/
theorem unequalDampedInner_eq_F_div13_17
    {s y : ℝ} (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedInner (3 / 7) unequalDampedKappa13_17
        (unequalDampedR s y)
      =
    unequalDampedF (3 / 7) (4 / 7)
        unequalDampedKappa13_17 s y
      / unequalDampedDenom s y ^ 2 :=
  unequalDampedInner_eq_F_div (by norm_num) hsy

/-- Swapped-side specialization of the inner `F` identity. -/
theorem unequalDampedInner_eq_F_div17_13
    {s y : ℝ} (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedInner (4 / 7) (-unequalDampedKappa13_17)
        (unequalDampedR s y)
      =
    unequalDampedF (4 / 7) (3 / 7)
        (-unequalDampedKappa13_17) s y
      / unequalDampedDenom s y ^ 2 :=
  unequalDampedInner_eq_F_div (by norm_num) hsy

/-- Original-side specialization of the affine `Ψ` identity. -/
theorem unequalDampedPsi_factorization13_17
    {s y : ℝ} (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedC13_17
        - unequalDampedK13_17 * unequalDampedU (4 / 7) s y
      =
    unequalDampedPsiNumerator (4 / 7)
        unequalDampedC13_17 unequalDampedK13_17 s y
      / unequalDampedDenom s y :=
  unequalDampedC_sub_kU_eq_psi_div hsy

/-- Swapped-side specialization of the affine `Ψ` identity. -/
theorem unequalDampedPsi_factorization17_13
    {s y : ℝ} (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedC13_17
        - unequalDampedK13_17 * unequalDampedU (3 / 7) s y
      =
    unequalDampedPsiNumerator (3 / 7)
        unequalDampedC13_17 unequalDampedK13_17 s y
      / unequalDampedDenom s y :=
  unequalDampedC_sub_kU_eq_psi_div hsy

/-- Original-side specialization of the `B` integrand identity. -/
theorem unequalDampedB_integrand_factorization13_17
    {s y : ℝ}
    (hqs : 1 - (4 / 7 : ℝ) * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    (unequalDampedR s y
        - unequalDampedTheta (3 / 7) (4 / 7) s)
        * unequalDampedPhi (3 / 7) unequalDampedKappa13_17
          (unequalDampedR s y)
        * (unequalDampedC13_17
          - unequalDampedK13_17 * unequalDampedU (4 / 7) s y)
      =
    (1 - s) ^ 2 / (1 - (4 / 7) * s)
      *
    (((4 / 7 : ℝ) - y) * y * (1 - y)
        * unequalDampedF (3 / 7) (4 / 7)
          unequalDampedKappa13_17 s y
        * unequalDampedPsiNumerator (4 / 7)
          unequalDampedC13_17 unequalDampedK13_17 s y
      / unequalDampedDenom s y ^ 6) := by
  apply unequalDampedB_integrand_factorization
  · norm_num
  · exact hqs
  · exact hsy

/-- Swapped-side specialization of the `B` integrand identity. -/
theorem unequalDampedB_integrand_factorization17_13
    {s y : ℝ}
    (hqs : 1 - (3 / 7 : ℝ) * s ≠ 0)
    (hsy : unequalDampedDenom s y ≠ 0) :
    (unequalDampedR s y
        - unequalDampedTheta (4 / 7) (3 / 7) s)
        * unequalDampedPhi (4 / 7) (-unequalDampedKappa13_17)
          (unequalDampedR s y)
        * (unequalDampedC13_17
          - unequalDampedK13_17 * unequalDampedU (3 / 7) s y)
      =
    (1 - s) ^ 2 / (1 - (3 / 7) * s)
      *
    (((3 / 7 : ℝ) - y) * y * (1 - y)
        * unequalDampedF (4 / 7) (3 / 7)
          (-unequalDampedKappa13_17) s y
        * unequalDampedPsiNumerator (3 / 7)
          unequalDampedC13_17 unequalDampedK13_17 s y
      / unequalDampedDenom s y ^ 6) := by
  apply unequalDampedB_integrand_factorization
  · norm_num
  · exact hqs
  · exact hsy

/-- Original-side exact `C` factorization. -/
theorem unequalDampedC_integrand_factorization13_17
    {s y : ℝ} (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedPhi (3 / 7) unequalDampedKappa13_17
          (unequalDampedR s y) ^ 2
        * unequalDampedCKernel13_17 (unequalDampedU (4 / 7) s y)
      =
    (1 - s) ^ 2
      *
    (y ^ 2 * (1 - y) ^ 2
        * unequalDampedF (3 / 7) (4 / 7)
          unequalDampedKappa13_17 s y ^ 2
      / unequalDampedDenom s y ^ 8)
      * unequalDampedCKernel13_17
          (unequalDampedU (4 / 7) s y) := by
  simpa [unequalDampedCKernel13_17] using
    (unequalDampedC_integrand_factorization
      (t := (3 / 7 : ℝ)) (q := (4 / 7 : ℝ))
      (κ := unequalDampedKappa13_17)
      (c := unequalDampedC13_17)
      (a₂ := 84 * unequalDampedC13_17 / 13)
      (b₂ := (245 / 13 : ℝ)) (s := s) (y := y)
      (by norm_num) hsy)

/-- Swapped-side exact `C` factorization. -/
theorem unequalDampedC_integrand_factorization17_13
    {s y : ℝ} (hsy : unequalDampedDenom s y ≠ 0) :
    unequalDampedPhi (4 / 7) (-unequalDampedKappa13_17)
          (unequalDampedR s y) ^ 2
        * unequalDampedCKernel13_17 (unequalDampedU (3 / 7) s y)
      =
    (1 - s) ^ 2
      *
    (y ^ 2 * (1 - y) ^ 2
        * unequalDampedF (4 / 7) (3 / 7)
          (-unequalDampedKappa13_17) s y ^ 2
      / unequalDampedDenom s y ^ 8)
      * unequalDampedCKernel13_17
          (unequalDampedU (3 / 7) s y) := by
  simpa [unequalDampedCKernel13_17] using
    (unequalDampedC_integrand_factorization
      (t := (4 / 7 : ℝ)) (q := (3 / 7 : ℝ))
      (κ := -unequalDampedKappa13_17)
      (c := unequalDampedC13_17)
      (a₂ := 84 * unequalDampedC13_17 / 13)
      (b₂ := (245 / 13 : ℝ)) (s := s) (y := y)
      (by norm_num) hsy)

/-- Original-side pointwise `C` envelope. -/
theorem unequalDampedC_pointwise_le_envelope13_17
    {s y : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    unequalDampedPhi (3 / 7) unequalDampedKappa13_17
          (unequalDampedR s y) ^ 2
        * unequalDampedCKernel13_17 (unequalDampedU (4 / 7) s y)
      ≤
    (1 - s) ^ 2 * (16 / 49)
      * (y ^ 2 / (1 - y) ^ 2)
      * (unequalDampedC13_17 ^ 2
        + (245 / 13) / (1 - y) ^ 2) := by
  apply unequalDampedC_pointwise_le_envelope
      (q := (4 / 7 : ℝ)) (t := (3 / 7 : ℝ))
      (κ := unequalDampedKappa13_17)
      (by norm_num) (by norm_num) hs0 hs1 hy0 hy1
  simpa [unequalDampedInner] using
    (abs_unequalDampedInner13_17_le
      (unequalDampedR_mem_Icc hs0 hs1 hy0 hy1.le))

/-- Swapped-side pointwise `C` envelope. -/
theorem unequalDampedC_pointwise_le_envelope17_13
    {s y : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    unequalDampedPhi (4 / 7) (-unequalDampedKappa13_17)
          (unequalDampedR s y) ^ 2
        * unequalDampedCKernel13_17 (unequalDampedU (3 / 7) s y)
      ≤
    (1 - s) ^ 2 * (16 / 49)
      * (y ^ 2 / (1 - y) ^ 2)
      * (unequalDampedC13_17 ^ 2
        + (245 / 13) / (1 - y) ^ 2) := by
  apply unequalDampedC_pointwise_le_envelope
      (q := (3 / 7 : ℝ)) (t := (4 / 7 : ℝ))
      (κ := -unequalDampedKappa13_17)
      (by norm_num) (by norm_num) hs0 hs1 hy0 hy1
  have h := abs_unequalDampedInner17_13_le
    (unequalDampedR_mem_Icc hs0 hs1 hy0 hy1.le)
  convert h using 1
  congr 1
  simp only [unequalDampedInner]
  ring

end

end GraybillDeal
