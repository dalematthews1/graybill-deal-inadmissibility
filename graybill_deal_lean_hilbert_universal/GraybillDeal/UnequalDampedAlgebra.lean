import GraybillDeal.Elementary
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Elementary bounds for the damped unequal-size certificate

This file records the purely algebraic part of the fixed
`(ν₁, ν₂) = (12, 16)` certificate.  The proposed direction and constants are

`φ(r) = r(1-r) (3/7 - r + (1045/5439) r(1-r))`,

`c = 601/182`, and `ε = 1/2000000`.

The analytic series argument supplies one-sided bounds

`B ≤ -b₀ (1-s)²` and `C ≤ M₊ (1-s)²`.

The final theorem below proves, without taking a ratio or invoking
compactness, that those two bounds imply strict negativity of the reduced
risk difference for the explicit fixed `ε`.
-/

namespace GraybillDeal

noncomputable section

/-- The asymmetric correction in the damped `(13,17)` direction. -/
def unequalDampedKappa13_17 : ℝ := 1045 / 5439

/-- The constant multiplying the standardized squared mean difference. -/
def unequalDampedC13_17 : ℝ := 601 / 182

/-- The endpoint-damped perturbation direction for sample sizes `(13,17)`. -/
def unequalDampedPhi13_17 (r : ℝ) : ℝ :=
  r * (1 - r)
    * (3 / 7 - r + unequalDampedKappa13_17 * r * (1 - r))

/-- The constant term in both one-sided linear-risk series. -/
def unequalDampedB0 : ℝ := 2927 / 12944820

/-- A common upper bound for the two one-sided quadratic coefficients. -/
def unequalDampedMPlus : ℝ := 1194621192 / 2028845

/-- A concrete perturbation size, independent of all unknown parameters. -/
def unequalDampedEpsilon13_17 : ℝ := 1 / 2000000

theorem unequalDampedKappa13_17_pos :
    0 < unequalDampedKappa13_17 := by
  norm_num [unequalDampedKappa13_17]

theorem unequalDampedKappa13_17_lt_one :
    unequalDampedKappa13_17 < 1 := by
  norm_num [unequalDampedKappa13_17]

theorem unequalDampedC13_17_pos :
    0 < unequalDampedC13_17 := by
  norm_num [unequalDampedC13_17]

theorem unequalDampedB0_pos :
    0 < unequalDampedB0 := by
  norm_num [unequalDampedB0]

theorem unequalDampedMPlus_pos :
    0 < unequalDampedMPlus := by
  norm_num [unequalDampedMPlus]

theorem unequalDampedEpsilon13_17_pos :
    0 < unequalDampedEpsilon13_17 := by
  norm_num [unequalDampedEpsilon13_17]

/--
The inner factor in the original damped direction stays between `-4/7` and
`4/7` on the unit interval.
-/
theorem abs_unequalDampedInner13_17_le
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    |3 / 7 - r + unequalDampedKappa13_17 * r * (1 - r)| ≤ 4 / 7 := by
  have hrprod : 0 ≤ r * (1 - r) :=
    mul_nonneg hr.1 (sub_nonneg.mpr hr.2)
  rw [abs_le]
  constructor <;>
    norm_num [unequalDampedKappa13_17] at * <;> nlinarith

/--
After swapping the two samples, the pivot becomes `4/7` and the correction
coefficient changes sign.  The same absolute bound holds.
-/
theorem abs_unequalDampedInner17_13_le
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    |4 / 7 - r - unequalDampedKappa13_17 * r * (1 - r)| ≤ 4 / 7 := by
  have hrprod : 0 ≤ r * (1 - r) :=
    mul_nonneg hr.1 (sub_nonneg.mpr hr.2)
  rw [abs_le]
  constructor <;>
    norm_num [unequalDampedKappa13_17] at * <;> nlinarith

/-- The elementary lower bound for the one-sided denominator. -/
theorem one_sub_sy_ge_one_sub_y
    {s y : ℝ} (hs : s ≤ 1) (hy : 0 ≤ y) :
    1 - y ≤ 1 - s * y := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) hy]

/--
The inequality which bounds the reciprocal normalized denominator by
`1 / (1-y)`.
-/
theorem one_sub_qs_mul_one_sub_y_le_one_sub_sy
    {q s y : ℝ}
    (hq : 0 ≤ q) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (1 - q * s) * (1 - y) ≤ 1 - s * y := by
  have h₁ : 0 ≤ (1 - s) * y :=
    mul_nonneg (sub_nonneg.mpr hs1) hy0
  have h₂ : 0 ≤ q * s * (1 - y) :=
    mul_nonneg (mul_nonneg hq hs0) (sub_nonneg.mpr hy1)
  nlinarith

/--
Dropping the negative linear term gives the quadratic-kernel upper bound
used in the explicit `C` estimate.
-/
theorem unequalDampedQuadraticKernel_le
    {u : ℝ} (hu : 0 ≤ u) :
    unequalDampedC13_17 ^ 2
        - (84 * unequalDampedC13_17 / 13) * u
        + (245 / 13) * u ^ 2
      ≤
    unequalDampedC13_17 ^ 2 + (245 / 13) * u ^ 2 := by
  have hc := unequalDampedC13_17_pos
  nlinarith

/-- Exact rational allowance for the explicit perturbation size. -/
theorem unequalDampedEpsilon13_17_lt_allowance :
    unequalDampedEpsilon13_17
      < 2 * unequalDampedB0 / unequalDampedMPlus := by
  norm_num [unequalDampedEpsilon13_17, unequalDampedB0,
    unequalDampedMPlus]

/--
The explicit ratio-free final step.

Once the two one-sided analytic estimates have supplied

`B ≤ -b₀(1-s)²` and `C ≤ M₊(1-s)²`,

the fixed value `ε = 1/2000000` makes `2εB + ε²C` strictly negative.
-/
theorem unequalDampedReducedRisk_neg_of_bounds
    {s B C : ℝ} (hs : s < 1)
    (hB : B ≤ -unequalDampedB0 * (1 - s) ^ 2)
    (hC : C ≤ unequalDampedMPlus * (1 - s) ^ 2) :
    2 * unequalDampedEpsilon13_17 * B
        + unequalDampedEpsilon13_17 ^ 2 * C < 0 := by
  have hε := unequalDampedEpsilon13_17_pos
  have hε2 : 0 ≤ unequalDampedEpsilon13_17 ^ 2 := sq_nonneg _
  have hsq : 0 < (1 - s) ^ 2 := by
    positivity
  have hallow :
      unequalDampedEpsilon13_17 * unequalDampedMPlus
        < 2 * unequalDampedB0 := by
    norm_num [unequalDampedEpsilon13_17, unequalDampedMPlus,
      unequalDampedB0]
  calc
    2 * unequalDampedEpsilon13_17 * B
          + unequalDampedEpsilon13_17 ^ 2 * C
        ≤
      2 * unequalDampedEpsilon13_17
          * (-unequalDampedB0 * (1 - s) ^ 2)
        + unequalDampedEpsilon13_17 ^ 2
          * (unequalDampedMPlus * (1 - s) ^ 2) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hB
                (mul_nonneg (by norm_num) hε.le))
              (mul_le_mul_of_nonneg_left hC hε2)
    _ =
      (1 - s) ^ 2 * unequalDampedEpsilon13_17
        * (unequalDampedEpsilon13_17 * unequalDampedMPlus
          - 2 * unequalDampedB0) := by
            ring
    _ < 0 := by
      exact mul_neg_of_pos_of_neg
        (mul_pos hsq hε)
        (sub_neg.mpr hallow)

end

end GraybillDeal
