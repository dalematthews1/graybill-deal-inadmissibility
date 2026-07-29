import GraybillDeal.GeneralSeriesCoefficients
import GraybillDeal.SeriesIntegration
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Termwise integration of the general paired kernel

For arbitrary residual degrees of freedom `ν`, the beta weight in the
paired linear-risk kernel is the real power

`(1 - x²) ^ (ν / 2)`.

This file proves that this causes no new difficulty in the exchange of the
negative-binomial series and the integral.  On `x ∈ [0,1]` and for `ν ≥ 0`,
the real-power weight lies in `[0,1]`.  The remaining polynomial is bounded
by the sum of the absolute values of its seven coefficients.  This gives a
summable, uniform-in-`x` majorant whenever `|s| < 1`.

The later coefficient-collection layer can therefore work with the
integrals of `generalPointwiseSeriesTerm` without carrying any additional
analytic convergence assumption.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

/-- The factor multiplying the order-four negative-binomial series. -/
def generalPairedSeriesPrefactor (ν s x : ℝ) : ℝ :=
  (1 - x ^ 2) ^ (ν / 2) * x ^ 2
    * generalPairedPolynomial ν (s ^ 2) (x ^ 2)

/-- The raw pointwise summands of the paired general kernel. -/
def generalPointwiseSeriesTerm (ν s x : ℝ) (m : ℕ) : ℝ :=
  generalPairedSeriesPrefactor ν s x
    * (((m + 4).choose 4 : ℝ) * (s ^ 2 * x ^ 2) ^ m)

/--
A bound for `generalPairedPolynomial ν z y` on the unit square.

Keeping the absolute coefficient sum explicit avoids introducing any
unnecessary upper bound on `ν`.
-/
def generalPolynomialMajorant (ν : ℝ) : ℝ :=
  let α := generalAlpha ν
  |2 * α| + |2 - 10 * α| + |-10 + 20 * α|
    + |20 - 20 * α| + |-20 + 10 * α|
    + |10 - 2 * α| + 2

/-- The corresponding summable uniform majorant for the pointwise series. -/
def generalPointwiseMajorant (ν s : ℝ) (m : ℕ) : ℝ :=
  generalPolynomialMajorant ν
    * ((m + 4).choose 4 : ℝ) * (s ^ 2) ^ m

theorem generalPolynomialMajorant_nonneg (ν : ℝ) :
    0 ≤ generalPolynomialMajorant ν := by
  unfold generalPolynomialMajorant
  dsimp only
  positivity

/--
The paired numerator polynomial is bounded on the unit square by the
absolute sum of its coefficients.
-/
theorem generalPairedPolynomial_abs_le_majorant
    {ν z y : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |generalPairedPolynomial ν z y| ≤ generalPolynomialMajorant ν := by
  let α := generalAlpha ν
  have hz2_nonneg : 0 ≤ z ^ 2 := sq_nonneg z
  have hz3_nonneg : 0 ≤ z ^ 3 := pow_nonneg hz0 3
  have hy2_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
  have hy3_nonneg : 0 ≤ y ^ 3 := pow_nonneg hy0 3
  have hz2_le : z ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ hz0 hz1 2
  have hz3_le : z ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ hz0 hz1 3
  have hy2_le : y ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ hy0 hy1 2
  have hy3_le : y ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ hy0 hy1 3
  have hzy_nonneg : 0 ≤ z * y := mul_nonneg hz0 hy0
  have hzy_le : z * y ≤ 1 :=
    (mul_le_mul hz1 hy1 hy0 (by norm_num)).trans_eq (by norm_num)
  have hz2y_nonneg : 0 ≤ z ^ 2 * y := mul_nonneg hz2_nonneg hy0
  have hz2y_le : z ^ 2 * y ≤ 1 :=
    (mul_le_mul hz2_le hy1 hy0 (by norm_num)).trans_eq (by norm_num)
  have hz2y2_nonneg : 0 ≤ z ^ 2 * y ^ 2 :=
    mul_nonneg hz2_nonneg hy2_nonneg
  have hz2y2_le : z ^ 2 * y ^ 2 ≤ 1 :=
    (mul_le_mul hz2_le hy2_le hy2_nonneg (by norm_num)).trans_eq (by norm_num)
  have hz3y2_nonneg : 0 ≤ z ^ 3 * y ^ 2 :=
    mul_nonneg hz3_nonneg hy2_nonneg
  have hz3y2_le : z ^ 3 * y ^ 2 ≤ 1 :=
    (mul_le_mul hz3_le hy2_le hy2_nonneg (by norm_num)).trans_eq (by norm_num)
  have hz3y3_nonneg : 0 ≤ z ^ 3 * y ^ 3 :=
    mul_nonneg hz3_nonneg hy3_nonneg
  have hz3y3_le : z ^ 3 * y ^ 3 ≤ 1 :=
    (mul_le_mul hz3_le hy3_le hy3_nonneg (by norm_num)).trans_eq (by norm_num)
  have h0 : |2 * α| ≤ |2 * α| := le_rfl
  have h1 : |(2 - 10 * α) * z| ≤ |2 - 10 * α| := by
    rw [abs_mul, abs_of_nonneg hz0]
    exact mul_le_of_le_one_right (abs_nonneg _) hz1
  have h2 : |(-10 + 20 * α) * z * y| ≤ |-10 + 20 * α| := by
    rw [show (-10 + 20 * α) * z * y = (-10 + 20 * α) * (z * y) by ring,
      abs_mul, abs_of_nonneg hzy_nonneg]
    exact mul_le_of_le_one_right (abs_nonneg _) hzy_le
  have h3 : |(20 - 20 * α) * z ^ 2 * y| ≤ |20 - 20 * α| := by
    rw [show (20 - 20 * α) * z ^ 2 * y =
        (20 - 20 * α) * (z ^ 2 * y) by ring,
      abs_mul, abs_of_nonneg hz2y_nonneg]
    exact mul_le_of_le_one_right (abs_nonneg _) hz2y_le
  have h4 :
      |(-20 + 10 * α) * z ^ 2 * y ^ 2| ≤ |-20 + 10 * α| := by
    rw [show (-20 + 10 * α) * z ^ 2 * y ^ 2 =
        (-20 + 10 * α) * (z ^ 2 * y ^ 2) by ring,
      abs_mul, abs_of_nonneg hz2y2_nonneg]
    exact mul_le_of_le_one_right (abs_nonneg _) hz2y2_le
  have h5 :
      |(10 - 2 * α) * z ^ 3 * y ^ 2| ≤ |10 - 2 * α| := by
    rw [show (10 - 2 * α) * z ^ 3 * y ^ 2 =
        (10 - 2 * α) * (z ^ 3 * y ^ 2) by ring,
      abs_mul, abs_of_nonneg hz3y2_nonneg]
    exact mul_le_of_le_one_right (abs_nonneg _) hz3y2_le
  have h6 : |2 * z ^ 3 * y ^ 3| ≤ 2 := by
    rw [show 2 * z ^ 3 * y ^ 3 = 2 * (z ^ 3 * y ^ 3) by ring,
      abs_mul, abs_of_nonneg hz3y3_nonneg]
    norm_num
    exact hz3y3_le
  unfold generalPairedPolynomial generalPolynomialMajorant
  dsimp only
  change
    |2 * α + (2 - 10 * α) * z + (-10 + 20 * α) * z * y
        + (20 - 20 * α) * z ^ 2 * y
        + (-20 + 10 * α) * z ^ 2 * y ^ 2
        + (10 - 2 * α) * z ^ 3 * y ^ 2
        - 2 * z ^ 3 * y ^ 3|
      ≤
    |2 * α| + |2 - 10 * α| + |-10 + 20 * α|
      + |20 - 20 * α| + |-20 + 10 * α|
      + |10 - 2 * α| + 2
  rw [abs_le]
  constructor <;>
    nlinarith [
      neg_abs_le (2 * α), le_abs_self (2 * α),
      neg_abs_le ((2 - 10 * α) * z), le_abs_self ((2 - 10 * α) * z),
      neg_abs_le ((-10 + 20 * α) * z * y),
        le_abs_self ((-10 + 20 * α) * z * y),
      neg_abs_le ((20 - 20 * α) * z ^ 2 * y),
        le_abs_self ((20 - 20 * α) * z ^ 2 * y),
      neg_abs_le ((-20 + 10 * α) * z ^ 2 * y ^ 2),
        le_abs_self ((-20 + 10 * α) * z ^ 2 * y ^ 2),
      neg_abs_le ((10 - 2 * α) * z ^ 3 * y ^ 2),
        le_abs_self ((10 - 2 * α) * z ^ 3 * y ^ 2),
      neg_abs_le (2 * z ^ 3 * y ^ 3),
        le_abs_self (2 * z ^ 3 * y ^ 3)]

/--
Uniform prefactor bound under the natural condition `|s| < 1`.
-/
theorem generalPairedSeriesPrefactor_norm_le_of_abs_lt_one
    {ν s x : ℝ} (hν : 0 ≤ ν) (hs : |s| < 1)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖generalPairedSeriesPrefactor ν s x‖
      ≤ generalPolynomialMajorant ν := by
  have hs_bounds := abs_lt.mp hs
  have hs2_le : s ^ 2 ≤ 1 := by
    nlinarith [mul_pos (sub_pos.mpr hs_bounds.2) (by linarith : 0 < 1 + s)]
  have hy0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hy1 : x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hbase0 : 0 ≤ 1 - x ^ 2 := sub_nonneg.mpr hy1
  have hbase1 : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hexp0 : 0 ≤ ν / 2 := div_nonneg hν (by norm_num)
  have hweight0 : 0 ≤ (1 - x ^ 2) ^ (ν / 2) :=
    Real.rpow_nonneg hbase0 _
  have hweight1 : (1 - x ^ 2) ^ (ν / 2) ≤ 1 :=
    Real.rpow_le_one hbase0 hbase1 hexp0
  have hpoly :=
    generalPairedPolynomial_abs_le_majorant
      (ν := ν) (z := s ^ 2) (y := x ^ 2)
      (sq_nonneg s) hs2_le hy0 hy1
  unfold generalPairedSeriesPrefactor
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hweight0,
    abs_of_nonneg hy0]
  calc
    (1 - x ^ 2) ^ (ν / 2) * x ^ 2
          * |generalPairedPolynomial ν (s ^ 2) (x ^ 2)|
        ≤ 1 * 1 * generalPolynomialMajorant ν := by gcongr
    _ = generalPolynomialMajorant ν := by ring

theorem generalPointwiseSeriesTerm_norm_le
    {ν s x : ℝ} (m : ℕ) (hν : 0 ≤ ν) (hs : |s| < 1)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖generalPointwiseSeriesTerm ν s x m‖
      ≤ generalPointwiseMajorant ν s m := by
  have hy0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hy1 : x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hs20 : 0 ≤ s ^ 2 := sq_nonneg s
  have ht0 : 0 ≤ s ^ 2 * x ^ 2 := mul_nonneg hs20 hy0
  have ht_le : s ^ 2 * x ^ 2 ≤ s ^ 2 := by
    nlinarith [mul_nonneg hs20 (sub_nonneg.mpr hy1)]
  have hpow : (s ^ 2 * x ^ 2) ^ m ≤ (s ^ 2) ^ m :=
    pow_le_pow_left₀ ht0 ht_le m
  have hpref :=
    generalPairedSeriesPrefactor_norm_le_of_abs_lt_one hν hs hx
  have hchoose : 0 ≤ ((m + 4).choose 4 : ℝ) := by positivity
  unfold generalPointwiseSeriesTerm generalPointwiseMajorant
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hchoose,
    abs_pow, abs_of_nonneg ht0]
  calc
    ‖generalPairedSeriesPrefactor ν s x‖
          * (((m + 4).choose 4 : ℝ) * (s ^ 2 * x ^ 2) ^ m)
        ≤
      generalPolynomialMajorant ν
          * (((m + 4).choose 4 : ℝ) * (s ^ 2 * x ^ 2) ^ m) := by
            gcongr
    _ ≤
      generalPolynomialMajorant ν
          * (((m + 4).choose 4 : ℝ) * (s ^ 2) ^ m) := by
            gcongr
            exact generalPolynomialMajorant_nonneg ν
    _ =
      generalPolynomialMajorant ν
        * ((m + 4).choose 4 : ℝ) * (s ^ 2) ^ m := by ring

theorem summable_generalPointwiseMajorant
    {ν s : ℝ} (hs : |s| < 1) :
    Summable (generalPointwiseMajorant ν s) := by
  have hs2 : ‖s ^ 2‖ < 1 := by
    simpa using
      (sq_mul_sq_norm_lt_one hs (x := (1 : ℝ)) (by norm_num))
  have h :=
    (summable_choose_four_mul_geometric hs2).mul_left
      (generalPolynomialMajorant ν)
  change Summable
    (fun m =>
      generalPolynomialMajorant ν
        * ((m + 4).choose 4 : ℝ) * (s ^ 2) ^ m)
  simpa only [mul_assoc] using h

/-- Pointwise negative-binomial expansion of the paired general kernel. -/
theorem hasSum_generalPointwiseSeries
    {ν s x : ℝ} (hs : |s| < 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum
      (generalPointwiseSeriesTerm ν s x)
      ((1 - x ^ 2) ^ (ν / 2) * x ^ 2
        * generalPairedPolynomial ν (s ^ 2) (x ^ 2)
        / (1 - s ^ 2 * x ^ 2) ^ 5) := by
  have hxabs : |x| ≤ 1 := by
    rw [abs_of_nonneg hx.1]
    exact hx.2
  have h :=
    (hasSum_paired_denominator hs hxabs).mul_left
      (generalPairedSeriesPrefactor ν s x)
  simpa [generalPointwiseSeriesTerm, generalPairedSeriesPrefactor,
    div_eq_mul_inv] using! h

/--
The general real-power paired-kernel series may be integrated term by term.
-/
theorem hasSum_integral_generalPointwiseSeries
    {ν s : ℝ} (hν : 0 ≤ ν) (hs : |s| < 1) :
    HasSum
      (fun m =>
        ∫ x in (0 : ℝ)..1, generalPointwiseSeriesTerm ν s x m)
      (∫ x in (0 : ℝ)..1,
        (1 - x ^ 2) ^ (ν / 2) * x ^ 2
          * generalPairedPolynomial ν (s ^ 2) (x ^ 2)
          / (1 - s ^ 2 * x ^ 2) ^ 5) := by
  apply hasSum_intervalIntegral_of_uniform_majorant
    (c := generalPointwiseMajorant ν s)
  · intro m
    apply Continuous.continuousOn
    have hweight :
        Continuous (fun x : ℝ => (1 - x ^ 2) ^ (ν / 2)) :=
      (Real.continuous_rpow_const
        (div_nonneg hν (by norm_num))).comp
          (continuous_const.sub (continuous_id.pow 2))
    have hpoly :
        Continuous
          (fun x : ℝ =>
            generalPairedPolynomial ν (s ^ 2) (x ^ 2)) := by
      unfold generalPairedPolynomial
      dsimp only
      fun_prop
    unfold generalPointwiseSeriesTerm generalPairedSeriesPrefactor
    fun_prop
  · intro m x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le] using hx
    exact generalPointwiseSeriesTerm_norm_le m hν hs hx'
  · exact summable_generalPointwiseMajorant hs
  · intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le] using hx
    exact hasSum_generalPointwiseSeries hs hx'

end

end GraybillDeal
