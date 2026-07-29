import GraybillDeal.UnequalFixedDifferenceFourCollectedAlgebra
import GraybillDeal.UnequalFixedDifferenceFourRealSeriesBridge
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp

/-!
# Real-parameter collected coefficient algebra

This module identifies the polynomial-moment coefficients in the
fixed-difference-four series with the real-parameter coefficient sequences.
The analytic family parameter is real, while the power-series index remains
natural.
-/

namespace GraybillDeal

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! ## Finite-shift recurrences for the two beta moments -/

def unequalFixedDifferenceFourRealPlusMomentRatio
    (m : ℝ) (n j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j,
    (m + 1 + ((n + i : ℕ) : ℝ))
      / (2 * m + ((n + i : ℕ) : ℝ))

def unequalFixedDifferenceFourRealMinusMomentRatio
    (m : ℝ) (n j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j,
    (m - 1 + ((n + i : ℕ) : ℝ))
      / (2 * m + ((n + i : ℕ) : ℝ))

theorem unequalFixedDifferenceFourRealPlusMoment_add
    (m : ℝ) (n j : ℕ) :
    unequalFixedDifferenceFourRealPlusMoment m (n + j)
      =
    unequalFixedDifferenceFourRealPlusMoment m n
      * unequalFixedDifferenceFourRealPlusMomentRatio m n j := by
  unfold unequalFixedDifferenceFourRealPlusMoment
    unequalFixedDifferenceFourRealPlusMomentRatio
  rw [Finset.prod_range_add]

theorem unequalFixedDifferenceFourRealMinusMoment_add
    (m : ℝ) (n j : ℕ) :
    unequalFixedDifferenceFourRealMinusMoment m (n + j)
      =
    unequalFixedDifferenceFourRealMinusMoment m n
      * unequalFixedDifferenceFourRealMinusMomentRatio m n j := by
  unfold unequalFixedDifferenceFourRealMinusMoment
    unequalFixedDifferenceFourRealMinusMomentRatio
  rw [Finset.prod_range_add]

macro "unequal_fd4_expand_real_plus_moment_ratios" : tactic =>
  `(tactic|
    (unfold unequalFixedDifferenceFourRealPlusMomentRatio
     norm_num [Finset.prod_range_succ]
     push_cast))

macro "unequal_fd4_expand_real_minus_moment_ratios" : tactic =>
  `(tactic|
    (unfold unequalFixedDifferenceFourRealMinusMomentRatio
     norm_num [Finset.prod_range_succ]
     push_cast))

/-! ## Normalized polynomial identities -/

/--
Before separating the three exceptional head coefficients, the right-chart
polynomial coefficient is its beta moment times the certified tail factor.
-/
theorem
    unequalFixedDifferenceFourRealPlusPolynomialCoefficient_eq_moment_mul
    {m : ℝ} (hm : 7 ≤ m) (n : ℕ) :
    unequalFixedDifferenceFourRealPlusPolynomialCoefficient m n
      =
    unequalFixedDifferenceFourRealPlusMoment m n
      * unequalFixedDifferenceFourRealPlusTailFactor m n := by
  have hm0 : m ≠ 0 := by linarith
  have h2m1 : 2 * m - 1 ≠ 0 := by linarith
  have hD : unequalFixedDifferenceFourRealD m ≠ 0 :=
    (unequalFixedDifferenceFourRealD_pos hm).ne'
  have hden (a : ℕ) :
      2 * m + (n : ℝ) + (a : ℝ) ≠ 0 := by
    positivity
  unfold unequalFixedDifferenceFourRealPlusPolynomialCoefficient
  rw [unequalFD4PolynomialMoment_G0, unequalFD4PolynomialMoment_G1,
    unequalFD4PolynomialMoment_G2, unequalFD4PolynomialMoment_G3]
  rw [
    unequalFixedDifferenceFourRealPlusMoment_add m n 1,
    unequalFixedDifferenceFourRealPlusMoment_add m n 2,
    unequalFixedDifferenceFourRealPlusMoment_add m n 3,
    unequalFixedDifferenceFourRealPlusMoment_add m n 4,
    unequalFixedDifferenceFourRealPlusMoment_add m n 5]
  rw [unequalFD4_cast_choose_five_poly (n + 5),
    unequalFD4_cast_choose_five_poly (n + 4),
    unequalFD4_cast_choose_five_poly (n + 3),
    unequalFD4_cast_choose_five_poly (n + 2)]
  unequal_fd4_expand_real_plus_moment_ratios
  unfold unequalFD4G1H1 unequalFD4G1H2
    unequalFD4G2H0 unequalFD4G2H1 unequalFD4G2H2
  unfold unequalFixedDifferenceFourRealT
    unequalFixedDifferenceFourRealQ
    unequalFixedDifferenceFourRealKappa
    unequalFixedDifferenceFourRealC
    unequalFixedDifferenceFourRealK
    unequalFixedDifferenceFourRealPlusTailFactor
    unequalFixedDifferenceFourRealPlusTailDenominator
    unequalFixedDifferenceFourRealTailProduct
    unequalFD4TailPlus unequalFD4TailPlusShift
    unequalFD4TailPlusA0 unequalFD4TailPlusA1
    unequalFD4TailPlusA2 unequalFD4TailPlusA3
    unequalFD4TailPlusA4 unequalFD4TailPlusA5
  norm_num [Finset.prod_range_succ]
  push_cast
  field_simp [hm0, h2m1, hD,
    hden 0, hden 1, hden 2, hden 3, hden 4,
    hden 5, hden 6, hden 7, hden 8, hden 9]
  unfold unequalFixedDifferenceFourRealD
  ring

/-- Swapped-chart counterpart of the normalized polynomial identity. -/
theorem
    unequalFixedDifferenceFourRealMinusPolynomialCoefficient_eq_moment_mul
    {m : ℝ} (hm : 7 ≤ m) (n : ℕ) :
    unequalFixedDifferenceFourRealMinusPolynomialCoefficient m n
      =
    unequalFixedDifferenceFourRealMinusMoment m n
      * unequalFixedDifferenceFourRealMinusTailFactor m n := by
  have hm0 : m ≠ 0 := by linarith
  have h2m1 : 2 * m - 1 ≠ 0 := by linarith
  have hD : unequalFixedDifferenceFourRealD m ≠ 0 :=
    (unequalFixedDifferenceFourRealD_pos hm).ne'
  have hden (a : ℕ) :
      2 * m + (n : ℝ) + (a : ℝ) ≠ 0 := by
    positivity
  unfold unequalFixedDifferenceFourRealMinusPolynomialCoefficient
  rw [unequalFD4PolynomialMoment_G0, unequalFD4PolynomialMoment_G1,
    unequalFD4PolynomialMoment_G2, unequalFD4PolynomialMoment_G3]
  rw [
    unequalFixedDifferenceFourRealMinusMoment_add m n 1,
    unequalFixedDifferenceFourRealMinusMoment_add m n 2,
    unequalFixedDifferenceFourRealMinusMoment_add m n 3,
    unequalFixedDifferenceFourRealMinusMoment_add m n 4,
    unequalFixedDifferenceFourRealMinusMoment_add m n 5]
  rw [unequalFD4_cast_choose_five_poly (n + 5),
    unequalFD4_cast_choose_five_poly (n + 4),
    unequalFD4_cast_choose_five_poly (n + 3),
    unequalFD4_cast_choose_five_poly (n + 2)]
  unequal_fd4_expand_real_minus_moment_ratios
  unfold unequalFD4G1H1 unequalFD4G1H2
    unequalFD4G2H0 unequalFD4G2H1 unequalFD4G2H2
  unfold unequalFixedDifferenceFourRealT
    unequalFixedDifferenceFourRealQ
    unequalFixedDifferenceFourRealKappa
    unequalFixedDifferenceFourRealC
    unequalFixedDifferenceFourRealK
    unequalFixedDifferenceFourRealMinusTailFactor
    unequalFixedDifferenceFourRealMinusTailDenominator
    unequalFixedDifferenceFourRealTailProduct
    unequalFD4TailMinus unequalFD4TailMinusShift
    unequalFD4TailMinusA0 unequalFD4TailMinusA1
    unequalFD4TailMinusA2 unequalFD4TailMinusA3
    unequalFD4TailMinusA4 unequalFD4TailMinusA5
  norm_num [Finset.prod_range_succ]
  push_cast
  field_simp [hm0, h2m1, hD,
    hden 0, hden 1, hden 2, hden 3, hden 4,
    hden 5, hden 6, hden 7, hden 8, hden 9]
  unfold unequalFixedDifferenceFourRealD
  ring

/-! ## Exceptional head coefficients -/

macro "unequal_fd4_unfold_real_plus_head_data" : tactic =>
  `(tactic|
    (simp only [unequalFixedDifferenceFourRealPlusMoment,
      unequalFixedDifferenceFourRealPlusTailFactor,
      unequalFixedDifferenceFourRealPlusTailDenominator,
      unequalFixedDifferenceFourRealTailProduct,
      unequalFixedDifferenceFourRealHeadOneDenominator,
      unequalFixedDifferenceFourRealHeadTwoDenominator,
      unequalFixedDifferenceFourRealB0,
      unequalFD4HeadPlusOne, unequalFD4HeadPlusTwo,
      unequalFD4TailPlus, unequalFD4TailPlusShift,
      unequalFD4TailPlusA0, unequalFD4TailPlusA1,
      unequalFD4TailPlusA2, unequalFD4TailPlusA3,
      unequalFD4TailPlusA4, unequalFD4TailPlusA5]))

macro "unequal_fd4_unfold_real_minus_head_data" : tactic =>
  `(tactic|
    (simp only [unequalFixedDifferenceFourRealMinusMoment,
      unequalFixedDifferenceFourRealMinusTailFactor,
      unequalFixedDifferenceFourRealMinusTailDenominator,
      unequalFixedDifferenceFourRealTailProduct,
      unequalFixedDifferenceFourRealHeadOneDenominator,
      unequalFixedDifferenceFourRealHeadTwoDenominator,
      unequalFixedDifferenceFourRealB0,
      unequalFD4HeadMinusOne, unequalFD4HeadMinusTwo,
      unequalFD4TailMinus, unequalFD4TailMinusShift,
      unequalFD4TailMinusA0, unequalFD4TailMinusA1,
      unequalFD4TailMinusA2, unequalFD4TailMinusA3,
      unequalFD4TailMinusA4, unequalFD4TailMinusA5]))

theorem unequalFixedDifferenceFourRealPlusHeadZero
    {m : ℝ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourRealPlusMoment m 0
        * unequalFixedDifferenceFourRealPlusTailFactor m 0
      =
    unequalFixedDifferenceFourRealPlusCoeff m 0 := by
  have hm0 : m ≠ 0 := by linarith
  have h2m1 : 2 * m - 1 ≠ 0 := by linarith
  have h2m1' : -1 + m * 2 ≠ 0 := by linarith
  have hD : unequalFixedDifferenceFourRealD m ≠ 0 :=
    (unequalFixedDifferenceFourRealD_pos hm).ne'
  have hadd (a : ℕ) :
      2 * m + (a : ℝ) ≠ 0 := by
    have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  simp only [unequalFixedDifferenceFourRealPlusCoeff]
  unequal_fd4_unfold_real_plus_head_data
  norm_num [Finset.prod_range_succ]
  push_cast
  field_simp [hm0, h2m1, hD,
    hadd 0, hadd 1, hadd 2, hadd 3, hadd 4]
  ring_nf <;> field_simp [h2m1, h2m1'] <;> ring

theorem unequalFixedDifferenceFourRealPlusHeadOne
    {m : ℝ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourRealPlusMoment m 1
        * unequalFixedDifferenceFourRealPlusTailFactor m 1
      =
    unequalFixedDifferenceFourRealPlusCoeff m 1 := by
  have hm0 : m ≠ 0 := by linarith
  have h2m1 : 2 * m - 1 ≠ 0 := by linarith
  have h2m1' : -1 + m * 2 ≠ 0 := by linarith
  have hD : unequalFixedDifferenceFourRealD m ≠ 0 :=
    (unequalFixedDifferenceFourRealD_pos hm).ne'
  have hadd (a : ℕ) :
      2 * m + (a : ℝ) ≠ 0 := by
    have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  simp only [unequalFixedDifferenceFourRealPlusCoeff]
  unequal_fd4_unfold_real_plus_head_data
  norm_num [Finset.prod_range_succ]
  push_cast
  field_simp [hm0, h2m1, hD,
    hadd 0, hadd 1, hadd 2, hadd 3, hadd 4, hadd 5]
  ring_nf <;> field_simp [h2m1, h2m1'] <;> ring

theorem unequalFixedDifferenceFourRealPlusHeadTwo
    {m : ℝ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourRealPlusMoment m 2
        * unequalFixedDifferenceFourRealPlusTailFactor m 2
      =
    unequalFixedDifferenceFourRealPlusCoeff m 2 := by
  have hm0 : m ≠ 0 := by linarith
  have h2m1 : 2 * m - 1 ≠ 0 := by linarith
  have h2m1' : -1 + m * 2 ≠ 0 := by linarith
  have hD : unequalFixedDifferenceFourRealD m ≠ 0 :=
    (unequalFixedDifferenceFourRealD_pos hm).ne'
  have hadd (a : ℕ) :
      2 * m + (a : ℝ) ≠ 0 := by
    have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  simp only [unequalFixedDifferenceFourRealPlusCoeff]
  unequal_fd4_unfold_real_plus_head_data
  norm_num [Finset.prod_range_succ]
  push_cast
  field_simp [hm0, h2m1, hD,
    hadd 0, hadd 1, hadd 2, hadd 3, hadd 4, hadd 5, hadd 6]
  ring_nf <;> field_simp [h2m1, h2m1'] <;> ring

theorem unequalFixedDifferenceFourRealMinusHeadZero
    {m : ℝ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourRealMinusMoment m 0
        * unequalFixedDifferenceFourRealMinusTailFactor m 0
      =
    unequalFixedDifferenceFourRealMinusCoeff m 0 := by
  have hm0 : m ≠ 0 := by linarith
  have h2m1 : 2 * m - 1 ≠ 0 := by linarith
  have h2m1' : -1 + m * 2 ≠ 0 := by linarith
  have hD : unequalFixedDifferenceFourRealD m ≠ 0 :=
    (unequalFixedDifferenceFourRealD_pos hm).ne'
  have hadd (a : ℕ) :
      2 * m + (a : ℝ) ≠ 0 := by
    have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  simp only [unequalFixedDifferenceFourRealMinusCoeff]
  unequal_fd4_unfold_real_minus_head_data
  norm_num [Finset.prod_range_succ]
  push_cast
  field_simp [hm0, h2m1, hD,
    hadd 0, hadd 1, hadd 2, hadd 3, hadd 4]
  ring_nf <;> field_simp [h2m1, h2m1'] <;> ring

theorem unequalFixedDifferenceFourRealMinusHeadOne
    {m : ℝ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourRealMinusMoment m 1
        * unequalFixedDifferenceFourRealMinusTailFactor m 1
      =
    unequalFixedDifferenceFourRealMinusCoeff m 1 := by
  have hm0 : m ≠ 0 := by linarith
  have h2m1 : 2 * m - 1 ≠ 0 := by linarith
  have h2m1' : -1 + m * 2 ≠ 0 := by linarith
  have hD : unequalFixedDifferenceFourRealD m ≠ 0 :=
    (unequalFixedDifferenceFourRealD_pos hm).ne'
  have hadd (a : ℕ) :
      2 * m + (a : ℝ) ≠ 0 := by
    have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  simp only [unequalFixedDifferenceFourRealMinusCoeff]
  unequal_fd4_unfold_real_minus_head_data
  norm_num [Finset.prod_range_succ]
  push_cast
  field_simp [hm0, h2m1, hD,
    hadd 0, hadd 1, hadd 2, hadd 3, hadd 4, hadd 5]
  ring_nf <;> field_simp [h2m1, h2m1'] <;> ring

theorem unequalFixedDifferenceFourRealMinusHeadTwo
    {m : ℝ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourRealMinusMoment m 2
        * unequalFixedDifferenceFourRealMinusTailFactor m 2
      =
    unequalFixedDifferenceFourRealMinusCoeff m 2 := by
  have hm0 : m ≠ 0 := by linarith
  have h2m1 : 2 * m - 1 ≠ 0 := by linarith
  have h2m1' : -1 + m * 2 ≠ 0 := by linarith
  have hD : unequalFixedDifferenceFourRealD m ≠ 0 :=
    (unequalFixedDifferenceFourRealD_pos hm).ne'
  have hadd (a : ℕ) :
      2 * m + (a : ℝ) ≠ 0 := by
    have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  simp only [unequalFixedDifferenceFourRealMinusCoeff]
  unequal_fd4_unfold_real_minus_head_data
  norm_num [Finset.prod_range_succ]
  push_cast
  field_simp [hm0, h2m1, hD,
    hadd 0, hadd 1, hadd 2, hadd 3, hadd 4, hadd 5, hadd 6]
  ring_nf <;> field_simp [h2m1, h2m1'] <;> ring

/-! ## Identification with the certified coefficient sequences -/

theorem unequalFixedDifferenceFourRealPlusPolynomialCoefficient_eq_coeff
    {m : ℝ} (hm : 7 ≤ m) :
    ∀ n : ℕ,
      unequalFixedDifferenceFourRealPlusPolynomialCoefficient m n
        = unequalFixedDifferenceFourRealPlusCoeff m n
  | 0 =>
      (unequalFixedDifferenceFourRealPlusPolynomialCoefficient_eq_moment_mul
        hm 0).trans
        (unequalFixedDifferenceFourRealPlusHeadZero hm)
  | 1 =>
      (unequalFixedDifferenceFourRealPlusPolynomialCoefficient_eq_moment_mul
        hm 1).trans
        (unequalFixedDifferenceFourRealPlusHeadOne hm)
  | 2 =>
      (unequalFixedDifferenceFourRealPlusPolynomialCoefficient_eq_moment_mul
        hm 2).trans
        (unequalFixedDifferenceFourRealPlusHeadTwo hm)
  | n + 3 => by
      rw [
        unequalFixedDifferenceFourRealPlusPolynomialCoefficient_eq_moment_mul
          hm (n + 3)]
      rfl

theorem unequalFixedDifferenceFourRealMinusPolynomialCoefficient_eq_coeff
    {m : ℝ} (hm : 7 ≤ m) :
    ∀ n : ℕ,
      unequalFixedDifferenceFourRealMinusPolynomialCoefficient m n
        = unequalFixedDifferenceFourRealMinusCoeff m n
  | 0 =>
      (unequalFixedDifferenceFourRealMinusPolynomialCoefficient_eq_moment_mul
        hm 0).trans
        (unequalFixedDifferenceFourRealMinusHeadZero hm)
  | 1 =>
      (unequalFixedDifferenceFourRealMinusPolynomialCoefficient_eq_moment_mul
        hm 1).trans
        (unequalFixedDifferenceFourRealMinusHeadOne hm)
  | 2 =>
      (unequalFixedDifferenceFourRealMinusPolynomialCoefficient_eq_moment_mul
        hm 2).trans
        (unequalFixedDifferenceFourRealMinusHeadTwo hm)
  | n + 3 => by
      rw [
        unequalFixedDifferenceFourRealMinusPolynomialCoefficient_eq_moment_mul
          hm (n + 3)]
      rfl

theorem unequalFixedDifferenceFourRealPlusIntegratedCoefficient_eq_coeff
    {m : ℝ} (hm : 7 ≤ m) (n : ℕ) :
    unequalDampedIntegratedCoefficient
        (unequalFixedDifferenceFourRealPlusDensity m)
        (unequalFixedDifferenceFourRealT m)
        (unequalFixedDifferenceFourRealQ m)
        (unequalFixedDifferenceFourRealKappa m)
        (unequalFixedDifferenceFourRealC m)
        (unequalFixedDifferenceFourRealK m) n
      =
    unequalFixedDifferenceFourRealPlusCoeff m n := by
  exact
    (unequalFixedDifferenceFourRealPlusIntegratedCoefficient_eq_polynomial
      hm n).trans
      (unequalFixedDifferenceFourRealPlusPolynomialCoefficient_eq_coeff hm n)

theorem unequalFixedDifferenceFourRealMinusIntegratedCoefficient_eq_coeff
    {m : ℝ} (hm : 7 ≤ m) (n : ℕ) :
    unequalDampedIntegratedCoefficient
        (unequalFixedDifferenceFourRealMinusDensity m)
        (unequalFixedDifferenceFourRealQ m)
        (unequalFixedDifferenceFourRealT m)
        (-unequalFixedDifferenceFourRealKappa m)
        (unequalFixedDifferenceFourRealC m)
        (unequalFixedDifferenceFourRealK m) n
      =
    unequalFixedDifferenceFourRealMinusCoeff m n := by
  exact
    (unequalFixedDifferenceFourRealMinusIntegratedCoefficient_eq_polynomial
      hm n).trans
      (unequalFixedDifferenceFourRealMinusPolynomialCoefficient_eq_coeff hm n)

end

end GraybillDeal
