import GraybillDeal.UnequalFixedDifferenceFourRealAlgebra
import GraybillDeal.UnequalFixedDifferenceFourRealMoments

/-!
# Real-parameter series signs for the fixed-difference-four family

This module lifts the coefficient and formal-series sign certificate from a
natural family parameter to an arbitrary real parameter `m ≥ 7`.  The series
index remains natural.

The first three coefficients are explicit rational functions.  Every later
coefficient is a positive beta moment times a strictly negative rational tail
factor.  The numerator signs are supplied by the real polynomial certificate
in `UnequalFixedDifferenceFourCoefficients`.
-/

namespace GraybillDeal

noncomputable section

private theorem unequalFD4RealSeries_cast_three_le
    {n : ℕ} (hn : 3 ≤ n) :
    (3 : ℝ) ≤ (n : ℝ) := by
  exact_mod_cast hn

/-! ## Positive beta moments -/

theorem unequalFixedDifferenceFourRealPlusMoment_pos
    {m : ℝ} (hm : 7 ≤ m) (n : ℕ) :
    0 < unequalFixedDifferenceFourRealPlusMoment m n := by
  unfold unequalFixedDifferenceFourRealPlusMoment
  exact Finset.prod_pos fun i hi => by
    have hiR : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    exact div_pos (by linarith) (by linarith)

theorem unequalFixedDifferenceFourRealMinusMoment_pos
    {m : ℝ} (hm : 7 ≤ m) (n : ℕ) :
    0 < unequalFixedDifferenceFourRealMinusMoment m n := by
  unfold unequalFixedDifferenceFourRealMinusMoment
  exact Finset.prod_pos fun i hi => by
    have hiR : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    exact div_pos (by linarith) (by linarith)

/-! ## Positive denominators -/

def unequalFixedDifferenceFourRealHeadOneDenominator (m : ℝ) : ℝ :=
  32 * m ^ 4 * (2 * m + 1) * (2 * m + 3)
    * unequalFixedDifferenceFourRealD m

def unequalFixedDifferenceFourRealHeadTwoDenominator (m : ℝ) : ℝ :=
  32 * m ^ 4 * (2 * m - 1) * (2 * m + 1) * (2 * m + 3)
    * (2 * m + 5) * unequalFixedDifferenceFourRealD m

def unequalFixedDifferenceFourRealTailProduct (m : ℝ) (n : ℕ) : ℝ :=
  ∏ h ∈ Finset.range 5,
    (2 * m + (n : ℝ) + (h : ℝ))

def unequalFixedDifferenceFourRealPlusTailDenominator
    (m : ℝ) (n : ℕ) : ℝ :=
  480 * m ^ 3 * (2 * m - 1)
    * unequalFixedDifferenceFourRealTailProduct m n
    * unequalFixedDifferenceFourRealD m

def unequalFixedDifferenceFourRealMinusTailDenominator
    (m : ℝ) (n : ℕ) : ℝ :=
  480 * m ^ 4 * (2 * m - 1)
    * unequalFixedDifferenceFourRealTailProduct m n
    * unequalFixedDifferenceFourRealD m

theorem unequalFixedDifferenceFourRealHeadOneDenominator_pos
    {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourRealHeadOneDenominator m := by
  have hD := unequalFixedDifferenceFourRealD_pos hm
  unfold unequalFixedDifferenceFourRealHeadOneDenominator
  positivity

theorem unequalFixedDifferenceFourRealHeadTwoDenominator_pos
    {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourRealHeadTwoDenominator m := by
  have hD := unequalFixedDifferenceFourRealD_pos hm
  have hm0 : 0 < m := by linarith
  have hminus : 0 < 2 * m - 1 := by linarith
  unfold unequalFixedDifferenceFourRealHeadTwoDenominator
  positivity

theorem unequalFixedDifferenceFourRealTailProduct_pos
    {m : ℝ} (hm : 7 ≤ m) (n : ℕ) :
    0 < unequalFixedDifferenceFourRealTailProduct m n := by
  unfold unequalFixedDifferenceFourRealTailProduct
  exact Finset.prod_pos fun h hh => by
    have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hhR : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
    linarith

theorem unequalFixedDifferenceFourRealPlusTailDenominator_pos
    {m : ℝ} (hm : 7 ≤ m) (n : ℕ) :
    0 < unequalFixedDifferenceFourRealPlusTailDenominator m n := by
  have hprod := unequalFixedDifferenceFourRealTailProduct_pos hm n
  have hD := unequalFixedDifferenceFourRealD_pos hm
  have hm0 : 0 < m := by linarith
  have hminus : 0 < 2 * m - 1 := by linarith
  unfold unequalFixedDifferenceFourRealPlusTailDenominator
  positivity

theorem unequalFixedDifferenceFourRealMinusTailDenominator_pos
    {m : ℝ} (hm : 7 ≤ m) (n : ℕ) :
    0 < unequalFixedDifferenceFourRealMinusTailDenominator m n := by
  have hprod := unequalFixedDifferenceFourRealTailProduct_pos hm n
  have hD := unequalFixedDifferenceFourRealD_pos hm
  have hm0 : 0 < m := by linarith
  have hminus : 0 < 2 * m - 1 := by linarith
  unfold unequalFixedDifferenceFourRealMinusTailDenominator
  positivity

/-! ## Strictly negative tail factors -/

def unequalFixedDifferenceFourRealPlusTailFactor
    (m : ℝ) (n : ℕ) : ℝ :=
  -((m - 1) * ((n : ℝ) + 1) * ((n : ℝ) + 2)
      * unequalFD4TailPlus m (n : ℝ))
    / unequalFixedDifferenceFourRealPlusTailDenominator m n

def unequalFixedDifferenceFourRealMinusTailFactor
    (m : ℝ) (n : ℕ) : ℝ :=
  -((m + 1) * ((n : ℝ) + 1) * ((n : ℝ) + 2)
      * unequalFD4TailMinus m (n : ℝ))
    / unequalFixedDifferenceFourRealMinusTailDenominator m n

theorem unequalFixedDifferenceFourRealPlusTailFactor_neg
    {m : ℝ} {n : ℕ} (hm : 7 ≤ m) (hn : 3 ≤ n) :
    unequalFixedDifferenceFourRealPlusTailFactor m n < 0 := by
  have hnR := unequalFD4RealSeries_cast_three_le hn
  have hpoly : 0 < unequalFD4TailPlus m (n : ℝ) :=
    unequalFD4TailPlus_pos hm hnR
  have hnum :
      0 <
        (m - 1) * ((n : ℝ) + 1) * ((n : ℝ) + 2)
          * unequalFD4TailPlus m (n : ℝ) := by
    exact mul_pos
      (mul_pos
        (mul_pos (by linarith) (by linarith))
        (by linarith))
      hpoly
  unfold unequalFixedDifferenceFourRealPlusTailFactor
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum)
    (unequalFixedDifferenceFourRealPlusTailDenominator_pos hm n)

theorem unequalFixedDifferenceFourRealMinusTailFactor_neg
    {m : ℝ} {n : ℕ} (hm : 7 ≤ m) (hn : 3 ≤ n) :
    unequalFixedDifferenceFourRealMinusTailFactor m n < 0 := by
  have hnR := unequalFD4RealSeries_cast_three_le hn
  have hpoly : 0 < unequalFD4TailMinus m (n : ℝ) :=
    unequalFD4TailMinus_pos hm hnR
  have hnum :
      0 <
        (m + 1) * ((n : ℝ) + 1) * ((n : ℝ) + 2)
          * unequalFD4TailMinus m (n : ℝ) := by
    exact mul_pos
      (mul_pos
        (mul_pos (by linarith) (by linarith))
        (by linarith))
      hpoly
  unfold unequalFixedDifferenceFourRealMinusTailFactor
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum)
    (unequalFixedDifferenceFourRealMinusTailDenominator_pos hm n)

/-! ## The two coefficient sequences -/

def unequalFixedDifferenceFourRealPlusCoeff (m : ℝ) : ℕ → ℝ
  | 0 => -unequalFixedDifferenceFourRealB0 m
  | 1 =>
      -unequalFD4HeadPlusOne m
        / unequalFixedDifferenceFourRealHeadOneDenominator m
  | 2 =>
      -unequalFD4HeadPlusTwo m
        / unequalFixedDifferenceFourRealHeadTwoDenominator m
  | n + 3 =>
      unequalFixedDifferenceFourRealPlusMoment m (n + 3)
        * unequalFixedDifferenceFourRealPlusTailFactor m (n + 3)

def unequalFixedDifferenceFourRealMinusCoeff (m : ℝ) : ℕ → ℝ
  | 0 => -unequalFixedDifferenceFourRealB0 m
  | 1 =>
      -unequalFD4HeadMinusOne m
        / unequalFixedDifferenceFourRealHeadOneDenominator m
  | 2 =>
      -unequalFD4HeadMinusTwo m
        / unequalFixedDifferenceFourRealHeadTwoDenominator m
  | n + 3 =>
      unequalFixedDifferenceFourRealMinusMoment m (n + 3)
        * unequalFixedDifferenceFourRealMinusTailFactor m (n + 3)

@[simp]
theorem unequalFixedDifferenceFourRealPlusCoeff_zero (m : ℝ) :
    unequalFixedDifferenceFourRealPlusCoeff m 0
      = -unequalFixedDifferenceFourRealB0 m := by
  rfl

@[simp]
theorem unequalFixedDifferenceFourRealMinusCoeff_zero (m : ℝ) :
    unequalFixedDifferenceFourRealMinusCoeff m 0
      = -unequalFixedDifferenceFourRealB0 m := by
  rfl

theorem unequalFixedDifferenceFourRealPlusCoeff_neg
    {m : ℝ} (hm : 7 ≤ m) :
    ∀ n : ℕ, unequalFixedDifferenceFourRealPlusCoeff m n < 0
  | 0 => by
      simp only [unequalFixedDifferenceFourRealPlusCoeff]
      exact neg_neg_of_pos (unequalFixedDifferenceFourRealB0_pos hm)
  | 1 => by
      simp only [unequalFixedDifferenceFourRealPlusCoeff]
      exact div_neg_of_neg_of_pos
        (neg_neg_of_pos (unequalFD4HeadPlusOne_pos hm))
        (unequalFixedDifferenceFourRealHeadOneDenominator_pos hm)
  | 2 => by
      simp only [unequalFixedDifferenceFourRealPlusCoeff]
      exact div_neg_of_neg_of_pos
        (neg_neg_of_pos (unequalFD4HeadPlusTwo_pos hm))
        (unequalFixedDifferenceFourRealHeadTwoDenominator_pos hm)
  | n + 3 => by
      simp only [unequalFixedDifferenceFourRealPlusCoeff]
      exact mul_neg_of_pos_of_neg
        (unequalFixedDifferenceFourRealPlusMoment_pos hm (n + 3))
        (unequalFixedDifferenceFourRealPlusTailFactor_neg hm (by omega))

theorem unequalFixedDifferenceFourRealMinusCoeff_neg
    {m : ℝ} (hm : 7 ≤ m) :
    ∀ n : ℕ, unequalFixedDifferenceFourRealMinusCoeff m n < 0
  | 0 => by
      simp only [unequalFixedDifferenceFourRealMinusCoeff]
      exact neg_neg_of_pos (unequalFixedDifferenceFourRealB0_pos hm)
  | 1 => by
      simp only [unequalFixedDifferenceFourRealMinusCoeff]
      exact div_neg_of_neg_of_pos
        (neg_neg_of_pos (unequalFD4HeadMinusOne_pos hm))
        (unequalFixedDifferenceFourRealHeadOneDenominator_pos hm)
  | 2 => by
      simp only [unequalFixedDifferenceFourRealMinusCoeff]
      exact div_neg_of_neg_of_pos
        (neg_neg_of_pos (unequalFD4HeadMinusTwo_pos hm))
        (unequalFixedDifferenceFourRealHeadTwoDenominator_pos hm)
  | n + 3 => by
      simp only [unequalFixedDifferenceFourRealMinusCoeff]
      exact mul_neg_of_pos_of_neg
        (unequalFixedDifferenceFourRealMinusMoment_pos hm (n + 3))
        (unequalFixedDifferenceFourRealMinusTailFactor_neg hm (by omega))

/-! ## Uniform bounds for the formal power series -/

def unequalFixedDifferenceFourRealPlusSeriesTerm
    (m s : ℝ) (n : ℕ) : ℝ :=
  unequalFixedDifferenceFourRealPlusCoeff m n * s ^ n

def unequalFixedDifferenceFourRealMinusSeriesTerm
    (m s : ℝ) (n : ℕ) : ℝ :=
  unequalFixedDifferenceFourRealMinusCoeff m n * s ^ n

def unequalFixedDifferenceFourRealPlusSeries (m s : ℝ) : ℝ :=
  ∑' n : ℕ, unequalFixedDifferenceFourRealPlusSeriesTerm m s n

def unequalFixedDifferenceFourRealMinusSeries (m s : ℝ) : ℝ :=
  ∑' n : ℕ, unequalFixedDifferenceFourRealMinusSeriesTerm m s n

theorem unequalFixedDifferenceFourRealPlusSeriesTerm_nonpos
    {m : ℝ} (hm : 7 ≤ m) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    unequalFixedDifferenceFourRealPlusSeriesTerm m s n ≤ 0 := by
  unfold unequalFixedDifferenceFourRealPlusSeriesTerm
  exact mul_nonpos_of_nonpos_of_nonneg
    (unequalFixedDifferenceFourRealPlusCoeff_neg hm n).le
    (pow_nonneg hs n)

theorem unequalFixedDifferenceFourRealMinusSeriesTerm_nonpos
    {m : ℝ} (hm : 7 ≤ m) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    unequalFixedDifferenceFourRealMinusSeriesTerm m s n ≤ 0 := by
  unfold unequalFixedDifferenceFourRealMinusSeriesTerm
  exact mul_nonpos_of_nonpos_of_nonneg
    (unequalFixedDifferenceFourRealMinusCoeff_neg hm n).le
    (pow_nonneg hs n)

theorem unequalFixedDifferenceFourRealPlusSeries_le_neg_b0
    {m : ℝ} (hm : 7 ≤ m) {s : ℝ} (hs : 0 ≤ s)
    (hsum : Summable (unequalFixedDifferenceFourRealPlusSeriesTerm m s)) :
    unequalFixedDifferenceFourRealPlusSeries m s
      ≤ -unequalFixedDifferenceFourRealB0 m := by
  unfold unequalFixedDifferenceFourRealPlusSeries
  calc
    (∑' n : ℕ, unequalFixedDifferenceFourRealPlusSeriesTerm m s n)
        ≤ unequalFixedDifferenceFourRealPlusSeriesTerm m s 0 :=
      tsum_le_zero_term_of_nonpos hsum
        (unequalFixedDifferenceFourRealPlusSeriesTerm_nonpos hm hs)
    _ = -unequalFixedDifferenceFourRealB0 m := by
      simp [unequalFixedDifferenceFourRealPlusSeriesTerm]

theorem unequalFixedDifferenceFourRealMinusSeries_le_neg_b0
    {m : ℝ} (hm : 7 ≤ m) {s : ℝ} (hs : 0 ≤ s)
    (hsum : Summable (unequalFixedDifferenceFourRealMinusSeriesTerm m s)) :
    unequalFixedDifferenceFourRealMinusSeries m s
      ≤ -unequalFixedDifferenceFourRealB0 m := by
  unfold unequalFixedDifferenceFourRealMinusSeries
  calc
    (∑' n : ℕ, unequalFixedDifferenceFourRealMinusSeriesTerm m s n)
        ≤ unequalFixedDifferenceFourRealMinusSeriesTerm m s 0 :=
      tsum_le_zero_term_of_nonpos hsum
        (unequalFixedDifferenceFourRealMinusSeriesTerm_nonpos hm hs)
    _ = -unequalFixedDifferenceFourRealB0 m := by
      simp [unequalFixedDifferenceFourRealMinusSeriesTerm]

theorem unequalFixedDifferenceFourRealPlusSeries_neg
    {m : ℝ} (hm : 7 ≤ m) {s : ℝ} (hs : 0 ≤ s)
    (hsum : Summable (unequalFixedDifferenceFourRealPlusSeriesTerm m s)) :
    unequalFixedDifferenceFourRealPlusSeries m s < 0 :=
  (unequalFixedDifferenceFourRealPlusSeries_le_neg_b0 hm hs hsum).trans_lt
    (neg_neg_of_pos (unequalFixedDifferenceFourRealB0_pos hm))

theorem unequalFixedDifferenceFourRealMinusSeries_neg
    {m : ℝ} (hm : 7 ≤ m) {s : ℝ} (hs : 0 ≤ s)
    (hsum : Summable (unequalFixedDifferenceFourRealMinusSeriesTerm m s)) :
    unequalFixedDifferenceFourRealMinusSeries m s < 0 :=
  (unequalFixedDifferenceFourRealMinusSeries_le_neg_b0 hm hs hsum).trans_lt
    (neg_neg_of_pos (unequalFixedDifferenceFourRealB0_pos hm))

end

end GraybillDeal
