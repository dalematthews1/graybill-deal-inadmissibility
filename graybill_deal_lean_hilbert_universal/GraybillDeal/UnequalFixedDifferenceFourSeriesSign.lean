import GraybillDeal.UnequalDampedSeriesSign
import GraybillDeal.UnequalFixedDifferenceFourAlgebra
import GraybillDeal.UnequalFixedDifferenceFourCoefficients

/-!
# Series signs for the fixed-difference-four family

This file packages the finite polynomial certificate into two coefficient
sequences for

`(n₁, n₂) = (2m - 1, 2m + 3)`, `m ≥ 7`.

The first three coefficients are the explicit rational functions from the
analytic calculation.  Every later coefficient is a positive beta moment
times a strictly negative rational tail factor.  The probability-integral
identification is deliberately left to a later module.
-/

namespace GraybillDeal

noncomputable section

private theorem unequalFD4_cast_seven_le
    {m : ℕ} (hm : 7 ≤ m) :
    (7 : ℝ) ≤ (m : ℝ) := by
  exact_mod_cast hm

private theorem unequalFD4_cast_three_le
    {n : ℕ} (hn : 3 ≤ n) :
    (3 : ℝ) ≤ (n : ℝ) := by
  exact_mod_cast hn

/-! ## Positive beta moments -/

/-- The `n`th raw moment of the right-chart `Beta(m+1,m-1)` law. -/
def unequalFixedDifferenceFourPlusMoment (m n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n,
    ((m : ℝ) + 1 + (i : ℝ))
      / (2 * (m : ℝ) + (i : ℝ))

/-- The `n`th raw moment of the left-chart `Beta(m-1,m+1)` law. -/
def unequalFixedDifferenceFourMinusMoment (m n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n,
    ((m : ℝ) - 1 + (i : ℝ))
      / (2 * (m : ℝ) + (i : ℝ))

theorem unequalFixedDifferenceFourPlusMoment_pos
    {m : ℕ} (hm : 7 ≤ m) (n : ℕ) :
    0 < unequalFixedDifferenceFourPlusMoment m n := by
  have hmR := unequalFD4_cast_seven_le hm
  unfold unequalFixedDifferenceFourPlusMoment
  exact Finset.prod_pos fun i hi => by
    have hiR : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    exact div_pos (by linarith) (by linarith)

theorem unequalFixedDifferenceFourMinusMoment_pos
    {m : ℕ} (hm : 7 ≤ m) (n : ℕ) :
    0 < unequalFixedDifferenceFourMinusMoment m n := by
  have hmR := unequalFD4_cast_seven_le hm
  unfold unequalFixedDifferenceFourMinusMoment
  exact Finset.prod_pos fun i hi => by
    have hiR : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    exact div_pos (by linarith) (by linarith)

/-! ## Positive denominators -/

def unequalFixedDifferenceFourHeadOneDenominator (m : ℕ) : ℝ :=
  32 * (m : ℝ) ^ 4
    * (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 3)
    * unequalFixedDifferenceFourD m

def unequalFixedDifferenceFourHeadTwoDenominator (m : ℕ) : ℝ :=
  32 * (m : ℝ) ^ 4
    * (2 * (m : ℝ) - 1)
    * (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 3)
    * (2 * (m : ℝ) + 5)
    * unequalFixedDifferenceFourD m

def unequalFixedDifferenceFourTailProduct (m n : ℕ) : ℝ :=
  ∏ h ∈ Finset.range 5,
    (2 * (m : ℝ) + (n : ℝ) + (h : ℝ))

def unequalFixedDifferenceFourPlusTailDenominator
    (m n : ℕ) : ℝ :=
  480 * (m : ℝ) ^ 3
    * (2 * (m : ℝ) - 1)
    * unequalFixedDifferenceFourTailProduct m n
    * unequalFixedDifferenceFourD m

def unequalFixedDifferenceFourMinusTailDenominator
    (m n : ℕ) : ℝ :=
  480 * (m : ℝ) ^ 4
    * (2 * (m : ℝ) - 1)
    * unequalFixedDifferenceFourTailProduct m n
    * unequalFixedDifferenceFourD m

theorem unequalFixedDifferenceFourHeadOneDenominator_pos
    {m : ℕ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourHeadOneDenominator m := by
  have hmR := unequalFD4_cast_seven_le hm
  have hD := unequalFixedDifferenceFourD_pos hm
  unfold unequalFixedDifferenceFourHeadOneDenominator
  positivity

theorem unequalFixedDifferenceFourHeadTwoDenominator_pos
    {m : ℕ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourHeadTwoDenominator m := by
  have hmR := unequalFD4_cast_seven_le hm
  have hD := unequalFixedDifferenceFourD_pos hm
  have hm0 : 0 < (m : ℝ) := by linarith
  have hminus : 0 < 2 * (m : ℝ) - 1 := by linarith
  unfold unequalFixedDifferenceFourHeadTwoDenominator
  positivity

theorem unequalFixedDifferenceFourTailProduct_pos
    {m : ℕ} (hm : 7 ≤ m) (n : ℕ) :
    0 < unequalFixedDifferenceFourTailProduct m n := by
  have hmR := unequalFD4_cast_seven_le hm
  unfold unequalFixedDifferenceFourTailProduct
  exact Finset.prod_pos fun h hh => by
    have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hhR : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
    linarith

theorem unequalFixedDifferenceFourPlusTailDenominator_pos
    {m : ℕ} (hm : 7 ≤ m) (n : ℕ) :
    0 < unequalFixedDifferenceFourPlusTailDenominator m n := by
  have hmR := unequalFD4_cast_seven_le hm
  have hprod := unequalFixedDifferenceFourTailProduct_pos hm n
  have hD := unequalFixedDifferenceFourD_pos hm
  have hm0 : 0 < (m : ℝ) := by linarith
  have hminus : 0 < 2 * (m : ℝ) - 1 := by linarith
  unfold unequalFixedDifferenceFourPlusTailDenominator
  positivity

theorem unequalFixedDifferenceFourMinusTailDenominator_pos
    {m : ℕ} (hm : 7 ≤ m) (n : ℕ) :
    0 < unequalFixedDifferenceFourMinusTailDenominator m n := by
  have hmR := unequalFD4_cast_seven_le hm
  have hprod := unequalFixedDifferenceFourTailProduct_pos hm n
  have hD := unequalFixedDifferenceFourD_pos hm
  have hm0 : 0 < (m : ℝ) := by linarith
  have hminus : 0 < 2 * (m : ℝ) - 1 := by linarith
  unfold unequalFixedDifferenceFourMinusTailDenominator
  positivity

/-! ## Strictly negative tail factors -/

def unequalFixedDifferenceFourPlusTailFactor
    (m n : ℕ) : ℝ :=
  -(((m : ℝ) - 1) * ((n : ℝ) + 1) * ((n : ℝ) + 2)
      * unequalFD4TailPlus (m : ℝ) (n : ℝ))
    / unequalFixedDifferenceFourPlusTailDenominator m n

def unequalFixedDifferenceFourMinusTailFactor
    (m n : ℕ) : ℝ :=
  -(((m : ℝ) + 1) * ((n : ℝ) + 1) * ((n : ℝ) + 2)
      * unequalFD4TailMinus (m : ℝ) (n : ℝ))
    / unequalFixedDifferenceFourMinusTailDenominator m n

theorem unequalFixedDifferenceFourPlusTailFactor_neg
    {m n : ℕ} (hm : 7 ≤ m) (hn : 3 ≤ n) :
    unequalFixedDifferenceFourPlusTailFactor m n < 0 := by
  have hmR := unequalFD4_cast_seven_le hm
  have hnR := unequalFD4_cast_three_le hn
  have hpoly :
      0 < unequalFD4TailPlus (m : ℝ) (n : ℝ) :=
    unequalFD4TailPlus_pos hmR hnR
  have hnum :
      0 <
        ((m : ℝ) - 1) * ((n : ℝ) + 1) * ((n : ℝ) + 2)
          * unequalFD4TailPlus (m : ℝ) (n : ℝ) := by
    exact mul_pos
      (mul_pos
        (mul_pos (by linarith) (by linarith))
        (by linarith))
      hpoly
  unfold unequalFixedDifferenceFourPlusTailFactor
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum)
    (unequalFixedDifferenceFourPlusTailDenominator_pos hm n)

theorem unequalFixedDifferenceFourMinusTailFactor_neg
    {m n : ℕ} (hm : 7 ≤ m) (hn : 3 ≤ n) :
    unequalFixedDifferenceFourMinusTailFactor m n < 0 := by
  have hmR := unequalFD4_cast_seven_le hm
  have hnR := unequalFD4_cast_three_le hn
  have hpoly :
      0 < unequalFD4TailMinus (m : ℝ) (n : ℝ) :=
    unequalFD4TailMinus_pos hmR hnR
  have hnum :
      0 <
        ((m : ℝ) + 1) * ((n : ℝ) + 1) * ((n : ℝ) + 2)
          * unequalFD4TailMinus (m : ℝ) (n : ℝ) := by
    exact mul_pos
      (mul_pos
        (mul_pos (by linarith) (by linarith))
        (by linarith))
      hpoly
  unfold unequalFixedDifferenceFourMinusTailFactor
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum)
    (unequalFixedDifferenceFourMinusTailDenominator_pos hm n)

/-! ## The two coefficient sequences -/

def unequalFixedDifferenceFourPlusCoeff (m : ℕ) : ℕ → ℝ
  | 0 => -unequalFixedDifferenceFourB0 m
  | 1 =>
      -unequalFD4HeadPlusOne (m : ℝ)
        / unequalFixedDifferenceFourHeadOneDenominator m
  | 2 =>
      -unequalFD4HeadPlusTwo (m : ℝ)
        / unequalFixedDifferenceFourHeadTwoDenominator m
  | n + 3 =>
      unequalFixedDifferenceFourPlusMoment m (n + 3)
        * unequalFixedDifferenceFourPlusTailFactor m (n + 3)

def unequalFixedDifferenceFourMinusCoeff (m : ℕ) : ℕ → ℝ
  | 0 => -unequalFixedDifferenceFourB0 m
  | 1 =>
      -unequalFD4HeadMinusOne (m : ℝ)
        / unequalFixedDifferenceFourHeadOneDenominator m
  | 2 =>
      -unequalFD4HeadMinusTwo (m : ℝ)
        / unequalFixedDifferenceFourHeadTwoDenominator m
  | n + 3 =>
      unequalFixedDifferenceFourMinusMoment m (n + 3)
        * unequalFixedDifferenceFourMinusTailFactor m (n + 3)

@[simp]
theorem unequalFixedDifferenceFourPlusCoeff_zero (m : ℕ) :
    unequalFixedDifferenceFourPlusCoeff m 0
      = -unequalFixedDifferenceFourB0 m := by
  rfl

@[simp]
theorem unequalFixedDifferenceFourMinusCoeff_zero (m : ℕ) :
    unequalFixedDifferenceFourMinusCoeff m 0
      = -unequalFixedDifferenceFourB0 m := by
  rfl

theorem unequalFixedDifferenceFourPlusCoeff_neg
    {m : ℕ} (hm : 7 ≤ m) :
    ∀ n : ℕ, unequalFixedDifferenceFourPlusCoeff m n < 0
  | 0 => by
      simp only [unequalFixedDifferenceFourPlusCoeff]
      exact neg_neg_of_pos (unequalFixedDifferenceFourB0_pos hm)
  | 1 => by
      simp only [unequalFixedDifferenceFourPlusCoeff]
      exact div_neg_of_neg_of_pos
        (neg_neg_of_pos
          (unequalFD4HeadPlusOne_pos (unequalFD4_cast_seven_le hm)))
        (unequalFixedDifferenceFourHeadOneDenominator_pos hm)
  | 2 => by
      simp only [unequalFixedDifferenceFourPlusCoeff]
      exact div_neg_of_neg_of_pos
        (neg_neg_of_pos
          (unequalFD4HeadPlusTwo_pos (unequalFD4_cast_seven_le hm)))
        (unequalFixedDifferenceFourHeadTwoDenominator_pos hm)
  | n + 3 => by
      simp only [unequalFixedDifferenceFourPlusCoeff]
      exact mul_neg_of_pos_of_neg
        (unequalFixedDifferenceFourPlusMoment_pos hm (n + 3))
        (unequalFixedDifferenceFourPlusTailFactor_neg hm (by omega))

theorem unequalFixedDifferenceFourMinusCoeff_neg
    {m : ℕ} (hm : 7 ≤ m) :
    ∀ n : ℕ, unequalFixedDifferenceFourMinusCoeff m n < 0
  | 0 => by
      simp only [unequalFixedDifferenceFourMinusCoeff]
      exact neg_neg_of_pos (unequalFixedDifferenceFourB0_pos hm)
  | 1 => by
      simp only [unequalFixedDifferenceFourMinusCoeff]
      exact div_neg_of_neg_of_pos
        (neg_neg_of_pos
          (unequalFD4HeadMinusOne_pos (unequalFD4_cast_seven_le hm)))
        (unequalFixedDifferenceFourHeadOneDenominator_pos hm)
  | 2 => by
      simp only [unequalFixedDifferenceFourMinusCoeff]
      exact div_neg_of_neg_of_pos
        (neg_neg_of_pos
          (unequalFD4HeadMinusTwo_pos (unequalFD4_cast_seven_le hm)))
        (unequalFixedDifferenceFourHeadTwoDenominator_pos hm)
  | n + 3 => by
      simp only [unequalFixedDifferenceFourMinusCoeff]
      exact mul_neg_of_pos_of_neg
        (unequalFixedDifferenceFourMinusMoment_pos hm (n + 3))
        (unequalFixedDifferenceFourMinusTailFactor_neg hm (by omega))

/-! ## Uniform bounds for the formal power series -/

def unequalFixedDifferenceFourPlusSeriesTerm
    (m : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  unequalFixedDifferenceFourPlusCoeff m n * s ^ n

def unequalFixedDifferenceFourMinusSeriesTerm
    (m : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  unequalFixedDifferenceFourMinusCoeff m n * s ^ n

def unequalFixedDifferenceFourPlusSeries (m : ℕ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, unequalFixedDifferenceFourPlusSeriesTerm m s n

def unequalFixedDifferenceFourMinusSeries (m : ℕ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, unequalFixedDifferenceFourMinusSeriesTerm m s n

theorem unequalFixedDifferenceFourPlusSeriesTerm_nonpos
    {m : ℕ} (hm : 7 ≤ m) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    unequalFixedDifferenceFourPlusSeriesTerm m s n ≤ 0 := by
  unfold unequalFixedDifferenceFourPlusSeriesTerm
  exact mul_nonpos_of_nonpos_of_nonneg
    (unequalFixedDifferenceFourPlusCoeff_neg hm n).le
    (pow_nonneg hs n)

theorem unequalFixedDifferenceFourMinusSeriesTerm_nonpos
    {m : ℕ} (hm : 7 ≤ m) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    unequalFixedDifferenceFourMinusSeriesTerm m s n ≤ 0 := by
  unfold unequalFixedDifferenceFourMinusSeriesTerm
  exact mul_nonpos_of_nonpos_of_nonneg
    (unequalFixedDifferenceFourMinusCoeff_neg hm n).le
    (pow_nonneg hs n)

theorem unequalFixedDifferenceFourPlusSeries_le_neg_b0
    {m : ℕ} (hm : 7 ≤ m) {s : ℝ} (hs : 0 ≤ s)
    (hsum : Summable (unequalFixedDifferenceFourPlusSeriesTerm m s)) :
    unequalFixedDifferenceFourPlusSeries m s
      ≤ -unequalFixedDifferenceFourB0 m := by
  unfold unequalFixedDifferenceFourPlusSeries
  calc
    (∑' n : ℕ, unequalFixedDifferenceFourPlusSeriesTerm m s n)
        ≤ unequalFixedDifferenceFourPlusSeriesTerm m s 0 :=
      tsum_le_zero_term_of_nonpos hsum
        (unequalFixedDifferenceFourPlusSeriesTerm_nonpos hm hs)
    _ = -unequalFixedDifferenceFourB0 m := by
      simp [unequalFixedDifferenceFourPlusSeriesTerm]

theorem unequalFixedDifferenceFourMinusSeries_le_neg_b0
    {m : ℕ} (hm : 7 ≤ m) {s : ℝ} (hs : 0 ≤ s)
    (hsum : Summable (unequalFixedDifferenceFourMinusSeriesTerm m s)) :
    unequalFixedDifferenceFourMinusSeries m s
      ≤ -unequalFixedDifferenceFourB0 m := by
  unfold unequalFixedDifferenceFourMinusSeries
  calc
    (∑' n : ℕ, unequalFixedDifferenceFourMinusSeriesTerm m s n)
        ≤ unequalFixedDifferenceFourMinusSeriesTerm m s 0 :=
      tsum_le_zero_term_of_nonpos hsum
        (unequalFixedDifferenceFourMinusSeriesTerm_nonpos hm hs)
    _ = -unequalFixedDifferenceFourB0 m := by
      simp [unequalFixedDifferenceFourMinusSeriesTerm]

theorem unequalFixedDifferenceFourPlusSeries_neg
    {m : ℕ} (hm : 7 ≤ m) {s : ℝ} (hs : 0 ≤ s)
    (hsum : Summable (unequalFixedDifferenceFourPlusSeriesTerm m s)) :
    unequalFixedDifferenceFourPlusSeries m s < 0 :=
  (unequalFixedDifferenceFourPlusSeries_le_neg_b0 hm hs hsum).trans_lt
    (neg_neg_of_pos (unequalFixedDifferenceFourB0_pos hm))

theorem unequalFixedDifferenceFourMinusSeries_neg
    {m : ℕ} (hm : 7 ≤ m) {s : ℝ} (hs : 0 ≤ s)
    (hsum : Summable (unequalFixedDifferenceFourMinusSeriesTerm m s)) :
    unequalFixedDifferenceFourMinusSeries m s < 0 :=
  (unequalFixedDifferenceFourMinusSeries_le_neg_b0 hm hs hsum).trans_lt
    (neg_neg_of_pos (unequalFixedDifferenceFourB0_pos hm))

end

end GraybillDeal
