import GraybillDeal.UnequalFixedDifferenceFourSeriesBridge
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp

/-!
# Collected coefficient algebra for the fixed-difference-four family

This file contains the pure rational-algebra calculation which identifies
the polynomial-moment coefficients from the analytic series bridge with the
two coefficient sequences whose signs were certified earlier.
-/

namespace GraybillDeal

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! ## Polynomial form of the shifted binomial coefficients -/

private theorem unequalFD4_cast_choose_two_poly (n : ℕ) :
    (Nat.choose n 2 : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  cases n with
  | zero => norm_num [Nat.choose]
  | succ n =>
      rw [Nat.cast_choose_two]

private theorem unequalFD4_cast_choose_three_poly (n : ℕ) :
    (Nat.choose n 3 : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
  induction n with
  | zero => norm_num [Nat.choose]
  | succ n ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.cast_add, Nat.cast_succ]
      rw [unequalFD4_cast_choose_two_poly, ih]
      ring

private theorem unequalFD4_cast_choose_four_poly (n : ℕ) :
    (Nat.choose n 4 : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)
        * ((n : ℝ) - 3) / 24 := by
  induction n with
  | zero => norm_num [Nat.choose]
  | succ n ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.cast_add, Nat.cast_succ]
      rw [unequalFD4_cast_choose_three_poly, ih]
      ring

theorem unequalFD4_cast_choose_five_poly (n : ℕ) :
    (Nat.choose n 5 : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)
        * ((n : ℝ) - 3) * ((n : ℝ) - 4) / 120 := by
  induction n with
  | zero => norm_num [Nat.choose]
  | succ n ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.cast_add, Nat.cast_succ]
      rw [unequalFD4_cast_choose_four_poly, ih]
      ring

/-! ## Finite-shift recurrences for the two beta moments -/

def unequalFixedDifferenceFourPlusMomentRatio
    (m n j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j,
    ((m : ℝ) + 1 + ((n + i : ℕ) : ℝ))
      / (2 * (m : ℝ) + ((n + i : ℕ) : ℝ))

def unequalFixedDifferenceFourMinusMomentRatio
    (m n j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j,
    ((m : ℝ) - 1 + ((n + i : ℕ) : ℝ))
      / (2 * (m : ℝ) + ((n + i : ℕ) : ℝ))

theorem unequalFixedDifferenceFourPlusMoment_add
    (m n j : ℕ) :
    unequalFixedDifferenceFourPlusMoment m (n + j)
      =
    unequalFixedDifferenceFourPlusMoment m n
      * unequalFixedDifferenceFourPlusMomentRatio m n j := by
  unfold unequalFixedDifferenceFourPlusMoment
    unequalFixedDifferenceFourPlusMomentRatio
  rw [Finset.prod_range_add]

theorem unequalFixedDifferenceFourMinusMoment_add
    (m n j : ℕ) :
    unequalFixedDifferenceFourMinusMoment m (n + j)
      =
    unequalFixedDifferenceFourMinusMoment m n
      * unequalFixedDifferenceFourMinusMomentRatio m n j := by
  unfold unequalFixedDifferenceFourMinusMoment
    unequalFixedDifferenceFourMinusMomentRatio
  rw [Finset.prod_range_add]

/-! ## Expansion of polynomial moments -/

private theorem unequalFD4PolynomialMoment_add
    (moment : ℕ → ℝ) (n : ℕ) (p q : Polynomial ℝ) :
    unequalDampedPolynomialMoment moment n (p + q)
      =
    unequalDampedPolynomialMoment moment n p
      + unequalDampedPolynomialMoment moment n q := by
  unfold unequalDampedPolynomialMoment
  apply Polynomial.sum_add_index
  · intro i
    simp
  · intro i a b
    ring

private theorem unequalFD4PolynomialMoment_monomial
    (moment : ℕ → ℝ) (n i : ℕ) (a : ℝ) :
    unequalDampedPolynomialMoment moment n
      (Polynomial.C a * Polynomial.X ^ i)
      = a * moment (n + i) := by
  rw [Polynomial.C_mul_X_pow_eq_monomial]
  simp [unequalDampedPolynomialMoment]

theorem unequalFD4PolynomialMoment_G0
    (moment : ℕ → ℝ) (n : ℕ) (q κ c k : ℝ) :
    unequalDampedPolynomialMoment moment n
      (unequalDampedG0Polynomial q κ c k)
      =
    (-q ^ 2 * (c - k)) * moment (n + 1)
      + (q * (c - k) * (κ + q + 2)) * moment (n + 2)
      + (-(κ + 1) * (c - k) * (2 * q + 1)) * moment (n + 3)
      + ((c - k) * (κ * q + 2 * κ + 1)) * moment (n + 4)
      + (-κ * (c - k)) * moment (n + 5) := by
  have hp :
      unequalDampedG0Polynomial q κ c k
        =
      Polynomial.C (-q ^ 2 * (c - k)) * Polynomial.X ^ 1
        + Polynomial.C (q * (c - k) * (κ + q + 2)) * Polynomial.X ^ 2
        + Polynomial.C (-(κ + 1) * (c - k) * (2 * q + 1))
            * Polynomial.X ^ 3
        + Polynomial.C ((c - k) * (κ * q + 2 * κ + 1))
            * Polynomial.X ^ 4
        + Polynomial.C (-κ * (c - k)) * Polynomial.X ^ 5 := by
    calc
      unequalDampedG0Polynomial q κ c k
          =
        (-(Polynomial.C q * Polynomial.C q)
            * (Polynomial.C c - Polynomial.C k)) * Polynomial.X ^ 1
          + (Polynomial.C q * (Polynomial.C c - Polynomial.C k)
              * (Polynomial.C κ + Polynomial.C q + Polynomial.C 2))
              * Polynomial.X ^ 2
          + (-(Polynomial.C κ + Polynomial.C 1)
              * (Polynomial.C c - Polynomial.C k)
              * (Polynomial.C 2 * Polynomial.C q + Polynomial.C 1))
              * Polynomial.X ^ 3
          + ((Polynomial.C c - Polynomial.C k)
              * (Polynomial.C κ * Polynomial.C q
                + Polynomial.C 2 * Polynomial.C κ + Polynomial.C 1))
              * Polynomial.X ^ 4
          + (-Polynomial.C κ * (Polynomial.C c - Polynomial.C k))
              * Polynomial.X ^ 5 := by
            unfold unequalDampedG0Polynomial unequalDampedWBarPolynomial
              unequalDampedF0Polynomial
            simp only [map_neg, map_add, map_sub, map_ofNat,
              Polynomial.C_1]
            ring
      _ = _ := by
        simp only [← Polynomial.C_mul, ← Polynomial.C_add,
          ← Polynomial.C_neg, ← Polynomial.C_sub]
        ring
  rw [hp, unequalFD4PolynomialMoment_add, unequalFD4PolynomialMoment_add,
    unequalFD4PolynomialMoment_add, unequalFD4PolynomialMoment_add]
  rw [unequalFD4PolynomialMoment_monomial,
    unequalFD4PolynomialMoment_monomial,
    unequalFD4PolynomialMoment_monomial,
    unequalFD4PolynomialMoment_monomial,
    unequalFD4PolynomialMoment_monomial]

def unequalFD4G1H1 (t q κ c k : ℝ) : ℝ :=
  c * (2 * q - t - κ) + k * (κ * q + t + κ)

def unequalFD4G1H2 (q κ c k : ℝ) : ℝ :=
  k - 2 * c - k * κ * (q + 1)

theorem unequalFD4PolynomialMoment_G1
    (moment : ℕ → ℝ) (n : ℕ) (t q κ c k : ℝ) :
    unequalDampedPolynomialMoment moment n
      (unequalDampedG1Polynomial t q κ c k)
      =
    (-k * q ^ 3) * moment n
      + (q * unequalFD4G1H1 t q κ c k + k * q ^ 2 * (q + 1))
          * moment (n + 1)
      + (q * unequalFD4G1H2 q κ c k
          - (q + 1) * unequalFD4G1H1 t q κ c k - k * q ^ 2)
          * moment (n + 2)
      + (q * κ * c - (q + 1) * unequalFD4G1H2 q κ c k
          + unequalFD4G1H1 t q κ c k) * moment (n + 3)
      + (-(q + 1) * κ * c + unequalFD4G1H2 q κ c k)
          * moment (n + 4)
      + (κ * c) * moment (n + 5) := by
  have hp :
      unequalDampedG1Polynomial t q κ c k
        =
      Polynomial.C (-k * q ^ 3) * Polynomial.X ^ 0
        + Polynomial.C
            (q * unequalFD4G1H1 t q κ c k + k * q ^ 2 * (q + 1))
            * Polynomial.X ^ 1
        + Polynomial.C
            (q * unequalFD4G1H2 q κ c k
              - (q + 1) * unequalFD4G1H1 t q κ c k - k * q ^ 2)
            * Polynomial.X ^ 2
        + Polynomial.C
            (q * κ * c - (q + 1) * unequalFD4G1H2 q κ c k
              + unequalFD4G1H1 t q κ c k)
            * Polynomial.X ^ 3
        + Polynomial.C
            (-(q + 1) * κ * c + unequalFD4G1H2 q κ c k)
            * Polynomial.X ^ 4
        + Polynomial.C (κ * c) * Polynomial.X ^ 5 := by
    unfold unequalDampedG1Polynomial unequalDampedWBarPolynomial
      unequalDampedF0Polynomial unequalDampedF1HatPolynomial
      unequalDampedPsi1Polynomial unequalFD4G1H1 unequalFD4G1H2
    simp only [map_neg, map_add, map_sub, map_mul, map_pow,
      map_ofNat, Polynomial.C_1]
    ring
  rw [hp, unequalFD4PolynomialMoment_add, unequalFD4PolynomialMoment_add,
    unequalFD4PolynomialMoment_add, unequalFD4PolynomialMoment_add,
    unequalFD4PolynomialMoment_add]
  rw [unequalFD4PolynomialMoment_monomial,
    unequalFD4PolynomialMoment_monomial,
    unequalFD4PolynomialMoment_monomial,
    unequalFD4PolynomialMoment_monomial,
    unequalFD4PolynomialMoment_monomial,
    unequalFD4PolynomialMoment_monomial]
  simp only [Nat.add_zero]

def unequalFD4G2H0 (t q κ k : ℝ) : ℝ :=
  k * q * (q - t - κ)

def unequalFD4G2H1 (t q κ c k : ℝ) : ℝ :=
  c * (2 * t + κ - q) + k * (q * κ - q - t)

def unequalFD4G2H2 (κ c : ℝ) : ℝ :=
  c * (1 - κ)

theorem unequalFD4PolynomialMoment_G2
    (moment : ℕ → ℝ) (n : ℕ) (t q κ c k : ℝ) :
    unequalDampedPolynomialMoment moment n
      (unequalDampedG2Polynomial t q κ c k)
      =
    (q * unequalFD4G2H0 t q κ k) * moment n
      + (q * unequalFD4G2H1 t q κ c k
          - (q + 1) * unequalFD4G2H0 t q κ k) * moment (n + 1)
      + (q * unequalFD4G2H2 κ c
          - (q + 1) * unequalFD4G2H1 t q κ c k
          + unequalFD4G2H0 t q κ k) * moment (n + 2)
      + (-(q + 1) * unequalFD4G2H2 κ c
          + unequalFD4G2H1 t q κ c k) * moment (n + 3)
      + unequalFD4G2H2 κ c * moment (n + 4) := by
  have hp :
      unequalDampedG2Polynomial t q κ c k
        =
      Polynomial.C (q * unequalFD4G2H0 t q κ k) * Polynomial.X ^ 0
        + Polynomial.C
            (q * unequalFD4G2H1 t q κ c k
              - (q + 1) * unequalFD4G2H0 t q κ k)
            * Polynomial.X ^ 1
        + Polynomial.C
            (q * unequalFD4G2H2 κ c
              - (q + 1) * unequalFD4G2H1 t q κ c k
              + unequalFD4G2H0 t q κ k)
            * Polynomial.X ^ 2
        + Polynomial.C
            (-(q + 1) * unequalFD4G2H2 κ c
              + unequalFD4G2H1 t q κ c k)
            * Polynomial.X ^ 3
        + Polynomial.C (unequalFD4G2H2 κ c) * Polynomial.X ^ 4 := by
    unfold unequalDampedG2Polynomial unequalDampedWBarPolynomial
      unequalDampedF1HatPolynomial unequalDampedPsi1Polynomial
      unequalFD4G2H0 unequalFD4G2H1 unequalFD4G2H2
    simp only [map_neg, map_add, map_sub, map_mul, map_pow,
      map_ofNat, Polynomial.C_1]
    ring
  rw [hp, unequalFD4PolynomialMoment_add, unequalFD4PolynomialMoment_add,
    unequalFD4PolynomialMoment_add, unequalFD4PolynomialMoment_add]
  rw [unequalFD4PolynomialMoment_monomial,
    unequalFD4PolynomialMoment_monomial,
    unequalFD4PolynomialMoment_monomial,
    unequalFD4PolynomialMoment_monomial,
    unequalFD4PolynomialMoment_monomial]
  simp only [Nat.add_zero]

theorem unequalFD4PolynomialMoment_G3
    (moment : ℕ → ℝ) (n : ℕ) (t q c k : ℝ) :
    unequalDampedPolynomialMoment moment n
      (unequalDampedG3Polynomial t q c k)
      =
    (t * k * q ^ 2) * moment n
      + (-t * q * (c + k * (q + 1))) * moment (n + 1)
      + (t * (c * (q + 1) + k * q)) * moment (n + 2)
      + (-t * c) * moment (n + 3) := by
  have hp :
      unequalDampedG3Polynomial t q c k
        =
      Polynomial.C (t * k * q ^ 2) * Polynomial.X ^ 0
        + Polynomial.C (-t * q * (c + k * (q + 1)))
            * Polynomial.X ^ 1
        + Polynomial.C (t * (c * (q + 1) + k * q))
            * Polynomial.X ^ 2
        + Polynomial.C (-t * c) * Polynomial.X ^ 3 := by
    unfold unequalDampedG3Polynomial unequalDampedWBarPolynomial
      unequalDampedPsi1Polynomial
    simp only [map_neg, map_add, map_sub, map_mul, map_pow,
      map_ofNat, Polynomial.C_1]
    ring
  rw [hp, unequalFD4PolynomialMoment_add, unequalFD4PolynomialMoment_add,
    unequalFD4PolynomialMoment_add]
  rw [unequalFD4PolynomialMoment_monomial,
    unequalFD4PolynomialMoment_monomial,
    unequalFD4PolynomialMoment_monomial,
    unequalFD4PolynomialMoment_monomial]
  simp only [Nat.add_zero]

macro "unequal_fd4_expand_plus_moment_ratios" : tactic =>
  `(tactic|
    (unfold unequalFixedDifferenceFourPlusMomentRatio
     norm_num [Finset.prod_range_succ]
     push_cast))

macro "unequal_fd4_expand_minus_moment_ratios" : tactic =>
  `(tactic|
    (unfold unequalFixedDifferenceFourMinusMomentRatio
     norm_num [Finset.prod_range_succ]
     push_cast))

/--
Before splitting off the first three exceptional coefficients, the
right-chart polynomial expression is its beta moment times the certified
tail factor.
-/
theorem unequalFixedDifferenceFourPlusPolynomialCoefficient_eq_moment_mul
    {m : ℕ} (hm : 7 ≤ m) (n : ℕ) :
    unequalFixedDifferenceFourPlusPolynomialCoefficient m n
      =
    unequalFixedDifferenceFourPlusMoment m n
      * unequalFixedDifferenceFourPlusTailFactor m n := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have h2m1 : 2 * (m : ℝ) - 1 ≠ 0 := by linarith
  have hD : unequalFixedDifferenceFourD m ≠ 0 :=
    (unequalFixedDifferenceFourD_pos hm).ne'
  have hden (a : ℕ) :
      2 * (m : ℝ) + (n : ℝ) + (a : ℝ) ≠ 0 := by
    positivity
  unfold unequalFixedDifferenceFourPlusPolynomialCoefficient
  rw [unequalFD4PolynomialMoment_G0, unequalFD4PolynomialMoment_G1,
    unequalFD4PolynomialMoment_G2, unequalFD4PolynomialMoment_G3]
  rw [
    unequalFixedDifferenceFourPlusMoment_add m n 1,
    unequalFixedDifferenceFourPlusMoment_add m n 2,
    unequalFixedDifferenceFourPlusMoment_add m n 3,
    unequalFixedDifferenceFourPlusMoment_add m n 4,
    unequalFixedDifferenceFourPlusMoment_add m n 5]
  rw [unequalFD4_cast_choose_five_poly (n + 5),
    unequalFD4_cast_choose_five_poly (n + 4),
    unequalFD4_cast_choose_five_poly (n + 3),
    unequalFD4_cast_choose_five_poly (n + 2)]
  unequal_fd4_expand_plus_moment_ratios
  unfold unequalFD4G1H1 unequalFD4G1H2
    unequalFD4G2H0 unequalFD4G2H1 unequalFD4G2H2
  unfold unequalFixedDifferenceFourT unequalFixedDifferenceFourQ
    unequalFixedDifferenceFourKappa unequalFixedDifferenceFourC
    unequalFixedDifferenceFourK
    unequalFixedDifferenceFourPlusTailFactor
    unequalFixedDifferenceFourPlusTailDenominator
    unequalFixedDifferenceFourTailProduct
    unequalFD4TailPlus unequalFD4TailPlusShift
    unequalFD4TailPlusA0 unequalFD4TailPlusA1 unequalFD4TailPlusA2
    unequalFD4TailPlusA3 unequalFD4TailPlusA4 unequalFD4TailPlusA5
  norm_num [Finset.prod_range_succ]
  push_cast
  field_simp [hm0, h2m1, hD,
    hden 0, hden 1, hden 2, hden 3, hden 4,
    hden 5, hden 6, hden 7, hden 8, hden 9]
  unfold unequalFixedDifferenceFourD
  ring

/-- Swapped-chart counterpart of the normalized polynomial identity. -/
theorem unequalFixedDifferenceFourMinusPolynomialCoefficient_eq_moment_mul
    {m : ℕ} (hm : 7 ≤ m) (n : ℕ) :
    unequalFixedDifferenceFourMinusPolynomialCoefficient m n
      =
    unequalFixedDifferenceFourMinusMoment m n
      * unequalFixedDifferenceFourMinusTailFactor m n := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have h2m1 : 2 * (m : ℝ) - 1 ≠ 0 := by linarith
  have hD : unequalFixedDifferenceFourD m ≠ 0 :=
    (unequalFixedDifferenceFourD_pos hm).ne'
  have hden (a : ℕ) :
      2 * (m : ℝ) + (n : ℝ) + (a : ℝ) ≠ 0 := by
    positivity
  unfold unequalFixedDifferenceFourMinusPolynomialCoefficient
  rw [unequalFD4PolynomialMoment_G0, unequalFD4PolynomialMoment_G1,
    unequalFD4PolynomialMoment_G2, unequalFD4PolynomialMoment_G3]
  rw [
    unequalFixedDifferenceFourMinusMoment_add m n 1,
    unequalFixedDifferenceFourMinusMoment_add m n 2,
    unequalFixedDifferenceFourMinusMoment_add m n 3,
    unequalFixedDifferenceFourMinusMoment_add m n 4,
    unequalFixedDifferenceFourMinusMoment_add m n 5]
  rw [unequalFD4_cast_choose_five_poly (n + 5),
    unequalFD4_cast_choose_five_poly (n + 4),
    unequalFD4_cast_choose_five_poly (n + 3),
    unequalFD4_cast_choose_five_poly (n + 2)]
  unequal_fd4_expand_minus_moment_ratios
  unfold unequalFD4G1H1 unequalFD4G1H2
    unequalFD4G2H0 unequalFD4G2H1 unequalFD4G2H2
  unfold unequalFixedDifferenceFourT unequalFixedDifferenceFourQ
    unequalFixedDifferenceFourKappa unequalFixedDifferenceFourC
    unequalFixedDifferenceFourK
    unequalFixedDifferenceFourMinusTailFactor
    unequalFixedDifferenceFourMinusTailDenominator
    unequalFixedDifferenceFourTailProduct
    unequalFD4TailMinus unequalFD4TailMinusShift
    unequalFD4TailMinusA0 unequalFD4TailMinusA1 unequalFD4TailMinusA2
    unequalFD4TailMinusA3 unequalFD4TailMinusA4 unequalFD4TailMinusA5
  norm_num [Finset.prod_range_succ]
  push_cast
  field_simp [hm0, h2m1, hD,
    hden 0, hden 1, hden 2, hden 3, hden 4,
    hden 5, hden 6, hden 7, hden 8, hden 9]
  unfold unequalFixedDifferenceFourD
  ring

/-! ## Exceptional head coefficients -/

macro "unequal_fd4_unfold_plus_head_data" : tactic =>
  `(tactic|
    (simp only [unequalFixedDifferenceFourPlusMoment,
      unequalFixedDifferenceFourPlusTailFactor,
      unequalFixedDifferenceFourPlusTailDenominator,
      unequalFixedDifferenceFourTailProduct,
      unequalFixedDifferenceFourHeadOneDenominator,
      unequalFixedDifferenceFourHeadTwoDenominator,
      unequalFixedDifferenceFourB0,
      unequalFD4HeadPlusOne, unequalFD4HeadPlusTwo,
      unequalFD4TailPlus, unequalFD4TailPlusShift,
      unequalFD4TailPlusA0, unequalFD4TailPlusA1,
      unequalFD4TailPlusA2, unequalFD4TailPlusA3,
      unequalFD4TailPlusA4, unequalFD4TailPlusA5]))

macro "unequal_fd4_unfold_minus_head_data" : tactic =>
  `(tactic|
    (simp only [unequalFixedDifferenceFourMinusMoment,
      unequalFixedDifferenceFourMinusTailFactor,
      unequalFixedDifferenceFourMinusTailDenominator,
      unequalFixedDifferenceFourTailProduct,
      unequalFixedDifferenceFourHeadOneDenominator,
      unequalFixedDifferenceFourHeadTwoDenominator,
      unequalFixedDifferenceFourB0,
      unequalFD4HeadMinusOne, unequalFD4HeadMinusTwo,
      unequalFD4TailMinus, unequalFD4TailMinusShift,
      unequalFD4TailMinusA0, unequalFD4TailMinusA1,
      unequalFD4TailMinusA2, unequalFD4TailMinusA3,
      unequalFD4TailMinusA4, unequalFD4TailMinusA5]))

theorem unequalFixedDifferenceFourPlusHeadZero
    {m : ℕ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourPlusMoment m 0
        * unequalFixedDifferenceFourPlusTailFactor m 0
      =
    unequalFixedDifferenceFourPlusCoeff m 0 := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have h2m1 : 2 * (m : ℝ) - 1 ≠ 0 := by linarith
  have h2m1' : -1 + (m : ℝ) * 2 ≠ 0 := by linarith
  have hD : unequalFixedDifferenceFourD m ≠ 0 :=
    (unequalFixedDifferenceFourD_pos hm).ne'
  have hadd (a : ℕ) :
      2 * (m : ℝ) + (a : ℝ) ≠ 0 := by
    have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  simp only [unequalFixedDifferenceFourPlusCoeff]
  unequal_fd4_unfold_plus_head_data
  norm_num [Finset.prod_range_succ]
  push_cast
  field_simp [hm0, h2m1, hD,
    hadd 0, hadd 1, hadd 2, hadd 3, hadd 4]
  ring_nf <;> field_simp [h2m1, h2m1'] <;> ring

theorem unequalFixedDifferenceFourPlusHeadOne
    {m : ℕ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourPlusMoment m 1
        * unequalFixedDifferenceFourPlusTailFactor m 1
      =
    unequalFixedDifferenceFourPlusCoeff m 1 := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have h2m1 : 2 * (m : ℝ) - 1 ≠ 0 := by linarith
  have h2m1' : -1 + (m : ℝ) * 2 ≠ 0 := by linarith
  have hD : unequalFixedDifferenceFourD m ≠ 0 :=
    (unequalFixedDifferenceFourD_pos hm).ne'
  have hadd (a : ℕ) :
      2 * (m : ℝ) + (a : ℝ) ≠ 0 := by
    have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  simp only [unequalFixedDifferenceFourPlusCoeff]
  unequal_fd4_unfold_plus_head_data
  norm_num [Finset.prod_range_succ]
  push_cast
  field_simp [hm0, h2m1, hD,
    hadd 0, hadd 1, hadd 2, hadd 3, hadd 4, hadd 5]
  ring_nf <;> field_simp [h2m1, h2m1'] <;> ring

theorem unequalFixedDifferenceFourPlusHeadTwo
    {m : ℕ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourPlusMoment m 2
        * unequalFixedDifferenceFourPlusTailFactor m 2
      =
    unequalFixedDifferenceFourPlusCoeff m 2 := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have h2m1 : 2 * (m : ℝ) - 1 ≠ 0 := by linarith
  have h2m1' : -1 + (m : ℝ) * 2 ≠ 0 := by linarith
  have hD : unequalFixedDifferenceFourD m ≠ 0 :=
    (unequalFixedDifferenceFourD_pos hm).ne'
  have hadd (a : ℕ) :
      2 * (m : ℝ) + (a : ℝ) ≠ 0 := by
    have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  simp only [unequalFixedDifferenceFourPlusCoeff]
  unequal_fd4_unfold_plus_head_data
  norm_num [Finset.prod_range_succ]
  push_cast
  field_simp [hm0, h2m1, hD,
    hadd 0, hadd 1, hadd 2, hadd 3, hadd 4, hadd 5, hadd 6]
  ring_nf <;> field_simp [h2m1, h2m1'] <;> ring

theorem unequalFixedDifferenceFourMinusHeadZero
    {m : ℕ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourMinusMoment m 0
        * unequalFixedDifferenceFourMinusTailFactor m 0
      =
    unequalFixedDifferenceFourMinusCoeff m 0 := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have h2m1 : 2 * (m : ℝ) - 1 ≠ 0 := by linarith
  have h2m1' : -1 + (m : ℝ) * 2 ≠ 0 := by linarith
  have hD : unequalFixedDifferenceFourD m ≠ 0 :=
    (unequalFixedDifferenceFourD_pos hm).ne'
  have hadd (a : ℕ) :
      2 * (m : ℝ) + (a : ℝ) ≠ 0 := by
    have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  simp only [unequalFixedDifferenceFourMinusCoeff]
  unequal_fd4_unfold_minus_head_data
  norm_num [Finset.prod_range_succ]
  push_cast
  field_simp [hm0, h2m1, hD,
    hadd 0, hadd 1, hadd 2, hadd 3, hadd 4]
  ring_nf <;> field_simp [h2m1, h2m1'] <;> ring

theorem unequalFixedDifferenceFourMinusHeadOne
    {m : ℕ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourMinusMoment m 1
        * unequalFixedDifferenceFourMinusTailFactor m 1
      =
    unequalFixedDifferenceFourMinusCoeff m 1 := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have h2m1 : 2 * (m : ℝ) - 1 ≠ 0 := by linarith
  have h2m1' : -1 + (m : ℝ) * 2 ≠ 0 := by linarith
  have hD : unequalFixedDifferenceFourD m ≠ 0 :=
    (unequalFixedDifferenceFourD_pos hm).ne'
  have hadd (a : ℕ) :
      2 * (m : ℝ) + (a : ℝ) ≠ 0 := by
    have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  simp only [unequalFixedDifferenceFourMinusCoeff]
  unequal_fd4_unfold_minus_head_data
  norm_num [Finset.prod_range_succ]
  push_cast
  field_simp [hm0, h2m1, hD,
    hadd 0, hadd 1, hadd 2, hadd 3, hadd 4, hadd 5]
  ring_nf <;> field_simp [h2m1, h2m1'] <;> ring

theorem unequalFixedDifferenceFourMinusHeadTwo
    {m : ℕ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourMinusMoment m 2
        * unequalFixedDifferenceFourMinusTailFactor m 2
      =
    unequalFixedDifferenceFourMinusCoeff m 2 := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have h2m1 : 2 * (m : ℝ) - 1 ≠ 0 := by linarith
  have h2m1' : -1 + (m : ℝ) * 2 ≠ 0 := by linarith
  have hD : unequalFixedDifferenceFourD m ≠ 0 :=
    (unequalFixedDifferenceFourD_pos hm).ne'
  have hadd (a : ℕ) :
      2 * (m : ℝ) + (a : ℝ) ≠ 0 := by
    have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  simp only [unequalFixedDifferenceFourMinusCoeff]
  unequal_fd4_unfold_minus_head_data
  norm_num [Finset.prod_range_succ]
  push_cast
  field_simp [hm0, h2m1, hD,
    hadd 0, hadd 1, hadd 2, hadd 3, hadd 4, hadd 5, hadd 6]
  ring_nf <;> field_simp [h2m1, h2m1'] <;> ring

/-! ## Identification with the certified coefficient sequences -/

theorem unequalFixedDifferenceFourPlusPolynomialCoefficient_eq_coeff
    {m : ℕ} (hm : 7 ≤ m) :
    ∀ n : ℕ,
      unequalFixedDifferenceFourPlusPolynomialCoefficient m n
        = unequalFixedDifferenceFourPlusCoeff m n
  | 0 =>
      (unequalFixedDifferenceFourPlusPolynomialCoefficient_eq_moment_mul
        hm 0).trans
        (unequalFixedDifferenceFourPlusHeadZero hm)
  | 1 =>
      (unequalFixedDifferenceFourPlusPolynomialCoefficient_eq_moment_mul
        hm 1).trans
        (unequalFixedDifferenceFourPlusHeadOne hm)
  | 2 =>
      (unequalFixedDifferenceFourPlusPolynomialCoefficient_eq_moment_mul
        hm 2).trans
        (unequalFixedDifferenceFourPlusHeadTwo hm)
  | n + 3 => by
      rw [
        unequalFixedDifferenceFourPlusPolynomialCoefficient_eq_moment_mul
          hm (n + 3)]
      rfl

theorem unequalFixedDifferenceFourMinusPolynomialCoefficient_eq_coeff
    {m : ℕ} (hm : 7 ≤ m) :
    ∀ n : ℕ,
      unequalFixedDifferenceFourMinusPolynomialCoefficient m n
        = unequalFixedDifferenceFourMinusCoeff m n
  | 0 =>
      (unequalFixedDifferenceFourMinusPolynomialCoefficient_eq_moment_mul
        hm 0).trans
        (unequalFixedDifferenceFourMinusHeadZero hm)
  | 1 =>
      (unequalFixedDifferenceFourMinusPolynomialCoefficient_eq_moment_mul
        hm 1).trans
        (unequalFixedDifferenceFourMinusHeadOne hm)
  | 2 =>
      (unequalFixedDifferenceFourMinusPolynomialCoefficient_eq_moment_mul
        hm 2).trans
        (unequalFixedDifferenceFourMinusHeadTwo hm)
  | n + 3 => by
      rw [
        unequalFixedDifferenceFourMinusPolynomialCoefficient_eq_moment_mul
          hm (n + 3)]
      rfl

theorem unequalFixedDifferenceFourPlusIntegratedCoefficient_eq_coeff
    {m : ℕ} (hm : 7 ≤ m) (n : ℕ) :
    unequalDampedIntegratedCoefficient
        (unequalFixedDifferenceFourPlusDensity m)
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourQ m)
        (unequalFixedDifferenceFourKappa m)
        (unequalFixedDifferenceFourC m)
        (unequalFixedDifferenceFourK m) n
      =
    unequalFixedDifferenceFourPlusCoeff m n := by
  exact
    (unequalFixedDifferenceFourPlusIntegratedCoefficient_eq_polynomial
      hm n).trans
      (unequalFixedDifferenceFourPlusPolynomialCoefficient_eq_coeff hm n)

theorem unequalFixedDifferenceFourMinusIntegratedCoefficient_eq_coeff
    {m : ℕ} (hm : 7 ≤ m) (n : ℕ) :
    unequalDampedIntegratedCoefficient
        (unequalFixedDifferenceFourMinusDensity m)
        (unequalFixedDifferenceFourQ m)
        (unequalFixedDifferenceFourT m)
        (-unequalFixedDifferenceFourKappa m)
        (unequalFixedDifferenceFourC m)
        (unequalFixedDifferenceFourK m) n
      =
    unequalFixedDifferenceFourMinusCoeff m n := by
  exact
    (unequalFixedDifferenceFourMinusIntegratedCoefficient_eq_polynomial
      hm n).trans
      (unequalFixedDifferenceFourMinusPolynomialCoefficient_eq_coeff hm n)

end

end GraybillDeal
