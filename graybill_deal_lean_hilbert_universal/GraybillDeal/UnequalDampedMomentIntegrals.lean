import GraybillDeal.UnequalDampedMomentAlgebra
import GraybillDeal.UnequalDampedSeriesIntegration
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp

/-!
# Exact moment integrals for the unequal damped certificate

This file connects the polynomial beta densities used by the analytic
one-sided integrals with the finite-product moments and collected
coefficients certified in `UnequalDampedMomentAlgebra`.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

/-- The plus-side density multiplied by its `n`th monomial. -/
def unequalDampedPlusMomentIntegrand (n : ℕ) (y : ℝ) : ℝ :=
  unequalDampedPlusDensity y * y ^ n

/-- The swapped-side density multiplied by its `n`th monomial. -/
def unequalDampedMinusMomentIntegrand (n : ℕ) (y : ℝ) : ℝ :=
  unequalDampedMinusDensity y * y ^ n

theorem continuous_unequalDampedPlusMomentIntegrand (n : ℕ) :
    Continuous (unequalDampedPlusMomentIntegrand n) := by
  unfold unequalDampedPlusMomentIntegrand unequalDampedPlusDensity
  fun_prop

theorem continuous_unequalDampedMinusMomentIntegrand (n : ℕ) :
    Continuous (unequalDampedMinusMomentIntegrand n) := by
  unfold unequalDampedMinusMomentIntegrand unequalDampedMinusDensity
  fun_prop

/-- Closed rational form of a `Beta(8,6)` moment. -/
def unequalDampedPlusMomentClosed (n : ℕ) : ℝ :=
  1235520 /
    ((n + 8 : ℝ) * (n + 9) * (n + 10) * (n + 11) * (n + 12) * (n + 13))

/-- Closed rational form of a `Beta(6,8)` moment. -/
def unequalDampedMinusMomentClosed (n : ℕ) : ℝ :=
  51891840 /
    ((n + 6 : ℝ) * (n + 7) * (n + 8) * (n + 9)
      * (n + 10) * (n + 11) * (n + 12) * (n + 13))

theorem unequalDampedPlusMoment_eq_closed :
    ∀ n : ℕ,
      unequalDampedPlusMoment n = unequalDampedPlusMomentClosed n
  | 0 => by
      norm_num [unequalDampedPlusMoment, unequalDampedPlusMomentClosed]
  | n + 1 => by
      rw [show unequalDampedPlusMoment (n + 1)
          = unequalDampedPlusMoment n
              * ((8 + (n : ℝ)) / (14 + (n : ℝ))) by
            unfold unequalDampedPlusMoment
            rw [Finset.prod_range_succ]]
      rw [unequalDampedPlusMoment_eq_closed n]
      unfold unequalDampedPlusMomentClosed
      push_cast
      field_simp
      ring

theorem unequalDampedMinusMoment_eq_closed :
    ∀ n : ℕ,
      unequalDampedMinusMoment n = unequalDampedMinusMomentClosed n
  | 0 => by
      norm_num [unequalDampedMinusMoment, unequalDampedMinusMomentClosed]
  | n + 1 => by
      rw [show unequalDampedMinusMoment (n + 1)
          = unequalDampedMinusMoment n
              * ((6 + (n : ℝ)) / (14 + (n : ℝ))) by
            unfold unequalDampedMinusMoment
            rw [Finset.prod_range_succ]]
      rw [unequalDampedMinusMoment_eq_closed n]
      unfold unequalDampedMinusMomentClosed
      push_cast
      field_simp
      ring

/-- A polynomial antiderivative of the plus-side moment integrand. -/
def unequalDampedPlusMomentPrimitive (n : ℕ) : ℝ → ℝ :=
  (fun y => 10296 * y ^ (n + 8) / (n + 8 : ℝ))
    - (fun y => 51480 * y ^ (n + 9) / (n + 9 : ℝ))
    + (fun y => 102960 * y ^ (n + 10) / (n + 10 : ℝ))
    - (fun y => 102960 * y ^ (n + 11) / (n + 11 : ℝ))
    + (fun y => 51480 * y ^ (n + 12) / (n + 12 : ℝ))
    - (fun y => 10296 * y ^ (n + 13) / (n + 13 : ℝ))

/-- A polynomial antiderivative of the swapped-side moment integrand. -/
def unequalDampedMinusMomentPrimitive (n : ℕ) : ℝ → ℝ :=
  (fun y => 10296 * y ^ (n + 6) / (n + 6 : ℝ))
    - (fun y => 72072 * y ^ (n + 7) / (n + 7 : ℝ))
    + (fun y => 216216 * y ^ (n + 8) / (n + 8 : ℝ))
    - (fun y => 360360 * y ^ (n + 9) / (n + 9 : ℝ))
    + (fun y => 360360 * y ^ (n + 10) / (n + 10 : ℝ))
    - (fun y => 216216 * y ^ (n + 11) / (n + 11 : ℝ))
    + (fun y => 72072 * y ^ (n + 12) / (n + 12 : ℝ))
    - (fun y => 10296 * y ^ (n + 13) / (n + 13 : ℝ))

private theorem hasDerivAt_unequalDampedPlusMomentPrimitive
    (n : ℕ) (y : ℝ) :
    HasDerivAt (unequalDampedPlusMomentPrimitive n)
      (unequalDampedPlusMomentIntegrand n y) y := by
  unfold unequalDampedPlusMomentPrimitive
    unequalDampedPlusMomentIntegrand unequalDampedPlusDensity
  have h8 :=
    ((hasDerivAt_pow (n + 8) y).const_mul 10296).div_const
      (n + 8 : ℝ)
  have h9 :=
    ((hasDerivAt_pow (n + 9) y).const_mul 51480).div_const
      (n + 9 : ℝ)
  have h10 :=
    ((hasDerivAt_pow (n + 10) y).const_mul 102960).div_const
      (n + 10 : ℝ)
  have h11 :=
    ((hasDerivAt_pow (n + 11) y).const_mul 102960).div_const
      (n + 11 : ℝ)
  have h12 :=
    ((hasDerivAt_pow (n + 12) y).const_mul 51480).div_const
      (n + 12 : ℝ)
  have h13 :=
    ((hasDerivAt_pow (n + 13) y).const_mul 10296).div_const
      (n + 13 : ℝ)
  have hderiv := ((((h8.sub h9).add h10).sub h11).add h12).sub h13
  apply hderiv.congr_deriv
  simp only [show n + 8 - 1 = n + 7 by omega,
      show n + 9 - 1 = n + 8 by omega,
      show n + 10 - 1 = n + 9 by omega,
      show n + 11 - 1 = n + 10 by omega,
      show n + 12 - 1 = n + 11 by omega,
      show n + 13 - 1 = n + 12 by omega,
      Nat.cast_add, Nat.cast_ofNat]
  field_simp
  simp only [pow_add]
  ring

private theorem hasDerivAt_unequalDampedMinusMomentPrimitive
    (n : ℕ) (y : ℝ) :
    HasDerivAt (unequalDampedMinusMomentPrimitive n)
      (unequalDampedMinusMomentIntegrand n y) y := by
  unfold unequalDampedMinusMomentPrimitive
    unequalDampedMinusMomentIntegrand unequalDampedMinusDensity
  have h6 :=
    ((hasDerivAt_pow (n + 6) y).const_mul 10296).div_const
      (n + 6 : ℝ)
  have h7 :=
    ((hasDerivAt_pow (n + 7) y).const_mul 72072).div_const
      (n + 7 : ℝ)
  have h8 :=
    ((hasDerivAt_pow (n + 8) y).const_mul 216216).div_const
      (n + 8 : ℝ)
  have h9 :=
    ((hasDerivAt_pow (n + 9) y).const_mul 360360).div_const
      (n + 9 : ℝ)
  have h10 :=
    ((hasDerivAt_pow (n + 10) y).const_mul 360360).div_const
      (n + 10 : ℝ)
  have h11 :=
    ((hasDerivAt_pow (n + 11) y).const_mul 216216).div_const
      (n + 11 : ℝ)
  have h12 :=
    ((hasDerivAt_pow (n + 12) y).const_mul 72072).div_const
      (n + 12 : ℝ)
  have h13 :=
    ((hasDerivAt_pow (n + 13) y).const_mul 10296).div_const
      (n + 13 : ℝ)
  have h67 := h6.sub h7
  have h678 := h67.add h8
  have h6789 := h678.sub h9
  have h6789a := h6789.add h10
  have h6789ab := h6789a.sub h11
  have h6789abc := h6789ab.add h12
  have hderiv := h6789abc.sub h13
  apply hderiv.congr_deriv
  simp only [show n + 6 - 1 = n + 5 by omega,
      show n + 7 - 1 = n + 6 by omega,
      show n + 8 - 1 = n + 7 by omega,
      show n + 9 - 1 = n + 8 by omega,
      show n + 10 - 1 = n + 9 by omega,
      show n + 11 - 1 = n + 10 by omega,
      show n + 12 - 1 = n + 11 by omega,
      show n + 13 - 1 = n + 12 by omega,
      Nat.cast_add, Nat.cast_ofNat]
  field_simp
  simp only [pow_add]
  ring

/-- Exact plus-side polynomial-density moment integral. -/
theorem integral_unequalDampedPlusMomentIntegrand (n : ℕ) :
    (∫ y in (0 : ℝ)..1, unequalDampedPlusMomentIntegrand n y)
      = unequalDampedPlusMoment n := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := unequalDampedPlusMomentPrimitive n)
    (fun y hy => hasDerivAt_unequalDampedPlusMomentPrimitive n y)
    ((continuous_unequalDampedPlusMomentIntegrand n).intervalIntegrable 0 1)]
  rw [unequalDampedPlusMoment_eq_closed]
  unfold unequalDampedPlusMomentPrimitive unequalDampedPlusMomentClosed
  norm_num
  push_cast
  field_simp
  ring

/-- Exact swapped-side polynomial-density moment integral. -/
theorem integral_unequalDampedMinusMomentIntegrand (n : ℕ) :
    (∫ y in (0 : ℝ)..1, unequalDampedMinusMomentIntegrand n y)
      = unequalDampedMinusMoment n := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := unequalDampedMinusMomentPrimitive n)
    (fun y hy => hasDerivAt_unequalDampedMinusMomentPrimitive n y)
    ((continuous_unequalDampedMinusMomentIntegrand n).intervalIntegrable 0 1)]
  rw [unequalDampedMinusMoment_eq_closed]
  unfold unequalDampedMinusMomentPrimitive unequalDampedMinusMomentClosed
  norm_num
  push_cast
  field_simp
  ring

/--
A six-term linear combination of consecutive moment integrands.  Degree
five suffices for each of the four collected polynomials.
-/
def unequalDampedMomentCombination6
    (momentIntegrand : ℕ → ℝ → ℝ) (n : ℕ)
    (a0 a1 a2 a3 a4 a5 y : ℝ) : ℝ :=
  a0 * momentIntegrand n y
    + (a1 * momentIntegrand (n + 1) y
    + (a2 * momentIntegrand (n + 2) y
    + (a3 * momentIntegrand (n + 3) y
    + (a4 * momentIntegrand (n + 4) y
    + a5 * momentIntegrand (n + 5) y))))

private theorem integral_unequalDampedMomentCombination6
    {momentIntegrand : ℕ → ℝ → ℝ} {moment : ℕ → ℝ}
    (hcontinuous : ∀ j, Continuous (momentIntegrand j))
    (hintegral :
      ∀ j, (∫ y in (0 : ℝ)..1, momentIntegrand j y) = moment j)
    (n : ℕ) (a0 a1 a2 a3 a4 a5 : ℝ) :
    (∫ y in (0 : ℝ)..1,
      unequalDampedMomentCombination6 momentIntegrand n
        a0 a1 a2 a3 a4 a5 y)
      =
    a0 * moment n
      + (a1 * moment (n + 1)
      + (a2 * moment (n + 2)
      + (a3 * moment (n + 3)
      + (a4 * moment (n + 4)
      + a5 * moment (n + 5))))) := by
  have h0 : IntervalIntegrable
      (fun y => a0 * momentIntegrand n y) volume 0 1 :=
    ((hcontinuous n).intervalIntegrable 0 1).const_mul a0
  have h1 : IntervalIntegrable
      (fun y => a1 * momentIntegrand (n + 1) y) volume 0 1 :=
    ((hcontinuous (n + 1)).intervalIntegrable 0 1).const_mul a1
  have h2 : IntervalIntegrable
      (fun y => a2 * momentIntegrand (n + 2) y) volume 0 1 :=
    ((hcontinuous (n + 2)).intervalIntegrable 0 1).const_mul a2
  have h3 : IntervalIntegrable
      (fun y => a3 * momentIntegrand (n + 3) y) volume 0 1 :=
    ((hcontinuous (n + 3)).intervalIntegrable 0 1).const_mul a3
  have h4 : IntervalIntegrable
      (fun y => a4 * momentIntegrand (n + 4) y) volume 0 1 :=
    ((hcontinuous (n + 4)).intervalIntegrable 0 1).const_mul a4
  have h5 : IntervalIntegrable
      (fun y => a5 * momentIntegrand (n + 5) y) volume 0 1 :=
    ((hcontinuous (n + 5)).intervalIntegrable 0 1).const_mul a5
  unfold unequalDampedMomentCombination6
  rw [intervalIntegral.integral_add h0
      (h1.add (h2.add (h3.add (h4.add h5)))),
    intervalIntegral.integral_add h1
      (h2.add (h3.add (h4.add h5))),
    intervalIntegral.integral_add h2 (h3.add (h4.add h5)),
    intervalIntegral.integral_add h3 (h4.add h5),
    intervalIntegral.integral_add h4 h5]
  simp only [intervalIntegral.integral_const_mul, hintegral]

/-- Plus-side integrand for the collected polynomial `G₀`. -/
def unequalDampedPlusG0Integrand (n : ℕ) (y : ℝ) : ℝ :=
  unequalDampedPlusDensity y * y ^ n
    * unequalDampedG0 (4 / 7) unequalDampedKappa13_17
      unequalDampedC13_17 unequalDampedK13_17 y

theorem unequalDampedPlusG0Integrand_eq_combination (n : ℕ) (y : ℝ) :
    unequalDampedPlusG0Integrand n y
      =
    unequalDampedMomentCombination6 unequalDampedPlusMomentIntegrand n
      0 (-8 / 343) (30062 / 266511) (-16210 / 88837)
      (18961 / 177674) (-1045 / 76146) y := by
  unfold unequalDampedPlusG0Integrand unequalDampedMomentCombination6
    unequalDampedPlusMomentIntegrand unequalDampedG0 unequalDampedWBar
    unequalDampedF0 unequalDampedPsi0 unequalDampedKappa13_17
    unequalDampedC13_17 unequalDampedK13_17
  norm_num
  simp only [pow_add, pow_succ]
  ring

/-- Exact plus-side integral of `y^n G₀(y)`. -/
theorem integral_unequalDampedPlusG0Integrand (n : ℕ) :
    (∫ y in (0 : ℝ)..1, unequalDampedPlusG0Integrand n y)
      = unequalDampedPlusG0Moment n := by
  calc
    (∫ y in (0 : ℝ)..1, unequalDampedPlusG0Integrand n y)
        =
      ∫ y in (0 : ℝ)..1,
        unequalDampedMomentCombination6 unequalDampedPlusMomentIntegrand n
          0 (-8 / 343) (30062 / 266511) (-16210 / 88837)
          (18961 / 177674) (-1045 / 76146) y := by
            apply intervalIntegral.integral_congr
            intro y hy
            exact unequalDampedPlusG0Integrand_eq_combination n y
    _ = unequalDampedPlusG0Moment n := by
      rw [integral_unequalDampedMomentCombination6
        continuous_unequalDampedPlusMomentIntegrand
        integral_unequalDampedPlusMomentIntegrand]
      unfold unequalDampedPlusG0Moment
      ring

/-- Plus-side integrand for the collected polynomial `G₁`. -/
def unequalDampedPlusG1Integrand (n : ℕ) (y : ℝ) : ℝ :=
  unequalDampedPlusDensity y * y ^ n
    * unequalDampedG1 (3 / 7) (4 / 7) unequalDampedKappa13_17
      unequalDampedC13_17 unequalDampedK13_17 y

/-- Plus-side integrand for the collected polynomial `G₂`. -/
def unequalDampedPlusG2Integrand (n : ℕ) (y : ℝ) : ℝ :=
  unequalDampedPlusDensity y * y ^ n
    * unequalDampedG2 (3 / 7) (4 / 7) unequalDampedKappa13_17
      unequalDampedC13_17 unequalDampedK13_17 y

/-- Plus-side integrand for the collected polynomial `G₃`. -/
def unequalDampedPlusG3Integrand (n : ℕ) (y : ℝ) : ℝ :=
  unequalDampedPlusDensity y * y ^ n
    * unequalDampedG3 (3 / 7) (4 / 7)
      unequalDampedC13_17 unequalDampedK13_17 y

/-- Swapped-side integrand for the collected polynomial `G₀`. -/
def unequalDampedMinusG0Integrand (n : ℕ) (y : ℝ) : ℝ :=
  unequalDampedMinusDensity y * y ^ n
    * unequalDampedG0 (3 / 7) (-unequalDampedKappa13_17)
      unequalDampedC13_17 unequalDampedK13_17 y

/-- Swapped-side integrand for the collected polynomial `G₁`. -/
def unequalDampedMinusG1Integrand (n : ℕ) (y : ℝ) : ℝ :=
  unequalDampedMinusDensity y * y ^ n
    * unequalDampedG1 (4 / 7) (3 / 7) (-unequalDampedKappa13_17)
      unequalDampedC13_17 unequalDampedK13_17 y

/-- Swapped-side integrand for the collected polynomial `G₂`. -/
def unequalDampedMinusG2Integrand (n : ℕ) (y : ℝ) : ℝ :=
  unequalDampedMinusDensity y * y ^ n
    * unequalDampedG2 (4 / 7) (3 / 7) (-unequalDampedKappa13_17)
      unequalDampedC13_17 unequalDampedK13_17 y

/-- Swapped-side integrand for the collected polynomial `G₃`. -/
def unequalDampedMinusG3Integrand (n : ℕ) (y : ℝ) : ℝ :=
  unequalDampedMinusDensity y * y ^ n
    * unequalDampedG3 (4 / 7) (3 / 7)
      unequalDampedC13_17 unequalDampedK13_17 y

theorem continuous_unequalDampedPlusG0Integrand (n : ℕ) :
    Continuous (unequalDampedPlusG0Integrand n) := by
  unfold unequalDampedPlusG0Integrand unequalDampedPlusDensity
    unequalDampedG0 unequalDampedWBar unequalDampedF0 unequalDampedPsi0
  fun_prop

theorem continuous_unequalDampedPlusG1Integrand (n : ℕ) :
    Continuous (unequalDampedPlusG1Integrand n) := by
  unfold unequalDampedPlusG1Integrand unequalDampedPlusDensity
    unequalDampedG1 unequalDampedWBar unequalDampedF0
    unequalDampedF1Hat unequalDampedPsi0 unequalDampedPsi1
  fun_prop

theorem continuous_unequalDampedPlusG2Integrand (n : ℕ) :
    Continuous (unequalDampedPlusG2Integrand n) := by
  unfold unequalDampedPlusG2Integrand unequalDampedPlusDensity
    unequalDampedG2 unequalDampedWBar unequalDampedF1Hat
    unequalDampedPsi0 unequalDampedPsi1
  fun_prop

theorem continuous_unequalDampedPlusG3Integrand (n : ℕ) :
    Continuous (unequalDampedPlusG3Integrand n) := by
  unfold unequalDampedPlusG3Integrand unequalDampedPlusDensity
    unequalDampedG3 unequalDampedWBar unequalDampedPsi1
  fun_prop

theorem continuous_unequalDampedMinusG0Integrand (n : ℕ) :
    Continuous (unequalDampedMinusG0Integrand n) := by
  unfold unequalDampedMinusG0Integrand unequalDampedMinusDensity
    unequalDampedG0 unequalDampedWBar unequalDampedF0 unequalDampedPsi0
  fun_prop

theorem continuous_unequalDampedMinusG1Integrand (n : ℕ) :
    Continuous (unequalDampedMinusG1Integrand n) := by
  unfold unequalDampedMinusG1Integrand unequalDampedMinusDensity
    unequalDampedG1 unequalDampedWBar unequalDampedF0
    unequalDampedF1Hat unequalDampedPsi0 unequalDampedPsi1
  fun_prop

theorem continuous_unequalDampedMinusG2Integrand (n : ℕ) :
    Continuous (unequalDampedMinusG2Integrand n) := by
  unfold unequalDampedMinusG2Integrand unequalDampedMinusDensity
    unequalDampedG2 unequalDampedWBar unequalDampedF1Hat
    unequalDampedPsi0 unequalDampedPsi1
  fun_prop

theorem continuous_unequalDampedMinusG3Integrand (n : ℕ) :
    Continuous (unequalDampedMinusG3Integrand n) := by
  unfold unequalDampedMinusG3Integrand unequalDampedMinusDensity
    unequalDampedG3 unequalDampedWBar unequalDampedPsi1
  fun_prop

theorem unequalDampedPlusG1Integrand_eq_combination (n : ℕ) (y : ℝ) :
    unequalDampedPlusG1Integrand n y
      =
    unequalDampedMomentCombination6 unequalDampedPlusMomentIntegrand n
      (-384 / 637) (13829680 / 3464643) (-34502024 / 3464643)
      (13028317 / 1154881) (-37044377 / 6929286)
      (628045 / 989898) y := by
  unfold unequalDampedPlusG1Integrand unequalDampedMomentCombination6
    unequalDampedPlusMomentIntegrand unequalDampedG1 unequalDampedWBar
    unequalDampedF0 unequalDampedF1Hat unequalDampedPsi0
    unequalDampedPsi1 unequalDampedKappa13_17
    unequalDampedC13_17 unequalDampedK13_17
  norm_num
  simp only [pow_add, pow_succ]
  ring

theorem unequalDampedPlusG2Integrand_eq_combination (n : ℕ) (y : ℝ) :
    unequalDampedPlusG2Integrand n y
      =
    unequalDampedMomentCombination6 unequalDampedPlusMomentIntegrand n
      (-8576 / 164983) (-2074762 / 3464643) (8022661 / 2309762)
      (-12681275 / 2309762) (101569 / 38073) 0 y := by
  unfold unequalDampedPlusG2Integrand unequalDampedMomentCombination6
    unequalDampedPlusMomentIntegrand unequalDampedG2 unequalDampedWBar
    unequalDampedF1Hat unequalDampedPsi0 unequalDampedPsi1
    unequalDampedKappa13_17 unequalDampedC13_17 unequalDampedK13_17
  norm_num
  simp only [pow_add, pow_succ]
  ring

theorem unequalDampedPlusG3Integrand_eq_combination (n : ℕ) (y : ℝ) :
    unequalDampedPlusG3Integrand n y
      =
    unequalDampedMomentCombination6 unequalDampedPlusMomentIntegrand n
      (288 / 637) (-9150 / 4459) (26889 / 8918)
      (-1803 / 1274) 0 0 y := by
  unfold unequalDampedPlusG3Integrand unequalDampedMomentCombination6
    unequalDampedPlusMomentIntegrand unequalDampedG3 unequalDampedWBar
    unequalDampedPsi1 unequalDampedC13_17 unequalDampedK13_17
  norm_num
  simp only [pow_add, pow_succ]
  ring

theorem unequalDampedMinusG0Integrand_eq_combination (n : ℕ) (y : ℝ) :
    unequalDampedMinusG0Integrand n y
      =
    unequalDampedMomentCombination6 unequalDampedMinusMomentIntegrand n
      0 (-9 / 686) (6082 / 88837) (-28561 / 266511)
      (10154 / 266511) (1045 / 76146) y := by
  unfold unequalDampedMinusG0Integrand unequalDampedMomentCombination6
    unequalDampedMinusMomentIntegrand unequalDampedG0 unequalDampedWBar
    unequalDampedF0 unequalDampedPsi0 unequalDampedKappa13_17
    unequalDampedC13_17 unequalDampedK13_17
  norm_num
  simp only [pow_add, pow_succ]
  ring

theorem unequalDampedMinusG1Integrand_eq_combination (n : ℕ) (y : ℝ) :
    unequalDampedMinusG1Integrand n y
      =
    unequalDampedMomentCombination6 unequalDampedMinusMomentIntegrand n
      (-162 / 637) (4469743 / 2309762) (-18307076 / 3464643)
      (20157623 / 3464643) (-421222 / 266511)
      (-628045 / 989898) y := by
  unfold unequalDampedMinusG1Integrand unequalDampedMomentCombination6
    unequalDampedMinusMomentIntegrand unequalDampedG1 unequalDampedWBar
    unequalDampedF0 unequalDampedF1Hat unequalDampedPsi0
    unequalDampedPsi1 unequalDampedKappa13_17
    unequalDampedC13_17 unequalDampedK13_17
  norm_num
  simp only [pow_add, pow_succ]
  ring

theorem unequalDampedMinusG2Integrand_eq_combination (n : ℕ) (y : ℝ) :
    unequalDampedMinusG2Integrand n y
      =
    unequalDampedMomentCombination6 unequalDampedMinusMomentIntegrand n
      (4824 / 164983) (-989876 / 1154881) (14854862 / 3464643)
      (-25625632 / 3464643) (1948442 / 494949) 0 y := by
  unfold unequalDampedMinusG2Integrand unequalDampedMomentCombination6
    unequalDampedMinusMomentIntegrand unequalDampedG2 unequalDampedWBar
    unequalDampedF1Hat unequalDampedPsi0 unequalDampedPsi1
    unequalDampedKappa13_17 unequalDampedC13_17 unequalDampedK13_17
  norm_num
  simp only [pow_add, pow_succ]
  ring

theorem unequalDampedMinusG3Integrand_eq_combination (n : ℕ) (y : ℝ) :
    unequalDampedMinusG3Integrand n y
      =
    unequalDampedMomentCombination6 unequalDampedMinusMomentIntegrand n
      (216 / 637) (-8646 / 4459) (1196 / 343)
      (-1202 / 637) 0 0 y := by
  unfold unequalDampedMinusG3Integrand unequalDampedMomentCombination6
    unequalDampedMinusMomentIntegrand unequalDampedG3 unequalDampedWBar
    unequalDampedPsi1 unequalDampedC13_17 unequalDampedK13_17
  norm_num
  simp only [pow_add, pow_succ]
  ring

/-- Exact plus-side integral of `y^n G₁(y)`. -/
theorem integral_unequalDampedPlusG1Integrand (n : ℕ) :
    (∫ y in (0 : ℝ)..1, unequalDampedPlusG1Integrand n y)
      = unequalDampedPlusG1Moment n := by
  calc
    (∫ y in (0 : ℝ)..1, unequalDampedPlusG1Integrand n y)
        =
      ∫ y in (0 : ℝ)..1,
        unequalDampedMomentCombination6 unequalDampedPlusMomentIntegrand n
          (-384 / 637) (13829680 / 3464643) (-34502024 / 3464643)
          (13028317 / 1154881) (-37044377 / 6929286)
          (628045 / 989898) y := by
            apply intervalIntegral.integral_congr
            intro y hy
            exact unequalDampedPlusG1Integrand_eq_combination n y
    _ = unequalDampedPlusG1Moment n := by
      rw [integral_unequalDampedMomentCombination6
        continuous_unequalDampedPlusMomentIntegrand
        integral_unequalDampedPlusMomentIntegrand]
      unfold unequalDampedPlusG1Moment
      ring

/-- Exact plus-side integral of `y^n G₂(y)`. -/
theorem integral_unequalDampedPlusG2Integrand (n : ℕ) :
    (∫ y in (0 : ℝ)..1, unequalDampedPlusG2Integrand n y)
      = unequalDampedPlusG2Moment n := by
  calc
    (∫ y in (0 : ℝ)..1, unequalDampedPlusG2Integrand n y)
        =
      ∫ y in (0 : ℝ)..1,
        unequalDampedMomentCombination6 unequalDampedPlusMomentIntegrand n
          (-8576 / 164983) (-2074762 / 3464643) (8022661 / 2309762)
          (-12681275 / 2309762) (101569 / 38073) 0 y := by
            apply intervalIntegral.integral_congr
            intro y hy
            exact unequalDampedPlusG2Integrand_eq_combination n y
    _ = unequalDampedPlusG2Moment n := by
      rw [integral_unequalDampedMomentCombination6
        continuous_unequalDampedPlusMomentIntegrand
        integral_unequalDampedPlusMomentIntegrand]
      unfold unequalDampedPlusG2Moment
      ring

/-- Exact plus-side integral of `y^n G₃(y)`. -/
theorem integral_unequalDampedPlusG3Integrand (n : ℕ) :
    (∫ y in (0 : ℝ)..1, unequalDampedPlusG3Integrand n y)
      = unequalDampedPlusG3Moment n := by
  calc
    (∫ y in (0 : ℝ)..1, unequalDampedPlusG3Integrand n y)
        =
      ∫ y in (0 : ℝ)..1,
        unequalDampedMomentCombination6 unequalDampedPlusMomentIntegrand n
          (288 / 637) (-9150 / 4459) (26889 / 8918)
          (-1803 / 1274) 0 0 y := by
            apply intervalIntegral.integral_congr
            intro y hy
            exact unequalDampedPlusG3Integrand_eq_combination n y
    _ = unequalDampedPlusG3Moment n := by
      rw [integral_unequalDampedMomentCombination6
        continuous_unequalDampedPlusMomentIntegrand
        integral_unequalDampedPlusMomentIntegrand]
      unfold unequalDampedPlusG3Moment
      ring

/-- Exact swapped-side integral of `y^n G₀(y)`. -/
theorem integral_unequalDampedMinusG0Integrand (n : ℕ) :
    (∫ y in (0 : ℝ)..1, unequalDampedMinusG0Integrand n y)
      = unequalDampedMinusG0Moment n := by
  calc
    (∫ y in (0 : ℝ)..1, unequalDampedMinusG0Integrand n y)
        =
      ∫ y in (0 : ℝ)..1,
        unequalDampedMomentCombination6 unequalDampedMinusMomentIntegrand n
          0 (-9 / 686) (6082 / 88837) (-28561 / 266511)
          (10154 / 266511) (1045 / 76146) y := by
            apply intervalIntegral.integral_congr
            intro y hy
            exact unequalDampedMinusG0Integrand_eq_combination n y
    _ = unequalDampedMinusG0Moment n := by
      rw [integral_unequalDampedMomentCombination6
        continuous_unequalDampedMinusMomentIntegrand
        integral_unequalDampedMinusMomentIntegrand]
      unfold unequalDampedMinusG0Moment
      ring

/-- Exact swapped-side integral of `y^n G₁(y)`. -/
theorem integral_unequalDampedMinusG1Integrand (n : ℕ) :
    (∫ y in (0 : ℝ)..1, unequalDampedMinusG1Integrand n y)
      = unequalDampedMinusG1Moment n := by
  calc
    (∫ y in (0 : ℝ)..1, unequalDampedMinusG1Integrand n y)
        =
      ∫ y in (0 : ℝ)..1,
        unequalDampedMomentCombination6 unequalDampedMinusMomentIntegrand n
          (-162 / 637) (4469743 / 2309762) (-18307076 / 3464643)
          (20157623 / 3464643) (-421222 / 266511)
          (-628045 / 989898) y := by
            apply intervalIntegral.integral_congr
            intro y hy
            exact unequalDampedMinusG1Integrand_eq_combination n y
    _ = unequalDampedMinusG1Moment n := by
      rw [integral_unequalDampedMomentCombination6
        continuous_unequalDampedMinusMomentIntegrand
        integral_unequalDampedMinusMomentIntegrand]
      unfold unequalDampedMinusG1Moment
      ring

/-- Exact swapped-side integral of `y^n G₂(y)`. -/
theorem integral_unequalDampedMinusG2Integrand (n : ℕ) :
    (∫ y in (0 : ℝ)..1, unequalDampedMinusG2Integrand n y)
      = unequalDampedMinusG2Moment n := by
  calc
    (∫ y in (0 : ℝ)..1, unequalDampedMinusG2Integrand n y)
        =
      ∫ y in (0 : ℝ)..1,
        unequalDampedMomentCombination6 unequalDampedMinusMomentIntegrand n
          (4824 / 164983) (-989876 / 1154881) (14854862 / 3464643)
          (-25625632 / 3464643) (1948442 / 494949) 0 y := by
            apply intervalIntegral.integral_congr
            intro y hy
            exact unequalDampedMinusG2Integrand_eq_combination n y
    _ = unequalDampedMinusG2Moment n := by
      rw [integral_unequalDampedMomentCombination6
        continuous_unequalDampedMinusMomentIntegrand
        integral_unequalDampedMinusMomentIntegrand]
      unfold unequalDampedMinusG2Moment
      ring

/-- Exact swapped-side integral of `y^n G₃(y)`. -/
theorem integral_unequalDampedMinusG3Integrand (n : ℕ) :
    (∫ y in (0 : ℝ)..1, unequalDampedMinusG3Integrand n y)
      = unequalDampedMinusG3Moment n := by
  calc
    (∫ y in (0 : ℝ)..1, unequalDampedMinusG3Integrand n y)
        =
      ∫ y in (0 : ℝ)..1,
        unequalDampedMomentCombination6 unequalDampedMinusMomentIntegrand n
          (216 / 637) (-8646 / 4459) (1196 / 343)
          (-1202 / 637) 0 0 y := by
            apply intervalIntegral.integral_congr
            intro y hy
            exact unequalDampedMinusG3Integrand_eq_combination n y
    _ = unequalDampedMinusG3Moment n := by
      rw [integral_unequalDampedMomentCombination6
        continuous_unequalDampedMinusMomentIntegrand
        integral_unequalDampedMinusMomentIntegrand]
      unfold unequalDampedMinusG3Moment
      ring

/-- The plus-side integrated coefficient before the final rational collapse. -/
def unequalDampedPlusIntegratedCoeff (n : ℕ) : ℝ :=
  (Nat.choose (n + 5) 5 : ℝ) * unequalDampedPlusG0Moment n
    + (Nat.choose (n + 4) 5 : ℝ) * unequalDampedPlusG1Moment n
    + (Nat.choose (n + 3) 5 : ℝ) * unequalDampedPlusG2Moment n
    + (Nat.choose (n + 2) 5 : ℝ) * unequalDampedPlusG3Moment n

/-- The swapped-side integrated coefficient before the rational collapse. -/
def unequalDampedMinusIntegratedCoeff (n : ℕ) : ℝ :=
  (Nat.choose (n + 5) 5 : ℝ) * unequalDampedMinusG0Moment n
    + (Nat.choose (n + 4) 5 : ℝ) * unequalDampedMinusG1Moment n
    + (Nat.choose (n + 3) 5 : ℝ) * unequalDampedMinusG2Moment n
    + (Nat.choose (n + 2) 5 : ℝ) * unequalDampedMinusG3Moment n

theorem unequalDampedPlusIntegratedCoeff_eq (n : ℕ) :
    unequalDampedPlusIntegratedCoeff n = unequalDampedPlusCoeff n := by
  rw [show unequalDampedPlusIntegratedCoeff n
      = unequalDampedPlusMoment n * unequalDampedPlusRawFactor n by
        unfold unequalDampedPlusIntegratedCoeff unequalDampedPlusRawFactor
        rw [unequalDampedPlusG0Moment_eq, unequalDampedPlusG1Moment_eq,
          unequalDampedPlusG2Moment_eq, unequalDampedPlusG3Moment_eq]
        ring]
  rw [unequalDampedPlusRawFactor_eq,
    unequalDampedPlusMoment_mul_tailFactor_eq_coeff]

theorem unequalDampedMinusIntegratedCoeff_eq (n : ℕ) :
    unequalDampedMinusIntegratedCoeff n = unequalDampedMinusCoeff n := by
  rw [show unequalDampedMinusIntegratedCoeff n
      = unequalDampedMinusMoment n * unequalDampedMinusRawFactor n by
        unfold unequalDampedMinusIntegratedCoeff unequalDampedMinusRawFactor
        rw [unequalDampedMinusG0Moment_eq, unequalDampedMinusG1Moment_eq,
          unequalDampedMinusG2Moment_eq, unequalDampedMinusG3Moment_eq]
        ring]
  rw [unequalDampedMinusRawFactor_eq,
    unequalDampedMinusMoment_mul_tailFactor_eq_coeff]

/-- A four-term linear combination of functions. -/
def unequalDampedFunctionCombination4
    (f0 f1 f2 f3 : ℝ → ℝ) (a0 a1 a2 a3 y : ℝ) : ℝ :=
  a0 * f0 y + a1 * f1 y + a2 * f2 y + a3 * f3 y

private theorem integral_unequalDampedFunctionCombination4
    {f0 f1 f2 f3 : ℝ → ℝ}
    (h0 : Continuous f0) (h1 : Continuous f1)
    (h2 : Continuous f2) (h3 : Continuous f3)
    (a0 a1 a2 a3 : ℝ) :
    (∫ y in (0 : ℝ)..1,
      unequalDampedFunctionCombination4 f0 f1 f2 f3
        a0 a1 a2 a3 y)
      =
    a0 * (∫ y in (0 : ℝ)..1, f0 y)
      + a1 * (∫ y in (0 : ℝ)..1, f1 y)
      + a2 * (∫ y in (0 : ℝ)..1, f2 y)
      + a3 * (∫ y in (0 : ℝ)..1, f3 y) := by
  have hi0 : IntervalIntegrable (fun y => a0 * f0 y) volume 0 1 :=
    (h0.intervalIntegrable 0 1).const_mul a0
  have hi1 : IntervalIntegrable (fun y => a1 * f1 y) volume 0 1 :=
    (h1.intervalIntegrable 0 1).const_mul a1
  have hi2 : IntervalIntegrable (fun y => a2 * f2 y) volume 0 1 :=
    (h2.intervalIntegrable 0 1).const_mul a2
  have hi3 : IntervalIntegrable (fun y => a3 * f3 y) volume 0 1 :=
    (h3.intervalIntegrable 0 1).const_mul a3
  unfold unequalDampedFunctionCombination4
  rw [intervalIntegral.integral_add ((hi0.add hi1).add hi2) hi3,
    intervalIntegral.integral_add (hi0.add hi1) hi2,
    intervalIntegral.integral_add hi0 hi1]
  simp only [intervalIntegral.integral_const_mul]

/-- Collected plus-side target-indexed integrand. -/
def unequalDampedPlusCollectedTermIntegrand
    (s : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  s ^ n *
    unequalDampedFunctionCombination4
      (unequalDampedPlusG0Integrand n)
      (unequalDampedPlusG1Integrand n)
      (unequalDampedPlusG2Integrand n)
      (unequalDampedPlusG3Integrand n)
      (Nat.choose (n + 5) 5 : ℝ)
      (Nat.choose (n + 4) 5 : ℝ)
      (Nat.choose (n + 3) 5 : ℝ)
      (Nat.choose (n + 2) 5 : ℝ) y

/-- Collected swapped-side target-indexed integrand. -/
def unequalDampedMinusCollectedTermIntegrand
    (s : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  s ^ n *
    unequalDampedFunctionCombination4
      (unequalDampedMinusG0Integrand n)
      (unequalDampedMinusG1Integrand n)
      (unequalDampedMinusG2Integrand n)
      (unequalDampedMinusG3Integrand n)
      (Nat.choose (n + 5) 5 : ℝ)
      (Nat.choose (n + 4) 5 : ℝ)
      (Nat.choose (n + 3) 5 : ℝ)
      (Nat.choose (n + 2) 5 : ℝ) y

theorem unequalDampedPlusPointwiseSeriesTerm_eq_collected
    (s : ℝ) (n : ℕ) (y : ℝ) :
    unequalDampedPointwiseSeriesTerm
      unequalDampedPlusDensity
      (3 / 7) (4 / 7) unequalDampedKappa13_17
      unequalDampedC13_17 unequalDampedK13_17 s y n
      =
    unequalDampedPlusCollectedTermIntegrand s n y := by
  unfold unequalDampedPointwiseSeriesTerm unequalDampedPlusCollectedTermIntegrand
    unequalDampedFunctionCombination4 unequalDampedPlusG0Integrand
    unequalDampedPlusG1Integrand unequalDampedPlusG2Integrand
    unequalDampedPlusG3Integrand unequalBinomialC0 unequalBinomialC1
    unequalBinomialC2 unequalBinomialC3
  rw [mul_pow]
  ring

theorem unequalDampedMinusPointwiseSeriesTerm_eq_collected
    (s : ℝ) (n : ℕ) (y : ℝ) :
    unequalDampedPointwiseSeriesTerm
      unequalDampedMinusDensity
      (4 / 7) (3 / 7) (-unequalDampedKappa13_17)
      unequalDampedC13_17 unequalDampedK13_17 s y n
      =
    unequalDampedMinusCollectedTermIntegrand s n y := by
  unfold unequalDampedPointwiseSeriesTerm unequalDampedMinusCollectedTermIntegrand
    unequalDampedFunctionCombination4 unequalDampedMinusG0Integrand
    unequalDampedMinusG1Integrand unequalDampedMinusG2Integrand
    unequalDampedMinusG3Integrand unequalBinomialC0 unequalBinomialC1
    unequalBinomialC2 unequalBinomialC3
  rw [mul_pow]
  ring

theorem integral_unequalDampedPlusCollectedTermIntegrand
    (s : ℝ) (n : ℕ) :
    (∫ y in (0 : ℝ)..1,
      unequalDampedPlusCollectedTermIntegrand s n y)
      = s ^ n * unequalDampedPlusIntegratedCoeff n := by
  unfold unequalDampedPlusCollectedTermIntegrand
  rw [intervalIntegral.integral_const_mul]
  rw [integral_unequalDampedFunctionCombination4
    (continuous_unequalDampedPlusG0Integrand n)
    (continuous_unequalDampedPlusG1Integrand n)
    (continuous_unequalDampedPlusG2Integrand n)
    (continuous_unequalDampedPlusG3Integrand n)]
  rw [integral_unequalDampedPlusG0Integrand,
    integral_unequalDampedPlusG1Integrand,
    integral_unequalDampedPlusG2Integrand,
    integral_unequalDampedPlusG3Integrand]
  rfl

theorem integral_unequalDampedMinusCollectedTermIntegrand
    (s : ℝ) (n : ℕ) :
    (∫ y in (0 : ℝ)..1,
      unequalDampedMinusCollectedTermIntegrand s n y)
      = s ^ n * unequalDampedMinusIntegratedCoeff n := by
  unfold unequalDampedMinusCollectedTermIntegrand
  rw [intervalIntegral.integral_const_mul]
  rw [integral_unequalDampedFunctionCombination4
    (continuous_unequalDampedMinusG0Integrand n)
    (continuous_unequalDampedMinusG1Integrand n)
    (continuous_unequalDampedMinusG2Integrand n)
    (continuous_unequalDampedMinusG3Integrand n)]
  rw [integral_unequalDampedMinusG0Integrand,
    integral_unequalDampedMinusG1Integrand,
    integral_unequalDampedMinusG2Integrand,
    integral_unequalDampedMinusG3Integrand]
  rfl

/--
The integrated plus-side target-indexed pointwise summand is exactly the
certified coefficient-series term.
-/
theorem integral_unequalDampedPlusPointwiseSeriesTerm
    (s : ℝ) (n : ℕ) :
    (∫ y in (0 : ℝ)..1,
      unequalDampedPointwiseSeriesTerm
        unequalDampedPlusDensity
        (3 / 7) (4 / 7) unequalDampedKappa13_17
        unequalDampedC13_17 unequalDampedK13_17 s y n)
      = unequalDampedPlusSeriesTerm s n := by
  calc
    (∫ y in (0 : ℝ)..1,
      unequalDampedPointwiseSeriesTerm
        unequalDampedPlusDensity
        (3 / 7) (4 / 7) unequalDampedKappa13_17
        unequalDampedC13_17 unequalDampedK13_17 s y n)
        =
      ∫ y in (0 : ℝ)..1,
        unequalDampedPlusCollectedTermIntegrand s n y := by
          apply intervalIntegral.integral_congr
          intro y hy
          exact unequalDampedPlusPointwiseSeriesTerm_eq_collected s n y
    _ = s ^ n * unequalDampedPlusIntegratedCoeff n :=
      integral_unequalDampedPlusCollectedTermIntegrand s n
    _ = unequalDampedPlusSeriesTerm s n := by
      rw [unequalDampedPlusIntegratedCoeff_eq]
      unfold unequalDampedPlusSeriesTerm
      ring

/--
The integrated swapped-side pointwise summand is exactly the corresponding
certified coefficient-series term.
-/
theorem integral_unequalDampedMinusPointwiseSeriesTerm
    (s : ℝ) (n : ℕ) :
    (∫ y in (0 : ℝ)..1,
      unequalDampedPointwiseSeriesTerm
        unequalDampedMinusDensity
        (4 / 7) (3 / 7) (-unequalDampedKappa13_17)
        unequalDampedC13_17 unequalDampedK13_17 s y n)
      = unequalDampedMinusSeriesTerm s n := by
  calc
    (∫ y in (0 : ℝ)..1,
      unequalDampedPointwiseSeriesTerm
        unequalDampedMinusDensity
        (4 / 7) (3 / 7) (-unequalDampedKappa13_17)
        unequalDampedC13_17 unequalDampedK13_17 s y n)
        =
      ∫ y in (0 : ℝ)..1,
        unequalDampedMinusCollectedTermIntegrand s n y := by
          apply intervalIntegral.integral_congr
          intro y hy
          exact unequalDampedMinusPointwiseSeriesTerm_eq_collected s n y
    _ = s ^ n * unequalDampedMinusIntegratedCoeff n :=
      integral_unequalDampedMinusCollectedTermIntegrand s n
    _ = unequalDampedMinusSeriesTerm s n := by
      rw [unequalDampedMinusIntegratedCoeff_eq]
      unfold unequalDampedMinusSeriesTerm
      ring

/-- The certified plus coefficient series sums to the analytic integral. -/
theorem hasSum_unequalDampedPlusSeriesTerm_eq_H
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasSum (unequalDampedPlusSeriesTerm s) (unequalDampedPlusH s) := by
  have h := hasSum_integral_unequalDampedPlusPointwiseSeries hs0 hs1
  convert h using 1
  funext n
  exact (integral_unequalDampedPlusPointwiseSeriesTerm s n).symm

/-- The certified swapped coefficient series sums to its analytic integral. -/
theorem hasSum_unequalDampedMinusSeriesTerm_eq_H
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasSum (unequalDampedMinusSeriesTerm s) (unequalDampedMinusH s) := by
  have h := hasSum_integral_unequalDampedMinusPointwiseSeries hs0 hs1
  convert h using 1
  funext n
  exact (integral_unequalDampedMinusPointwiseSeriesTerm s n).symm

/-- Identification of the plus analytic integral with its coefficient series. -/
theorem unequalDampedPlusH_eq_series
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalDampedPlusH s = unequalDampedPlusSeries s := by
  unfold unequalDampedPlusSeries
  exact (hasSum_unequalDampedPlusSeriesTerm_eq_H hs0 hs1).tsum_eq.symm

/-- Identification of the swapped analytic integral with its series. -/
theorem unequalDampedMinusH_eq_series
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalDampedMinusH s = unequalDampedMinusSeries s := by
  unfold unequalDampedMinusSeries
  exact (hasSum_unequalDampedMinusSeriesTerm_eq_H hs0 hs1).tsum_eq.symm

/-- Uniform negative bound for the plus-side analytic integral. -/
theorem unequalDampedPlusH_le_neg_b0
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalDampedPlusH s ≤ -unequalDampedB0 := by
  rw [unequalDampedPlusH_eq_series hs0 hs1]
  exact unequalDampedPlusSeries_le_neg_b0 hs0
    (hasSum_unequalDampedPlusSeriesTerm_eq_H hs0 hs1).summable

/-- Uniform negative bound for the swapped analytic integral. -/
theorem unequalDampedMinusH_le_neg_b0
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalDampedMinusH s ≤ -unequalDampedB0 := by
  rw [unequalDampedMinusH_eq_series hs0 hs1]
  exact unequalDampedMinusSeries_le_neg_b0 hs0
    (hasSum_unequalDampedMinusSeriesTerm_eq_H hs0 hs1).summable

theorem unequalDampedPlusH_neg
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalDampedPlusH s < 0 :=
  (unequalDampedPlusH_le_neg_b0 hs0 hs1).trans_lt
    (neg_neg_of_pos unequalDampedB0_pos)

theorem unequalDampedMinusH_neg
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalDampedMinusH s < 0 :=
  (unequalDampedMinusH_le_neg_b0 hs0 hs1).trans_lt
    (neg_neg_of_pos unequalDampedB0_pos)

end

end GraybillDeal
