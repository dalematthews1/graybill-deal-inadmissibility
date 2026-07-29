import GraybillDeal.UnequalDampedCollectedAlgebra
import GraybillDeal.UnequalDampedSeriesPointwise
import GraybillDeal.UnequalDampedSeriesSign

/-!
# Beta-moment algebra for the collected unequal series

The functions `unequalDampedPlusMoment` and
`unequalDampedMinusMoment` are the raw moments of `Beta(8,6)` and
`Beta(6,8)`.  This file proves their finite-shift recurrence and checks that
the four small collected polynomials `G₀`--`G₃` have the normalized
expectations recorded in `UnequalDampedCollectedAlgebra`.

No integration occurs here.  The next layer identifies these finite moment
combinations with the corresponding interval integrals.
-/

namespace GraybillDeal

noncomputable section

/-- Forward moment ratio for `Beta(8,6)`. -/
def unequalDampedPlusMomentRatio (n j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j,
    (8 + ((n + i : ℕ) : ℝ)) / (14 + ((n + i : ℕ) : ℝ))

/-- Forward moment ratio for `Beta(6,8)`. -/
def unequalDampedMinusMomentRatio (n j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j,
    (6 + ((n + i : ℕ) : ℝ)) / (14 + ((n + i : ℕ) : ℝ))

theorem unequalDampedPlusMoment_add (n j : ℕ) :
    unequalDampedPlusMoment (n + j)
      =
    unequalDampedPlusMoment n
      * unequalDampedPlusMomentRatio n j := by
  unfold unequalDampedPlusMoment unequalDampedPlusMomentRatio
  rw [Finset.prod_range_add]

theorem unequalDampedMinusMoment_add (n j : ℕ) :
    unequalDampedMinusMoment (n + j)
      =
    unequalDampedMinusMoment n
      * unequalDampedMinusMomentRatio n j := by
  unfold unequalDampedMinusMoment unequalDampedMinusMomentRatio
  rw [Finset.prod_range_add]

/-- Formal expectation of `y^n G₀(y)` on the plus side. -/
def unequalDampedPlusG0Moment (n : ℕ) : ℝ :=
  (-8 / 343) * unequalDampedPlusMoment (n + 1)
    + (30062 / 266511) * unequalDampedPlusMoment (n + 2)
    - (16210 / 88837) * unequalDampedPlusMoment (n + 3)
    + (18961 / 177674) * unequalDampedPlusMoment (n + 4)
    - (1045 / 76146) * unequalDampedPlusMoment (n + 5)

/-- Formal expectation of `y^n G₁(y)` on the plus side. -/
def unequalDampedPlusG1Moment (n : ℕ) : ℝ :=
  (-384 / 637) * unequalDampedPlusMoment n
    + (13829680 / 3464643) * unequalDampedPlusMoment (n + 1)
    - (34502024 / 3464643) * unequalDampedPlusMoment (n + 2)
    + (13028317 / 1154881) * unequalDampedPlusMoment (n + 3)
    - (37044377 / 6929286) * unequalDampedPlusMoment (n + 4)
    + (628045 / 989898) * unequalDampedPlusMoment (n + 5)

/-- Formal expectation of `y^n G₂(y)` on the plus side. -/
def unequalDampedPlusG2Moment (n : ℕ) : ℝ :=
  (-8576 / 164983) * unequalDampedPlusMoment n
    - (2074762 / 3464643) * unequalDampedPlusMoment (n + 1)
    + (8022661 / 2309762) * unequalDampedPlusMoment (n + 2)
    - (12681275 / 2309762) * unequalDampedPlusMoment (n + 3)
    + (101569 / 38073) * unequalDampedPlusMoment (n + 4)

/-- Formal expectation of `y^n G₃(y)` on the plus side. -/
def unequalDampedPlusG3Moment (n : ℕ) : ℝ :=
  (288 / 637) * unequalDampedPlusMoment n
    - (9150 / 4459) * unequalDampedPlusMoment (n + 1)
    + (26889 / 8918) * unequalDampedPlusMoment (n + 2)
    - (1803 / 1274) * unequalDampedPlusMoment (n + 3)

/-- Formal expectation of `y^n G₀(y)` on the swapped side. -/
def unequalDampedMinusG0Moment (n : ℕ) : ℝ :=
  (-9 / 686) * unequalDampedMinusMoment (n + 1)
    + (6082 / 88837) * unequalDampedMinusMoment (n + 2)
    - (28561 / 266511) * unequalDampedMinusMoment (n + 3)
    + (10154 / 266511) * unequalDampedMinusMoment (n + 4)
    + (1045 / 76146) * unequalDampedMinusMoment (n + 5)

/-- Formal expectation of `y^n G₁(y)` on the swapped side. -/
def unequalDampedMinusG1Moment (n : ℕ) : ℝ :=
  (-162 / 637) * unequalDampedMinusMoment n
    + (4469743 / 2309762) * unequalDampedMinusMoment (n + 1)
    - (18307076 / 3464643) * unequalDampedMinusMoment (n + 2)
    + (20157623 / 3464643) * unequalDampedMinusMoment (n + 3)
    - (421222 / 266511) * unequalDampedMinusMoment (n + 4)
    - (628045 / 989898) * unequalDampedMinusMoment (n + 5)

/-- Formal expectation of `y^n G₂(y)` on the swapped side. -/
def unequalDampedMinusG2Moment (n : ℕ) : ℝ :=
  (4824 / 164983) * unequalDampedMinusMoment n
    - (989876 / 1154881) * unequalDampedMinusMoment (n + 1)
    + (14854862 / 3464643) * unequalDampedMinusMoment (n + 2)
    - (25625632 / 3464643) * unequalDampedMinusMoment (n + 3)
    + (1948442 / 494949) * unequalDampedMinusMoment (n + 4)

/-- Formal expectation of `y^n G₃(y)` on the swapped side. -/
def unequalDampedMinusG3Moment (n : ℕ) : ℝ :=
  (216 / 637) * unequalDampedMinusMoment n
    - (8646 / 4459) * unequalDampedMinusMoment (n + 1)
    + (1196 / 343) * unequalDampedMinusMoment (n + 2)
    - (1202 / 637) * unequalDampedMinusMoment (n + 3)

macro "solve_plus_moment" : tactic =>
  `(tactic|
    (unfold unequalDampedPlusMomentRatio
     norm_num [Finset.prod_range_succ]
     push_cast
     field_simp
     ring))

macro "solve_minus_moment" : tactic =>
  `(tactic|
    (unfold unequalDampedMinusMomentRatio
     norm_num [Finset.prod_range_succ]
     push_cast
     field_simp
     ring))

theorem unequalDampedPlusG0Moment_eq (n : ℕ) :
    unequalDampedPlusG0Moment n
      = unequalDampedPlusMoment n * unequalDampedPlusE0 n := by
  unfold unequalDampedPlusG0Moment unequalDampedPlusE0
  rw [unequalDampedPlusMoment_add n 1,
    unequalDampedPlusMoment_add n 2,
    unequalDampedPlusMoment_add n 3,
    unequalDampedPlusMoment_add n 4,
    unequalDampedPlusMoment_add n 5]
  dsimp only
  solve_plus_moment

theorem unequalDampedPlusG1Moment_eq (n : ℕ) :
    unequalDampedPlusG1Moment n
      = unequalDampedPlusMoment n * unequalDampedPlusE1 n := by
  unfold unequalDampedPlusG1Moment unequalDampedPlusE1
  rw [unequalDampedPlusMoment_add n 1,
    unequalDampedPlusMoment_add n 2,
    unequalDampedPlusMoment_add n 3,
    unequalDampedPlusMoment_add n 4,
    unequalDampedPlusMoment_add n 5]
  dsimp only
  solve_plus_moment

theorem unequalDampedPlusG2Moment_eq (n : ℕ) :
    unequalDampedPlusG2Moment n
      = unequalDampedPlusMoment n * unequalDampedPlusE2 n := by
  unfold unequalDampedPlusG2Moment unequalDampedPlusE2
  rw [unequalDampedPlusMoment_add n 1,
    unequalDampedPlusMoment_add n 2,
    unequalDampedPlusMoment_add n 3,
    unequalDampedPlusMoment_add n 4]
  dsimp only
  solve_plus_moment

theorem unequalDampedPlusG3Moment_eq (n : ℕ) :
    unequalDampedPlusG3Moment n
      = unequalDampedPlusMoment n * unequalDampedPlusE3 n := by
  unfold unequalDampedPlusG3Moment unequalDampedPlusE3
  rw [unequalDampedPlusMoment_add n 1,
    unequalDampedPlusMoment_add n 2,
    unequalDampedPlusMoment_add n 3]
  dsimp only
  solve_plus_moment

theorem unequalDampedMinusG0Moment_eq (n : ℕ) :
    unequalDampedMinusG0Moment n
      = unequalDampedMinusMoment n * unequalDampedMinusE0 n := by
  unfold unequalDampedMinusG0Moment unequalDampedMinusE0
  rw [unequalDampedMinusMoment_add n 1,
    unequalDampedMinusMoment_add n 2,
    unequalDampedMinusMoment_add n 3,
    unequalDampedMinusMoment_add n 4,
    unequalDampedMinusMoment_add n 5]
  dsimp only
  solve_minus_moment

theorem unequalDampedMinusG1Moment_eq (n : ℕ) :
    unequalDampedMinusG1Moment n
      = unequalDampedMinusMoment n * unequalDampedMinusE1 n := by
  unfold unequalDampedMinusG1Moment unequalDampedMinusE1
  rw [unequalDampedMinusMoment_add n 1,
    unequalDampedMinusMoment_add n 2,
    unequalDampedMinusMoment_add n 3,
    unequalDampedMinusMoment_add n 4,
    unequalDampedMinusMoment_add n 5]
  dsimp only
  solve_minus_moment

theorem unequalDampedMinusG2Moment_eq (n : ℕ) :
    unequalDampedMinusG2Moment n
      = unequalDampedMinusMoment n * unequalDampedMinusE2 n := by
  unfold unequalDampedMinusG2Moment unequalDampedMinusE2
  rw [unequalDampedMinusMoment_add n 1,
    unequalDampedMinusMoment_add n 2,
    unequalDampedMinusMoment_add n 3,
    unequalDampedMinusMoment_add n 4]
  dsimp only
  solve_minus_moment

theorem unequalDampedMinusG3Moment_eq (n : ℕ) :
    unequalDampedMinusG3Moment n
      = unequalDampedMinusMoment n * unequalDampedMinusE3 n := by
  unfold unequalDampedMinusG3Moment unequalDampedMinusE3
  rw [unequalDampedMinusMoment_add n 1,
    unequalDampedMinusMoment_add n 2,
    unequalDampedMinusMoment_add n 3]
  dsimp only
  solve_minus_moment

/--
Multiplying the normalized plus-side factor by the raw beta moment recovers
the actual coefficient sequence, including its three exceptional displayed
values.
-/
theorem unequalDampedPlusMoment_mul_tailFactor_eq_coeff :
    ∀ n : ℕ,
      unequalDampedPlusMoment n * unequalDampedPlusTailFactor n
        = unequalDampedPlusCoeff n
  | 0 => by
      norm_num [unequalDampedPlusMoment, unequalDampedPlusTailFactor,
        unequalDampedPPlus, unequalDampedPlusCoeff]
  | 1 => by
      norm_num [unequalDampedPlusMoment, unequalDampedPlusTailFactor,
        unequalDampedPPlus, unequalDampedPlusCoeff,
        Finset.prod_range_succ]
  | 2 => by
      norm_num [unequalDampedPlusMoment, unequalDampedPlusTailFactor,
        unequalDampedPPlus, unequalDampedPlusCoeff,
        Finset.prod_range_succ]
  | n + 3 => by
      simp only [unequalDampedPlusCoeff]

/-- The corresponding identity for the swapped coefficient sequence. -/
theorem unequalDampedMinusMoment_mul_tailFactor_eq_coeff :
    ∀ n : ℕ,
      unequalDampedMinusMoment n * unequalDampedMinusTailFactor n
        = unequalDampedMinusCoeff n
  | 0 => by
      norm_num [unequalDampedMinusMoment, unequalDampedMinusTailFactor,
        unequalDampedPMinus, unequalDampedMinusCoeff]
  | 1 => by
      norm_num [unequalDampedMinusMoment, unequalDampedMinusTailFactor,
        unequalDampedPMinus, unequalDampedMinusCoeff,
        Finset.prod_range_succ]
  | 2 => by
      norm_num [unequalDampedMinusMoment, unequalDampedMinusTailFactor,
        unequalDampedPMinus, unequalDampedMinusCoeff,
        Finset.prod_range_succ]
  | n + 3 => by
      simp only [unequalDampedMinusCoeff]

end

end GraybillDeal
