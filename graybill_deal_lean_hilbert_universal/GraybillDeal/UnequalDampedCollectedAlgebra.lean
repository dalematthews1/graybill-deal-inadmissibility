import GraybillDeal.UnequalDampedCoefficients
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp

/-!
# Collected coefficient algebra for the damped unequal-size series

After factoring the `n`th beta moment from the four integrated collected
numerators, the remaining expectations are the rational functions `E0`--`E3`
below.  Multiplying them by the four shifted order-five binomial
coefficients collapses exactly to the tail factors certified in
`UnequalDampedCoefficients`.

This file proves that last rational identity.  The separate moment-integration
file will show that these rational functions are indeed the normalized
integrals of `G₀`--`G₃`.
-/

namespace GraybillDeal

noncomputable section

private theorem cast_choose_two_poly (m : ℕ) :
    (Nat.choose m 2 : ℝ) =
      (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  cases m with
  | zero => norm_num [Nat.choose]
  | succ m =>
      rw [Nat.cast_choose_two]

private theorem cast_choose_three_poly (m : ℕ) :
    (Nat.choose m 3 : ℝ) =
      (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) / 6 := by
  induction m with
  | zero => norm_num [Nat.choose]
  | succ m ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.cast_add, Nat.cast_succ]
      rw [cast_choose_two_poly, ih]
      ring

private theorem cast_choose_four_poly (m : ℕ) :
    (Nat.choose m 4 : ℝ) =
      (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2)
        * ((m : ℝ) - 3) / 24 := by
  induction m with
  | zero => norm_num [Nat.choose]
  | succ m ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.cast_add, Nat.cast_succ]
      rw [cast_choose_three_poly, ih]
      ring

private theorem cast_choose_five_poly (m : ℕ) :
    (Nat.choose m 5 : ℝ) =
      (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2)
        * ((m : ℝ) - 3) * ((m : ℝ) - 4) / 120 := by
  induction m with
  | zero => norm_num [Nat.choose]
  | succ m ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.cast_add, Nat.cast_succ]
      rw [cast_choose_four_poly, ih]
      ring

/-- Normalized integral of the plus-side `G₀`. -/
def unequalDampedPlusE0 (n : ℕ) : ℝ :=
  let x : ℝ := n
  (-((x + 8)
      * (999 * x ^ 3 + 21450 * x ^ 2 + 53653 * x + 368802))
    /
    (12691 * (x + 14) * (x + 15) * (x + 16)
      * (x + 17) * (x + 18)))

/-- Normalized integral of the plus-side `G₁`. -/
def unequalDampedPlusE1 (n : ℕ) : ℝ :=
  let x : ℝ := n
  ((290709 * x ^ 4 + 6389340 * x ^ 3 + 29831873 * x ^ 2
      + 324951946 * x - 236575728)
    /
    (164983 * (x + 14) * (x + 15) * (x + 16)
      * (x + 17) * (x + 18)))

/-- Normalized integral of the plus-side `G₂`. -/
def unequalDampedPlusE2 (n : ℕ) : ℝ :=
  let x : ℝ := n
  (-(542457 * x ^ 3 + 5188080 * x ^ 2
      + 15206527 * x + 93286904)
    /
    (164983 * (x + 14) * (x + 15) * (x + 16) * (x + 17)))

/-- Normalized integral of the plus-side `G₃`. -/
def unequalDampedPlusE3 (n : ℕ) : ℝ :=
  let x : ℝ := n
  (9 * (795 * x ^ 2 - 961 * x + 16696)
    /
    (4459 * (x + 14) * (x + 15) * (x + 16)))

/-- Normalized integral of the swapped-side `G₀`. -/
def unequalDampedMinusE0 (n : ℕ) : ℝ :=
  let x : ℝ := n
  (-(8 * (x + 6)
      * (2072 * x ^ 3 + 34134 * x ^ 2 + 34042 * x + 430269))
    /
    (88837 * (x + 14) * (x + 15) * (x + 16)
      * (x + 17) * (x + 18)))

/-- Normalized integral of the swapped-side `G₁`. -/
def unequalDampedMinusE1 (n : ℕ) : ℝ :=
  let x : ℝ := n
  (24 * (259000 * x ^ 4 + 4422902 * x ^ 3
      + 13477962 * x ^ 2 + 152592647 * x - 113043678)
    /
    (1154881 * (x + 14) * (x + 15) * (x + 16)
      * (x + 17) * (x + 18)))

/-- Normalized integral of the swapped-side `G₂`. -/
def unequalDampedMinusE2 (n : ℕ) : ℝ :=
  let x : ℝ := n
  (-(48 * (245532 * x ^ 3 + 1879271 * x ^ 2
      + 6070019 * x + 16229550))
    /
    (1154881 * (x + 14) * (x + 15) * (x + 16) * (x + 17)))

/-- Normalized integral of the swapped-side `G₃`. -/
def unequalDampedMinusE3 (n : ℕ) : ℝ :=
  let x : ℝ := n
  (16 * (1396 * x ^ 2 - 347 * x + 15702)
    /
    (4459 * (x + 14) * (x + 15) * (x + 16)))

/-- The plus-side coefficient after factoring out its positive beta moment. -/
def unequalDampedPlusRawFactor (n : ℕ) : ℝ :=
  (Nat.choose (n + 5) 5 : ℝ) * unequalDampedPlusE0 n
    + (Nat.choose (n + 4) 5 : ℝ) * unequalDampedPlusE1 n
    + (Nat.choose (n + 3) 5 : ℝ) * unequalDampedPlusE2 n
    + (Nat.choose (n + 2) 5 : ℝ) * unequalDampedPlusE3 n

/-- The swapped-side coefficient after factoring out its beta moment. -/
def unequalDampedMinusRawFactor (n : ℕ) : ℝ :=
  (Nat.choose (n + 5) 5 : ℝ) * unequalDampedMinusE0 n
    + (Nat.choose (n + 4) 5 : ℝ) * unequalDampedMinusE1 n
    + (Nat.choose (n + 3) 5 : ℝ) * unequalDampedMinusE2 n
    + (Nat.choose (n + 2) 5 : ℝ) * unequalDampedMinusE3 n

theorem unequalDampedPlusRawFactor_eq (n : ℕ) :
    unequalDampedPlusRawFactor n
      = unequalDampedPlusTailFactor n := by
  unfold unequalDampedPlusRawFactor unequalDampedPlusE0
    unequalDampedPlusE1 unequalDampedPlusE2 unequalDampedPlusE3
    unequalDampedPlusTailFactor unequalDampedPPlus
  dsimp only
  rw [cast_choose_five_poly (n + 5), cast_choose_five_poly (n + 4),
    cast_choose_five_poly (n + 3), cast_choose_five_poly (n + 2)]
  push_cast
  field_simp
  ring

theorem unequalDampedMinusRawFactor_eq (n : ℕ) :
    unequalDampedMinusRawFactor n
      = unequalDampedMinusTailFactor n := by
  unfold unequalDampedMinusRawFactor unequalDampedMinusE0
    unequalDampedMinusE1 unequalDampedMinusE2 unequalDampedMinusE3
    unequalDampedMinusTailFactor unequalDampedPMinus
  dsimp only
  rw [cast_choose_five_poly (n + 5), cast_choose_five_poly (n + 4),
    cast_choose_five_poly (n + 3), cast_choose_five_poly (n + 2)]
  push_cast
  field_simp
  ring

end

end GraybillDeal
