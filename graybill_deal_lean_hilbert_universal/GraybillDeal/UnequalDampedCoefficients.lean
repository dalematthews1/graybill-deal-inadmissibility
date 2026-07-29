import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sign certificate for the damped unequal-size series coefficients

After termwise beta integration, both one-sided `(13,17)` series have three
exceptional coefficients followed by a common-shaped rational tail.  The
numerator quintics have mixed coefficients in `n`, but become
coefficientwise positive after the shift `n = m + 3`.

This file formalizes that finite polynomial certificate.  It is independent
of the later proof that the displayed rational expressions are indeed the
integrated coefficients.
-/

namespace GraybillDeal

noncomputable section

/-- Tail numerator on the side `θ ≥ 3/7`. -/
def unequalDampedPPlus (n : ℕ) : ℝ :=
  894726 * (n : ℝ) ^ 5
    + 5235585 * (n : ℝ) ^ 4
    - 77362658 * (n : ℝ) ^ 3
    + 302400473 * (n : ℝ) ^ 2
    - 158799882 * (n : ℝ)
    + 115066224

/-- Tail numerator after swapping the two samples. -/
def unequalDampedPMinus (n : ℕ) : ℝ :=
  2024512 * (n : ℝ) ^ 5
    + 45552308 * (n : ℝ) ^ 4
    - 182753309 * (n : ℝ) ^ 3
    + 407426571 * (n : ℝ) ^ 2
    - 272952966 * (n : ℝ)
    + 134243928

theorem unequalDampedPPlus_add_three (m : ℕ) :
    unequalDampedPPlus (m + 3)
      =
    894726 * (m : ℝ) ^ 5
      + 18656475 * (m : ℝ) ^ 4
      + 65989702 * (m : ℝ) ^ 3
      + 130434161 * (m : ℝ) ^ 2
      + 494618400 * (m : ℝ)
      + 912979872 := by
  unfold unequalDampedPPlus
  push_cast
  ring

theorem unequalDampedPMinus_add_three (m : ℕ) :
    unequalDampedPMinus (m + 3)
      =
    2024512 * (m : ℝ) ^ 5
      + 75919988 * (m : ℝ) ^ 4
      + 546080467 * (m : ℝ) ^ 3
      + 1769089662 * (m : ℝ) ^ 2
      + 2976843741 * (m : ℝ)
      + 2229578190 := by
  unfold unequalDampedPMinus
  push_cast
  ring

theorem unequalDampedPPlus_pos
    (n : ℕ) (hn : 3 ≤ n) :
    0 < unequalDampedPPlus n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm, unequalDampedPPlus_add_three]
  positivity

theorem unequalDampedPMinus_pos
    (n : ℕ) (hn : 3 ≤ n) :
    0 < unequalDampedPMinus n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm, unequalDampedPMinus_add_three]
  positivity

/-- The rational factor multiplying the positive beta moment on the plus
side for every tail index `n ≥ 3`. -/
def unequalDampedPlusTailFactor (n : ℕ) : ℝ :=
  -(((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)
      * unequalDampedPPlus n)
    /
    (989898
      * ((n + 14 : ℕ) : ℝ)
      * ((n + 15 : ℕ) : ℝ)
      * ((n + 16 : ℕ) : ℝ)
      * ((n + 17 : ℕ) : ℝ)
      * ((n + 18 : ℕ) : ℝ))

/-- The corresponding tail factor on the swapped side. -/
def unequalDampedMinusTailFactor (n : ℕ) : ℝ :=
  -(((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)
      * unequalDampedPMinus n)
    /
    (1154881
      * ((n + 14 : ℕ) : ℝ)
      * ((n + 15 : ℕ) : ℝ)
      * ((n + 16 : ℕ) : ℝ)
      * ((n + 17 : ℕ) : ℝ)
      * ((n + 18 : ℕ) : ℝ))

theorem unequalDampedPlusTailFactor_neg
    (n : ℕ) (hn : 3 ≤ n) :
    unequalDampedPlusTailFactor n < 0 := by
  unfold unequalDampedPlusTailFactor
  have hP := unequalDampedPPlus_pos n hn
  apply div_neg_of_neg_of_pos
  · exact neg_neg_of_pos (by positivity)
  · positivity

theorem unequalDampedMinusTailFactor_neg
    (n : ℕ) (hn : 3 ≤ n) :
    unequalDampedMinusTailFactor n < 0 := by
  unfold unequalDampedMinusTailFactor
  have hP := unequalDampedPMinus_pos n hn
  apply div_neg_of_neg_of_pos
  · exact neg_neg_of_pos (by positivity)
  · positivity

/-- The first three plus-side coefficients are strictly negative. -/
theorem unequalDampedPlusFirstThree_neg :
    (-2927 / 12944820 : ℝ) < 0
      ∧ (-21079 / 45306870 : ℝ) < 0
      ∧ (-6257096 / 5595398445 : ℝ) < 0 := by
  norm_num

/-- The first three swapped-side coefficients are strictly negative. -/
theorem unequalDampedMinusFirstThree_neg :
    (-2927 / 12944820 : ℝ) < 0
      ∧ (-19309 / 90613740 : ℝ) < 0
      ∧ (-2290163 / 3730265630 : ℝ) < 0 := by
  norm_num

end

end GraybillDeal
