import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Elementary pointwise lemmas for the Graybill--Deal construction

This file contains the deterministic facts used when a perturbed weight is
projected back to the interval `[0, 1]`.  No probability or integration is
involved here.
-/

namespace GraybillDeal

/-- Projection of a real number onto the closed interval `[0, 1]`. -/
def clip01 (x : ℝ) : ℝ :=
  min 1 (max 0 x)

@[simp]
theorem clip01_of_nonpos {x : ℝ} (hx : x ≤ 0) : clip01 x = 0 := by
  simp [clip01, hx]

@[simp]
theorem clip01_of_one_le {x : ℝ} (hx : 1 ≤ x) : clip01 x = 1 := by
  simp [clip01, hx]

@[simp]
theorem clip01_of_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    clip01 x = x := by
  simp [clip01, hx.1, hx.2]

theorem clip01_nonneg (x : ℝ) : 0 ≤ clip01 x := by
  simp [clip01]

theorem clip01_le_one (x : ℝ) : clip01 x ≤ 1 := by
  simp [clip01]

theorem clip01_mem_Icc (x : ℝ) : clip01 x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨clip01_nonneg x, clip01_le_one x⟩

/--
Projection onto `[0, 1]` cannot increase squared distance from a point of
`[0, 1]`.
-/
theorem clip01_sq_sub_le_sq_sub (x θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    (clip01 x - θ) ^ 2 ≤ (x - θ) ^ 2 := by
  by_cases hx0 : x ≤ 0
  · rw [clip01_of_nonpos hx0]
    have hprod : 0 ≤ (-x) * (2 * θ - x) :=
      mul_nonneg (by linarith) (by linarith [hθ.1])
    nlinarith
  · have hx0' : 0 ≤ x := le_of_not_ge hx0
    by_cases hx1 : 1 ≤ x
    · rw [clip01_of_one_le hx1]
      have hprod : 0 ≤ (x - 1) * (x + 1 - 2 * θ) :=
        mul_nonneg (by linarith) (by linarith [hθ.2])
      nlinarith
    · rw [clip01_of_mem ⟨hx0', le_of_not_ge hx1⟩]

/-- A base weight perturbed in the direction `h` with step size `ε`. -/
def perturbation (r ε h : ℝ) : ℝ :=
  r + ε * h

/-- Exact pointwise expansion of the squared-error change under perturbation. -/
theorem perturbation_sq_sub_diff (r ε h θ : ℝ) :
    (perturbation r ε h - θ) ^ 2 - (r - θ) ^ 2
      = 2 * ε * (r - θ) * h + ε ^ 2 * h ^ 2 := by
  unfold perturbation
  ring

/-- The corresponding expansion without moving the baseline term to the left. -/
theorem perturbation_sq_sub (r ε h θ : ℝ) :
    (perturbation r ε h - θ) ^ 2
      = (r - θ) ^ 2 + 2 * ε * (r - θ) * h + ε ^ 2 * h ^ 2 := by
  unfold perturbation
  ring

/-- The affine estimate with weight `r` assigned to `x`. -/
def weightedAverage (r x y : ℝ) : ℝ :=
  r * x + (1 - r) * y

/--
Perturbing a weight by `ε h` perturbs the corresponding affine estimate by
`ε h (x - y)`.
-/
theorem weightedAverage_perturbation (r ε h x y : ℝ) :
    weightedAverage (perturbation r ε h) x y
      = weightedAverage r x y + ε * h * (x - y) := by
  unfold weightedAverage perturbation
  ring

/--
Pointwise squared-risk difference for a perturbed affine weight.  This is the
deterministic identity to which expectation will later be applied.
-/
theorem weightedAverage_perturbation_sq_error_diff
    (r ε h x y θ : ℝ) :
    (weightedAverage (perturbation r ε h) x y - θ) ^ 2
        - (weightedAverage r x y - θ) ^ 2
      =
        2 * ε * h * (x - y) * (weightedAverage r x y - θ)
          + ε ^ 2 * h ^ 2 * (x - y) ^ 2 := by
  rw [weightedAverage_perturbation]
  ring

end GraybillDeal
