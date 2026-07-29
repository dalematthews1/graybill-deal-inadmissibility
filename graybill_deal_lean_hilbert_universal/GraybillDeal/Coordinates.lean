import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Coordinate identities for the `n = 13` Graybill--Deal certificate

This file contains the elementary change-of-variables identities used after
writing `s = 2 * θ - 1` and `x = 2 * P - 1`.
-/

namespace GraybillDeal

noncomputable section

/-- The cubic factor in the proposed perturbation of the Graybill--Deal weight. -/
def p (r : ℝ) : ℝ := r * (1 - r) * (1 - 2 * r)

/-- Recover `θ` from the centered coordinate `s = 2 * θ - 1`. -/
def thetaOfS (s : ℝ) : ℝ := (1 + s) / 2

/-- The denominator `d = θP + (1-θ)(1-P)` in centered coordinates. -/
def dSX (s x : ℝ) : ℝ := (1 + s * x) / 2

/-- The Graybill--Deal variance weight in centered coordinates. -/
def rSX (s x : ℝ) : ℝ :=
  (1 + s) * (1 + x) / (2 * (1 + s * x))

/--
For an interior variance ratio (`|s| < 1`) and `x ∈ [-1,1]`, the denominator
appearing in `dSX` and `rSX` is strictly positive.
-/
theorem one_add_sx_pos {s x : ℝ} (hs : |s| < 1) (hx : |x| ≤ 1) :
    0 < 1 + s * x := by
  have hs0 : 0 ≤ |s| := abs_nonneg s
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hsx : |s * x| < 1 := by
    rw [abs_mul]
    nlinarith
  linarith [(abs_lt.mp hsx).1]

/-- Exact expression for `r - θ` in the centered `(s,x)` coordinates. -/
theorem rSX_sub_thetaOfS {s x : ℝ} (hs : |s| < 1) (hx : |x| ≤ 1) :
    rSX s x - thetaOfS s =
      (1 - s ^ 2) * x / (2 * (1 + s * x)) := by
  have hne : 1 + s * x ≠ 0 := ne_of_gt (one_add_sx_pos hs hx)
  unfold rSX thetaOfS
  field_simp [hne]
  ring

/-- Exact expression for `p(r)` in the centered `(s,x)` coordinates. -/
theorem p_rSX {s x : ℝ} (hs : |s| < 1) (hx : |x| ≤ 1) :
    p (rSX s x) =
      -((1 - s ^ 2) * (1 - x ^ 2) * (s + x))
        / (4 * (1 + s * x) ^ 3) := by
  have hne : 1 + s * x ≠ 0 := ne_of_gt (one_add_sx_pos hs hx)
  unfold p rSX
  field_simp [hne]
  ring

/--
The numerator bound used in controlling the quadratic risk term:
`(s+x)² ≤ (1+s*x)²` on the square `[-1,1]²`.
-/
theorem sq_add_le_sq_one_add_mul {s x : ℝ}
    (hs : |s| ≤ 1) (hx : |x| ≤ 1) :
    (s + x) ^ 2 ≤ (1 + s * x) ^ 2 := by
  rcases abs_le.mp hs with ⟨hs_lower, hs_upper⟩
  rcases abs_le.mp hx with ⟨hx_lower, hx_upper⟩
  have hs_left : 0 ≤ 1 + s := by linarith
  have hs_right : 0 ≤ 1 - s := by linarith
  have hx_left : 0 ≤ 1 + x := by linarith
  have hx_right : 0 ≤ 1 - x := by linarith
  have hs_sq : 0 ≤ 1 - s ^ 2 := by
    nlinarith [mul_nonneg hs_left hs_right]
  have hx_sq : 0 ≤ 1 - x ^ 2 := by
    nlinarith [mul_nonneg hx_left hx_right]
  nlinarith [mul_nonneg hs_sq hx_sq]

end

end GraybillDeal
