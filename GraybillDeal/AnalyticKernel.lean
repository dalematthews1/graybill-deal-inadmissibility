import GraybillDeal.Coordinates
import Mathlib.Tactic.FieldSimp

/-!
# The paired one-dimensional kernel for `n = 13`

This file performs the algebraic part of pairing the integrand at `x` and
`-x`. The result is the rational function whose geometric-series expansion
produces the coefficients `Q_m`.
-/

namespace GraybillDeal

noncomputable section

/-- The constant appearing in the linear risk term when `ν = 12`. -/
def alpha13 : ℝ := 2 / 11

/-- The part of the linear integrand left after removing `(1-x²)⁶`. -/
def linearCore13 (s x : ℝ) : ℝ :=
  x * (s + x) * (alpha13 + s * x) / (1 + s * x) ^ 5

/-- The integrand `I(s)` before pairing `x` with `-x`. -/
def linearKernel13 (s x : ℝ) : ℝ :=
  (1 - x ^ 2) ^ 6 * linearCore13 s x

/--
The numerator left after pairing and extracting
`x² (1-x²)⁶ / (1-z y)⁵`, with `z=s²` and `y=x²`.
-/
def pairedPolynomial13 (z y : ℝ) : ℝ :=
  4 / 11 + 2 / 11 * z
    - 70 / 11 * z * y
    + 180 / 11 * z ^ 2 * y
    - 200 / 11 * z ^ 2 * y ^ 2
    + 106 / 11 * z ^ 3 * y ^ 2
    - 2 * z ^ 3 * y ^ 3

theorem one_sub_sq_mul_sq_pos {s x : ℝ}
    (hs : |s| < 1) (hx : |x| ≤ 1) :
    0 < 1 - s ^ 2 * x ^ 2 := by
  have hplus : 0 < 1 + s * x := one_add_sx_pos hs hx
  have hxneg : |-x| ≤ 1 := by simpa only [abs_neg] using hx
  have hminus' : 0 < 1 + s * (-x) := one_add_sx_pos hs hxneg
  have hminus : 0 < 1 - s * x := by
    simpa only [mul_neg, sub_eq_add_neg] using hminus'
  nlinarith [mul_pos hplus hminus]

/-- The finite numerator identity used when the two fractions are combined. -/
theorem pairedNumerator13_eq (s x : ℝ) :
    (s + x) * (alpha13 + s * x) * (1 - s * x) ^ 5
        - (s - x) * (alpha13 - s * x) * (1 + s * x) ^ 5
      =
    x * pairedPolynomial13 (s ^ 2) (x ^ 2) := by
  unfold alpha13 pairedPolynomial13
  ring

/-- Pairing identity before restoring the common factor `(1-x²)⁶`. -/
theorem linearCore13_add_neg {s x : ℝ}
    (hs : |s| < 1) (hx : |x| ≤ 1) :
    linearCore13 s x + linearCore13 s (-x)
      =
    x ^ 2 * pairedPolynomial13 (s ^ 2) (x ^ 2)
      / (1 - s ^ 2 * x ^ 2) ^ 5 := by
  have hplus : 1 + s * x ≠ 0 :=
    ne_of_gt (one_add_sx_pos hs hx)
  have hxneg : |-x| ≤ 1 := by simpa only [abs_neg] using hx
  have hminus' : 1 + s * (-x) ≠ 0 :=
    ne_of_gt (one_add_sx_pos hs hxneg)
  have hminus : 1 - s * x ≠ 0 := by
    simpa only [mul_neg, sub_eq_add_neg] using hminus'
  have hpair : 1 - s ^ 2 * x ^ 2 ≠ 0 :=
    ne_of_gt (one_sub_sq_mul_sq_pos hs hx)
  have hplus5 : (1 + s * x) ^ 5 ≠ 0 := pow_ne_zero 5 hplus
  have hminus5 : (1 - s * x) ^ 5 ≠ 0 := pow_ne_zero 5 hminus
  have hden :
      (1 + s * x) ^ 5 * (1 - s * x) ^ 5
        = (1 - s ^ 2 * x ^ 2) ^ 5 := by
    ring
  have hneg :
      linearCore13 s (-x)
        =
      -(x * (s - x) * (alpha13 - s * x) / (1 - s * x) ^ 5) := by
    unfold linearCore13
    ring
  unfold linearCore13
  rw [show
      (-x) * (s + -x) * (alpha13 + s * -x) / (1 + s * -x) ^ 5
        =
      -(x * (s - x) * (alpha13 - s * x) / (1 - s * x) ^ 5) by
        simpa only [linearCore13] using hneg]
  rw [← sub_eq_add_neg, div_sub_div _ _ hplus5 hminus5, hden]
  congr 1
  calc
    x * (s + x) * (alpha13 + s * x) * (1 - s * x) ^ 5
          - (1 + s * x) ^ 5 * (x * (s - x) * (alpha13 - s * x))
        =
      x * ((s + x) * (alpha13 + s * x) * (1 - s * x) ^ 5
          - (s - x) * (alpha13 - s * x) * (1 + s * x) ^ 5) := by
        ring
    _ = x * (x * pairedPolynomial13 (s ^ 2) (x ^ 2)) := by
      rw [pairedNumerator13_eq]
    _ = x ^ 2 * pairedPolynomial13 (s ^ 2) (x ^ 2) := by
      ring

/--
Exact paired-kernel identity. This is the finite algebraic calculation behind
the passage from equation (8) to the power series in equation (9).
-/
theorem linearKernel13_add_neg {s x : ℝ}
    (hs : |s| < 1) (hx : |x| ≤ 1) :
    linearKernel13 s x + linearKernel13 s (-x)
      =
    (1 - x ^ 2) ^ 6 * x ^ 2
      * pairedPolynomial13 (s ^ 2) (x ^ 2)
      / (1 - s ^ 2 * x ^ 2) ^ 5 := by
  unfold linearKernel13
  rw [show (1 - (-x) ^ 2) ^ 6 = (1 - x ^ 2) ^ 6 by ring]
  rw [← mul_add, linearCore13_add_neg hs hx]
  ring

end

end GraybillDeal
