import GraybillDeal.AnalyticKernel
import GraybillDeal.GeneralSeriesCertificate

/-!
# The paired kernel at arbitrary residual degrees of freedom

The denominator order in the linear-risk kernel is always five; only the
beta-density factor changes from the integer power `(1-x²)^6` at `ν=12` to
the real power `(1-x²)^(ν/2)`.  This file proves the finite algebraic pairing
identity uniformly in `ν`.
-/

namespace GraybillDeal

noncomputable section

/-- The general coefficient multiplying the linear kernel. -/
def generalAlpha (ν : ℝ) : ℝ :=
  (ν - 4) / (4 * (ν - 1))

/-- The polynomial obtained after pairing `x` and `-x`. -/
def generalPairedPolynomial (ν z y : ℝ) : ℝ :=
  let α := generalAlpha ν
  2 * α
    + (2 - 10 * α) * z
    + (-10 + 20 * α) * z * y
    + (20 - 20 * α) * z ^ 2 * y
    + (-20 + 10 * α) * z ^ 2 * y ^ 2
    + (10 - 2 * α) * z ^ 3 * y ^ 2
    - 2 * z ^ 3 * y ^ 3

/-- The rational part of the generalized linear integrand. -/
def generalLinearCore (ν s x : ℝ) : ℝ :=
  x * (s + x) * (generalAlpha ν + s * x) / (1 + s * x) ^ 5

/-- The generalized linear kernel before pairing. -/
def generalLinearKernel (ν s x : ℝ) : ℝ :=
  (1 - x ^ 2) ^ (ν / 2) * generalLinearCore ν s x

theorem generalPairedNumerator_eq (ν s x : ℝ) :
    (s + x) * (generalAlpha ν + s * x) * (1 - s * x) ^ 5
        - (s - x) * (generalAlpha ν - s * x) * (1 + s * x) ^ 5
      =
    x * generalPairedPolynomial ν (s ^ 2) (x ^ 2) := by
  unfold generalPairedPolynomial
  dsimp only
  ring

theorem generalLinearCore_add_neg
    {ν s x : ℝ} (hs : |s| < 1) (hx : |x| ≤ 1) :
    generalLinearCore ν s x + generalLinearCore ν s (-x)
      =
    x ^ 2 * generalPairedPolynomial ν (s ^ 2) (x ^ 2)
      / (1 - s ^ 2 * x ^ 2) ^ 5 := by
  have hplus : 1 + s * x ≠ 0 :=
    ne_of_gt (one_add_sx_pos hs hx)
  have hxneg : |-x| ≤ 1 := by simpa only [abs_neg] using hx
  have hminus' : 1 + s * (-x) ≠ 0 :=
    ne_of_gt (one_add_sx_pos hs hxneg)
  have hminus : 1 - s * x ≠ 0 := by
    simpa only [mul_neg, sub_eq_add_neg] using hminus'
  have hplus5 : (1 + s * x) ^ 5 ≠ 0 := pow_ne_zero 5 hplus
  have hminus5 : (1 - s * x) ^ 5 ≠ 0 := pow_ne_zero 5 hminus
  have hden :
      (1 + s * x) ^ 5 * (1 - s * x) ^ 5
        = (1 - s ^ 2 * x ^ 2) ^ 5 := by
    ring
  have hneg :
      generalLinearCore ν s (-x)
        =
      -(x * (s - x) * (generalAlpha ν - s * x)
          / (1 - s * x) ^ 5) := by
    unfold generalLinearCore
    ring
  unfold generalLinearCore
  rw [show
      (-x) * (s + -x) * (generalAlpha ν + s * -x)
          / (1 + s * -x) ^ 5
        =
      -(x * (s - x) * (generalAlpha ν - s * x)
          / (1 - s * x) ^ 5) by
        simpa only [generalLinearCore] using hneg]
  rw [← sub_eq_add_neg, div_sub_div _ _ hplus5 hminus5, hden]
  congr 1
  calc
    x * (s + x) * (generalAlpha ν + s * x) * (1 - s * x) ^ 5
          - (1 + s * x) ^ 5
              * (x * (s - x) * (generalAlpha ν - s * x))
        =
      x * ((s + x) * (generalAlpha ν + s * x) * (1 - s * x) ^ 5
          - (s - x) * (generalAlpha ν - s * x)
              * (1 + s * x) ^ 5) := by
        ring
    _ = x * (x * generalPairedPolynomial ν (s ^ 2) (x ^ 2)) := by
      rw [generalPairedNumerator_eq]
    _ = x ^ 2 * generalPairedPolynomial ν (s ^ 2) (x ^ 2) := by
      ring

/-- Exact paired-kernel identity, including the real-power beta factor. -/
theorem generalLinearKernel_add_neg
    {ν s x : ℝ} (hs : |s| < 1) (hx : |x| ≤ 1) :
    generalLinearKernel ν s x + generalLinearKernel ν s (-x)
      =
    (1 - x ^ 2) ^ (ν / 2) * x ^ 2
      * generalPairedPolynomial ν (s ^ 2) (x ^ 2)
      / (1 - s ^ 2 * x ^ 2) ^ 5 := by
  unfold generalLinearKernel
  rw [show 1 - (-x) ^ 2 = 1 - x ^ 2 by ring]
  rw [← mul_add, generalLinearCore_add_neg hs hx]
  ring

end

end GraybillDeal
