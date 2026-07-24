import GraybillDeal.GeometricSeries
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Pointwise series for the paired `n = 13` kernel

This file multiplies the order-four binomial geometric series by the fixed
polynomial prefactor in the paired kernel.  The resulting term definition is
intended for the later termwise-integration argument.
-/

namespace GraybillDeal

noncomputable section

/-- The factor multiplying `(1 - s²x²)⁻⁵` in the paired kernel. -/
def pairedSeriesPrefactor13 (s x : ℝ) : ℝ :=
  (1 - x ^ 2) ^ 6 * x ^ 2
    * pairedPolynomial13 (s ^ 2) (x ^ 2)

/--
The pointwise summand before integration.  Integrating this expression and
collecting equal powers of `s²` produces the coefficient sequence `Q_m`.
-/
def pointwiseSeriesTerm13 (s x : ℝ) (m : ℕ) : ℝ :=
  pairedSeriesPrefactor13 s x
    * (((m + 4).choose 4 : ℝ) * (s ^ 2 * x ^ 2) ^ m)

/--
Pointwise expansion of the paired rational kernel on `x ∈ [0,1]`.
-/
theorem hasSum_pointwiseSeries13 {s x : ℝ}
    (hs : |s| < 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum
      (pointwiseSeriesTerm13 s x)
      ((1 - x ^ 2) ^ 6 * x ^ 2
        * pairedPolynomial13 (s ^ 2) (x ^ 2)
        / (1 - s ^ 2 * x ^ 2) ^ 5) := by
  have hxabs : |x| ≤ 1 := by
    rw [abs_of_nonneg hx.1]
    exact hx.2
  have h :=
    (hasSum_paired_denominator hs hxabs).mul_left
      (pairedSeriesPrefactor13 s x)
  simpa [pointwiseSeriesTerm13, pairedSeriesPrefactor13, div_eq_mul_inv] using! h

/--
The same expansion with the sum identified directly as the paired original
linear kernel.
-/
theorem hasSum_linearKernel13_pair {s x : ℝ}
    (hs : |s| < 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum
      (pointwiseSeriesTerm13 s x)
      (linearKernel13 s x + linearKernel13 s (-x)) := by
  have hxabs : |x| ≤ 1 := by
    rw [abs_of_nonneg hx.1]
    exact hx.2
  rw [linearKernel13_add_neg hs hxabs]
  exact hasSum_pointwiseSeries13 hs hx

end

end GraybillDeal
