import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Order-five binomial series for the damped unequal-size certificate

The one-sided `(13,17)` kernels have denominator `(1 - s*y)^6`.  This file
specializes Mathlib's negative-binomial series to exponent six and records
the three leading-zero shifts needed when a degree-three polynomial in `s`
is multiplied into that series.
-/

namespace GraybillDeal

noncomputable section

/-- The common closed form of the order-five negative-binomial series. -/
def unequalBinomialD6 (t : ℝ) : ℝ :=
  1 / (1 - t) ^ 6

/-- The unshifted order-five negative-binomial summand. -/
def unequalBinomialC0 (t : ℝ) (m : ℕ) : ℝ :=
  ((m + 5).choose 5 : ℝ) * t ^ m

/-- The one-place leading-zero shift. -/
def unequalBinomialC1 (t : ℝ) (m : ℕ) : ℝ :=
  ((m + 4).choose 5 : ℝ) * t ^ m

/-- The two-place leading-zero shift. -/
def unequalBinomialC2 (t : ℝ) (m : ℕ) : ℝ :=
  ((m + 3).choose 5 : ℝ) * t ^ m

/-- The three-place leading-zero shift. -/
def unequalBinomialC3 (t : ℝ) (m : ℕ) : ℝ :=
  ((m + 2).choose 5 : ℝ) * t ^ m

theorem hasSum_choose_five_mul_geometric
    {t : ℝ} (ht : ‖t‖ < 1) :
    HasSum (unequalBinomialC0 t) (unequalBinomialD6 t) := by
  change HasSum
    (fun m : ℕ => ((m + 5).choose 5 : ℝ) * t ^ m)
    (1 / (1 - t) ^ 6)
  simpa using
    hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 5 ht

theorem summable_choose_five_mul_geometric
    {t : ℝ} (ht : ‖t‖ < 1) :
    Summable (unequalBinomialC0 t) :=
  (hasSum_choose_five_mul_geometric ht).summable

theorem hasSum_unequalBinomialC1
    {t : ℝ} (ht : ‖t‖ < 1) :
    HasSum (unequalBinomialC1 t) (t * unequalBinomialD6 t) := by
  apply (hasSum_nat_add_iff' 1).mp
  simpa [unequalBinomialC0, unequalBinomialC1, unequalBinomialD6,
    Finset.sum_range_succ, pow_succ, mul_assoc, mul_left_comm, mul_comm] using!
      (hasSum_choose_five_mul_geometric ht).mul_left t

theorem hasSum_unequalBinomialC2
    {t : ℝ} (ht : ‖t‖ < 1) :
    HasSum (unequalBinomialC2 t) (t ^ 2 * unequalBinomialD6 t) := by
  apply (hasSum_nat_add_iff' 2).mp
  simpa [unequalBinomialC0, unequalBinomialC2, unequalBinomialD6,
    Finset.sum_range_succ, pow_add, mul_assoc, mul_left_comm, mul_comm] using!
      (hasSum_choose_five_mul_geometric ht).mul_left (t ^ 2)

theorem hasSum_unequalBinomialC3
    {t : ℝ} (ht : ‖t‖ < 1) :
    HasSum (unequalBinomialC3 t) (t ^ 3 * unequalBinomialD6 t) := by
  apply (hasSum_nat_add_iff' 3).mp
  simpa [unequalBinomialC0, unequalBinomialC3, unequalBinomialD6,
    Finset.sum_range_succ, pow_add, mul_assoc, mul_left_comm, mul_comm] using!
      (hasSum_choose_five_mul_geometric ht).mul_left (t ^ 3)

/-- On the unit square with `s < 1`, the product `s*y` lies inside the
radius of convergence. -/
theorem norm_mul_lt_one_of_mem_unit
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖s * y‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs0 hy0)]
  nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hy1)]

/-- The pointwise expansion used by both one-sided certificates. -/
theorem hasSum_unequal_oneSided_denominator
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    HasSum
      (fun m : ℕ => ((m + 5).choose 5 : ℝ) * (s * y) ^ m)
      (1 / (1 - s * y) ^ 6) := by
  change HasSum (unequalBinomialC0 (s * y))
    (unequalBinomialD6 (s * y))
  exact hasSum_choose_five_mul_geometric
    (norm_mul_lt_one_of_mem_unit hs0 hs1 hy0 hy1)

end

end GraybillDeal
