import GraybillDeal.GeometricSeries
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Shifted order-four binomial series

Leading-zero shifts of the order-four binomial geometric series, used to
reindex the seven monomials in the paired numerator.
-/

namespace GraybillDeal

noncomputable section

/-- The common sum of the unshifted order-four binomial series. -/
def shiftedBinomialD (t : ℝ) : ℝ :=
  1 / (1 - t) ^ 5

/-- The unshifted order-four binomial summand. -/
def shiftedBinomialC0 (t : ℝ) (m : ℕ) : ℝ :=
  ((m + 4).choose 4 : ℝ) * t ^ m

/-- The one-place leading-zero shift of `shiftedBinomialC0`. -/
def shiftedBinomialC1 (t : ℝ) (m : ℕ) : ℝ :=
  ((m + 3).choose 4 : ℝ) * t ^ m

/-- The two-place leading-zero shift of `shiftedBinomialC0`. -/
def shiftedBinomialC2 (t : ℝ) (m : ℕ) : ℝ :=
  ((m + 2).choose 4 : ℝ) * t ^ m

/-- The three-place leading-zero shift of `shiftedBinomialC0`. -/
def shiftedBinomialC3 (t : ℝ) (m : ℕ) : ℝ :=
  ((m + 1).choose 4 : ℝ) * t ^ m

theorem hasSum_shiftedBinomialC0 {t : ℝ} (ht : ‖t‖ < 1) :
    HasSum (shiftedBinomialC0 t) (shiftedBinomialD t) := by
  simpa [shiftedBinomialC0, shiftedBinomialD] using!
    hasSum_choose_four_mul_geometric ht

theorem hasSum_shiftedBinomialC1 {t : ℝ} (ht : ‖t‖ < 1) :
    HasSum (shiftedBinomialC1 t) (t * shiftedBinomialD t) := by
  apply (hasSum_nat_add_iff' 1).mp
  simpa [shiftedBinomialC0, shiftedBinomialC1, shiftedBinomialD,
    Finset.sum_range_succ, pow_succ, mul_assoc, mul_left_comm, mul_comm] using!
      (hasSum_shiftedBinomialC0 ht).mul_left t

theorem hasSum_shiftedBinomialC2 {t : ℝ} (ht : ‖t‖ < 1) :
    HasSum (shiftedBinomialC2 t) (t ^ 2 * shiftedBinomialD t) := by
  apply (hasSum_nat_add_iff' 2).mp
  simpa [shiftedBinomialC0, shiftedBinomialC2, shiftedBinomialD,
    Finset.sum_range_succ, pow_add, mul_assoc, mul_left_comm, mul_comm] using!
      (hasSum_shiftedBinomialC0 ht).mul_left (t ^ 2)

theorem hasSum_shiftedBinomialC3 {t : ℝ} (ht : ‖t‖ < 1) :
    HasSum (shiftedBinomialC3 t) (t ^ 3 * shiftedBinomialD t) := by
  apply (hasSum_nat_add_iff' 3).mp
  simpa [shiftedBinomialC0, shiftedBinomialC3, shiftedBinomialD,
    Finset.sum_range_succ, pow_add, mul_assoc, mul_left_comm, mul_comm] using!
      (hasSum_shiftedBinomialC0 ht).mul_left (t ^ 3)

end

end GraybillDeal
