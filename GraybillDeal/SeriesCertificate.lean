import GraybillDeal.Coefficients
import GraybillDeal.Moments
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The fixed-`n = 13` series lower bound

This file packages the coefficient and moment calculations into the lower
bound for the formal series appearing in the analytic certificate.
-/

namespace GraybillDeal

/-- The `m`th term of the fixed-`n = 13` series. -/
noncomputable def seriesTerm13 (z : ℝ) (m : ℕ) : ℝ :=
  M (m + 1) * (q13 m : ℝ) * z ^ m

/-- The sum of the fixed-`n = 13` series. -/
noncomputable def seriesSum13 (z : ℝ) : ℝ :=
  ∑' m : ℕ, seriesTerm13 z m

/-- Every term after the first three is nonnegative when `z ≥ 0`. -/
theorem seriesTerm13_add_three_nonneg {z : ℝ} (hz : 0 ≤ z) (m : ℕ) :
    0 ≤ seriesTerm13 z (m + 3) := by
  have hM : 0 ≤ M (m + 3 + 1) := M_nonneg _
  have hq : 0 ≤ (q13 (m + 3) : ℝ) := by
    exact_mod_cast q13_add_three_nonneg m
  have hzpow : 0 ≤ z ^ (m + 3) := pow_nonneg hz _
  exact mul_nonneg (mul_nonneg hM hq) hzpow

/--
For a summable series, the nonnegative tail implies that its sum is at least
the sum of its first three terms.
-/
theorem first_three_le_seriesSum13 {z : ℝ} (hz : 0 ≤ z)
    (hsum : Summable (seriesTerm13 z)) :
    seriesTerm13 z 0 + seriesTerm13 z 1 + seriesTerm13 z 2
      ≤ seriesSum13 z := by
  unfold seriesSum13
  have hfin :=
    Summable.sum_le_tsum (Finset.range 3)
      (fun i hi ↦ by
        have hi3 : 3 ≤ i := by
          simpa only [Finset.mem_range, not_lt] using hi
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hi3
        simpa [Nat.add_comm] using seriesTerm13_add_three_nonneg hz m)
      hsum
  simpa [Finset.sum_range_succ] using hfin

/-- The first three terms already contain the exact uniform certificate. -/
theorem certificate_le_first_three (z : ℝ) :
    M 1 * (1489 / 5610 : ℝ)
      ≤ seriesTerm13 z 0 + seriesTerm13 z 1 + seriesTerm13 z 2 := by
  have hquad :
      (1489 / 5610 : ℝ)
        ≤ (4 / 11 : ℝ)
          + (3 / 17) * (-116 / 33) * z
          + (15 / 323) * (232 / 11) * z ^ 2 := by
    rw [first_three_normalized_eq, certificate_quadratic_eq]
    nlinarith [sq_nonneg (z - 19 / 60)]
  calc
    M 1 * (1489 / 5610 : ℝ)
        ≤ M 1 *
          ((4 / 11 : ℝ)
            + (3 / 17) * (-116 / 33) * z
            + (15 / 323) * (232 / 11) * z ^ 2) :=
      mul_le_mul_of_nonneg_left hquad (M_nonneg 1)
    _ = seriesTerm13 z 0 + seriesTerm13 z 1 + seriesTerm13 z 2 := by
      norm_num [seriesTerm13, M_two, M_three]
      ring

/-- The formal series is bounded below by the exact positive certificate. -/
theorem certificate_le_seriesSum13 {z : ℝ} (hz : 0 ≤ z)
    (hsum : Summable (seriesTerm13 z)) :
    M 1 * (1489 / 5610 : ℝ) ≤ seriesSum13 z :=
  (certificate_le_first_three z).trans
    (first_three_le_seriesSum13 hz hsum)

theorem seriesSum13_pos {z : ℝ} (hz : 0 ≤ z)
    (hsum : Summable (seriesTerm13 z)) :
    0 < seriesSum13 z :=
  lt_of_lt_of_le
    (mul_pos M_one_pos (by norm_num))
    (certificate_le_seriesSum13 hz hsum)

end GraybillDeal
