import GraybillDeal.GeneralCoefficients
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# General formal-series certificate

This is the sample-size-generic counterpart of `SeriesCertificate.lean`.
It deliberately assumes summability: the remaining analytic task is to
identify this series with the real-power integral and justify exchanging the
sum and integral.
-/

namespace GraybillDeal

noncomputable section

def generalSeriesTerm (ν z : ℝ) (m : ℕ) : ℝ :=
  generalMoment ν (m + 1) * generalSeriesQ ν m * z ^ m

def generalSeriesSum (ν z : ℝ) : ℝ :=
  ∑' m : ℕ, generalSeriesTerm ν z m

theorem generalSeriesTerm_add_three_nonneg
    {ν z : ℝ} (hν : 9 ≤ ν) (hz : 0 ≤ z) (m : ℕ) :
    0 ≤ generalSeriesTerm ν z (m + 3) := by
  unfold generalSeriesTerm
  exact mul_nonneg
    (mul_nonneg
      (le_of_lt (generalMoment_pos (by linarith) (m + 3 + 1)))
      (le_of_lt (generalSeriesQ_add_three_pos hν m)))
    (pow_nonneg hz _)

/-- A nonnegative tail puts the full sum above its first three terms. -/
theorem general_first_three_le_seriesSum
    {ν z : ℝ} (hν : 9 ≤ ν) (hz : 0 ≤ z)
    (hsum : Summable (generalSeriesTerm ν z)) :
    generalSeriesTerm ν z 0 + generalSeriesTerm ν z 1
        + generalSeriesTerm ν z 2
      ≤ generalSeriesSum ν z := by
  unfold generalSeriesSum
  have hfin :=
    Summable.sum_le_tsum (Finset.range 3)
      (fun i hi ↦ by
        have hi3 : 3 ≤ i := by
          simpa only [Finset.mem_range, not_lt] using hi
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hi3
        simpa [Nat.add_comm] using
          generalSeriesTerm_add_three_nonneg hν hz m)
      hsum
  simpa [Finset.sum_range_succ] using hfin

theorem general_first_three_eq
    {ν z : ℝ} (hν : 9 ≤ ν) :
    generalSeriesTerm ν z 0 + generalSeriesTerm ν z 1
        + generalSeriesTerm ν z 2
      =
    generalMoment ν 1 * generalLowerQuadratic ν z := by
  simpa [generalSeriesTerm] using
    general_first_three_eq_lowerQuadratic (ν := ν) (z := z) hν

/--
Conditional on summability, the generalized series is bounded below by the
strictly positive first-three-term certificate.
-/
theorem general_lower_certificate_le_seriesSum
    (ν : ℕ) (hν : 9 ≤ ν) {z : ℝ} (hz0 : 0 ≤ z)
    (hsum : Summable (generalSeriesTerm (ν : ℝ) z)) :
    generalMoment (ν : ℝ) 1
        * generalLowerQuadratic (ν : ℝ) z
      ≤ generalSeriesSum (ν : ℝ) z := by
  rw [← general_first_three_eq (by exact_mod_cast hν)]
  exact general_first_three_le_seriesSum
    (by exact_mod_cast hν) hz0 hsum

theorem generalSeriesSum_pos
    (ν : ℕ) (hν : 9 ≤ ν) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hsum : Summable (generalSeriesTerm (ν : ℝ) z)) :
    0 < generalSeriesSum (ν : ℝ) z := by
  exact (mul_pos
      (generalMoment_pos (by
        have hνR : (9 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
        linarith) 1)
      (generalLowerQuadratic_pos_nat ν hν hz0 hz1)).trans_le
    (general_lower_certificate_le_seriesSum ν hν hz0 hsum)

end

end GraybillDeal
