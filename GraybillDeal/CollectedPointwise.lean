import GraybillDeal.ShiftedBinomialSeries
import GraybillDeal.IntegratedCoefficients

/-!
# Collected pointwise series for the paired `n = 13` kernel

The seven monomials of `pairedPolynomial13` contribute four shifted
order-four binomial series.  This file collects them by the target power of
`s²`, before integration.
-/

namespace GraybillDeal

noncomputable section

/--
The target-indexed pointwise summand obtained from all seven monomials of the
paired numerator.
-/
def collectedPointwiseSummand13 (s x : ℝ) (m : ℕ) : ℝ :=
  (1 - x ^ 2) ^ 6 *
    ((4 / 11) * x ^ 2 * shiftedBinomialC0 (s ^ 2 * x ^ 2) m
      + (2 / 11) * shiftedBinomialC1 (s ^ 2 * x ^ 2) m
      - (70 / 11) * x ^ 2 * shiftedBinomialC1 (s ^ 2 * x ^ 2) m
      + (180 / 11) * shiftedBinomialC2 (s ^ 2 * x ^ 2) m
      - (200 / 11) * x ^ 2 * shiftedBinomialC2 (s ^ 2 * x ^ 2) m
      + (106 / 11) * shiftedBinomialC3 (s ^ 2 * x ^ 2) m
      - 2 * x ^ 2 * shiftedBinomialC3 (s ^ 2 * x ^ 2) m)

/--
The collected pointwise term is the same target-indexed integrand used in the
integrated-coefficient calculation.
-/
theorem collectedPointwiseSummand13_eq_collectedIntegrand13
    (s x : ℝ) (m : ℕ) :
    collectedPointwiseSummand13 s x m = collectedIntegrand13 s x m := by
  change collectedPointwiseSummand13 s x m =
    (s ^ 2) ^ m *
      ((((m + 3).choose 4 : ℝ) * (2 / 11)
          + ((m + 2).choose 4 : ℝ) * (180 / 11)
          + ((m + 1).choose 4 : ℝ) * (106 / 11))
          * (x ^ (2 * m) * (1 - x ^ 2) ^ 6)
        + (((m + 4).choose 4 : ℝ) * (4 / 11)
            - ((m + 3).choose 4 : ℝ) * (70 / 11)
            - ((m + 2).choose 4 : ℝ) * (200 / 11)
            - ((m + 1).choose 4 : ℝ) * 2)
          * (x ^ (2 * (m + 1)) * (1 - x ^ 2) ^ 6))
  unfold collectedPointwiseSummand13
  unfold shiftedBinomialC0 shiftedBinomialC1
    shiftedBinomialC2 shiftedBinomialC3
  simp only [mul_pow, ← pow_mul, Nat.mul_add, pow_add]
  ring

/--
For `|s| < 1` and `x ∈ [0,1]`, the collected target-indexed terms sum to the
paired rational integrand.
-/
theorem hasSum_collectedPointwiseSummand13 {s x : ℝ}
    (hs : |s| < 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum
      (collectedPointwiseSummand13 s x)
      ((1 - x ^ 2) ^ 6 * x ^ 2
        * pairedPolynomial13 (s ^ 2) (x ^ 2)
        / (1 - s ^ 2 * x ^ 2) ^ 5) := by
  have hxabs : |x| ≤ 1 := by
    rw [abs_of_nonneg hx.1]
    exact hx.2
  have ht : ‖s ^ 2 * x ^ 2‖ < 1 :=
    sq_mul_sq_norm_lt_one hs hxabs
  have h0 := hasSum_shiftedBinomialC0 ht
  have h1 := hasSum_shiftedBinomialC1 ht
  have h2 := hasSum_shiftedBinomialC2 ht
  have h3 := hasSum_shiftedBinomialC3 ht
  have h01 :=
    (h0.mul_left ((4 / 11 : ℝ) * x ^ 2)).add
      (h1.mul_left (2 / 11 : ℝ))
  have h012 := h01.sub (h1.mul_left ((70 / 11 : ℝ) * x ^ 2))
  have h0123 := h012.add (h2.mul_left (180 / 11 : ℝ))
  have h01234 := h0123.sub (h2.mul_left ((200 / 11 : ℝ) * x ^ 2))
  have h012345 := h01234.add (h3.mul_left (106 / 11 : ℝ))
  have hinner := h012345.sub (h3.mul_left (2 * x ^ 2))
  have hall := hinner.mul_left ((1 - x ^ 2) ^ 6)
  convert! hall using 1
  unfold shiftedBinomialD pairedPolynomial13
  ring

end

end GraybillDeal
