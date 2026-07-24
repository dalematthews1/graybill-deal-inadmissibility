import GraybillDeal.GeneralIntegratedCoefficients
import GraybillDeal.GeneralIntegralPairing
import GraybillDeal.ShiftedBinomialSeries

/-!
# Collected pointwise series at arbitrary residual degrees of freedom

The seven monomials in `generalPairedPolynomial` give four shifted
order-four binomial series.  This module collects them by their target power
of `s²`, before integration.
-/

namespace GraybillDeal

noncomputable section

def generalMomentDensity (ν : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  x ^ (2 * j) * (1 - x ^ 2) ^ (ν / 2)

def generalCollectedIntegrand
    (ν s x : ℝ) (m : ℕ) : ℝ :=
  (s ^ 2) ^ m *
    (generalCollectedMomentCoeff ν m * generalMomentDensity ν m x
      + generalCollectedNextCoeff ν m
        * generalMomentDensity ν (m + 1) x)

/-- The visibly shifted, target-indexed pointwise summand. -/
def generalCollectedPointwiseSummand
    (ν s x : ℝ) (m : ℕ) : ℝ :=
  let α := generalAlpha ν
  (1 - x ^ 2) ^ (ν / 2) *
    ((2 * α) * x ^ 2 * shiftedBinomialC0 (s ^ 2 * x ^ 2) m
      + (2 - 10 * α) * shiftedBinomialC1 (s ^ 2 * x ^ 2) m
      + (-10 + 20 * α) * x ^ 2
          * shiftedBinomialC1 (s ^ 2 * x ^ 2) m
      + (20 - 20 * α) * shiftedBinomialC2 (s ^ 2 * x ^ 2) m
      + (-20 + 10 * α) * x ^ 2
          * shiftedBinomialC2 (s ^ 2 * x ^ 2) m
      + (10 - 2 * α) * shiftedBinomialC3 (s ^ 2 * x ^ 2) m
      - 2 * x ^ 2 * shiftedBinomialC3 (s ^ 2 * x ^ 2) m)

theorem generalCollectedPointwiseSummand_eq_collectedIntegrand
    (ν s x : ℝ) (m : ℕ) :
    generalCollectedPointwiseSummand ν s x m
      = generalCollectedIntegrand ν s x m := by
  unfold generalCollectedPointwiseSummand generalCollectedIntegrand
    generalCollectedMomentCoeff generalCollectedNextCoeff
    generalMomentDensity
  dsimp only
  unfold shiftedBinomialC0 shiftedBinomialC1
    shiftedBinomialC2 shiftedBinomialC3
  simp only [mul_pow, ← pow_mul, Nat.mul_add, pow_add]
  ring

/--
For `|s|<1` and `x∈[0,1]`, the collected target-indexed terms sum to the
paired generalized rational integrand.
-/
theorem hasSum_generalCollectedPointwiseSummand
    {ν s x : ℝ} (hs : |s| < 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum
      (generalCollectedPointwiseSummand ν s x)
      ((1 - x ^ 2) ^ (ν / 2) * x ^ 2
        * generalPairedPolynomial ν (s ^ 2) (x ^ 2)
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
  let α := generalAlpha ν
  have h01 :=
    (h0.mul_left ((2 * α) * x ^ 2)).add
      (h1.mul_left (2 - 10 * α))
  have h012 :=
    h01.add (h1.mul_left ((-10 + 20 * α) * x ^ 2))
  have h0123 :=
    h012.add (h2.mul_left (20 - 20 * α))
  have h01234 :=
    h0123.add (h2.mul_left ((-20 + 10 * α) * x ^ 2))
  have h012345 :=
    h01234.add (h3.mul_left (10 - 2 * α))
  have hinner :=
    h012345.sub (h3.mul_left (2 * x ^ 2))
  have hall :=
    hinner.mul_left ((1 - x ^ 2) ^ (ν / 2))
  convert! hall using 1
  unfold shiftedBinomialD generalPairedPolynomial
  dsimp only [α]
  ring

end

end GraybillDeal
