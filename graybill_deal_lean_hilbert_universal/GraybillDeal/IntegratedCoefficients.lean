import GraybillDeal.SeriesIntegration
import GraybillDeal.MomentRecurrence
import GraybillDeal.SeriesCoefficients
import GraybillDeal.SeriesCertificate

/-!
# Integrated coefficients of the paired kernel series

This file collects equal powers of `s²` in the seven monomials of
`pairedPolynomial13`.  The resulting target-indexed integrand has integral
equal to `seriesTerm13 (s²) m`.
-/

namespace GraybillDeal

noncomputable section

def momentDensity13 (j : ℕ) (x : ℝ) : ℝ :=
  x ^ (2 * j) * (1 - x ^ 2) ^ 6

def collectedMomentCoeff13 (m : ℕ) : ℝ :=
  ((m + 3).choose 4 : ℝ) * (2 / 11)
    + ((m + 2).choose 4 : ℝ) * (180 / 11)
    + ((m + 1).choose 4 : ℝ) * (106 / 11)

def collectedNextCoeff13 (m : ℕ) : ℝ :=
  ((m + 4).choose 4 : ℝ) * (4 / 11)
    - ((m + 3).choose 4 : ℝ) * (70 / 11)
    - ((m + 2).choose 4 : ℝ) * (200 / 11)
    - ((m + 1).choose 4 : ℝ) * 2

/--
The coefficient of `(s²)^m` after collecting the seven shifted monomial
series, before applying the moment recurrence.
-/
def integratedCoefficient13 (m : ℕ) : ℝ :=
  collectedMomentCoeff13 m * M m
    + collectedNextCoeff13 m * M (m + 1)

/-- The target-indexed collected integrand for the coefficient of `(s²)^m`. -/
def collectedIntegrand13 (s x : ℝ) (m : ℕ) : ℝ :=
  (s ^ 2) ^ m *
    (collectedMomentCoeff13 m * momentDensity13 m x
      + collectedNextCoeff13 m * momentDensity13 (m + 1) x)

/--
The same collected integrand with the four shifted negative-binomial
coefficients left visible.  These are respectively the contributions with
shifts zero, one, two, and three in the power of `s²`.
-/
def collectedSevenIntegrand13 (s x : ℝ) (m : ℕ) : ℝ :=
  (s ^ 2) ^ m *
    (((m + 4).choose 4 : ℝ) * (4 / 11) * momentDensity13 (m + 1) x
      + ((m + 3).choose 4 : ℝ) *
        ((2 / 11) * momentDensity13 m x
          - (70 / 11) * momentDensity13 (m + 1) x)
      + ((m + 2).choose 4 : ℝ) *
        ((180 / 11) * momentDensity13 m x
          - (200 / 11) * momentDensity13 (m + 1) x)
      + ((m + 1).choose 4 : ℝ) *
        ((106 / 11) * momentDensity13 m x
          - 2 * momentDensity13 (m + 1) x))

theorem collectedSevenIntegrand13_eq (s x : ℝ) (m : ℕ) :
    collectedSevenIntegrand13 s x m = collectedIntegrand13 s x m := by
  unfold collectedSevenIntegrand13 collectedIntegrand13
    collectedMomentCoeff13 collectedNextCoeff13
  ring

private theorem M_eq_ratio_mul_succ (m : ℕ) :
    M m =
      ((2 * m + 15 : ℝ) / (2 * m + 1 : ℝ)) * M (m + 1) := by
  have hden : (2 * m + 1 : ℝ) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hden).mpr
  simpa only [mul_comm] using M_recurrence m

private theorem rawQ13_cast_eq (m : ℕ) :
    (rawQ13 m : ℝ) =
      ((m + 4).choose 4 : ℝ) * (4 / 11)
        + ((m + 3).choose 4 : ℝ)
          * ((2 / 11) * ((2 * m + 15 : ℝ) / (2 * m + 1 : ℝ)) - 70 / 11)
        + ((m + 2).choose 4 : ℝ)
          * ((180 / 11) * ((2 * m + 15 : ℝ) / (2 * m + 1 : ℝ)) - 200 / 11)
        + ((m + 1).choose 4 : ℝ)
          * ((106 / 11) * ((2 * m + 15 : ℝ) / (2 * m + 1 : ℝ)) - 2) := by
  unfold rawQ13
  push_cast
  ring

/--
After the moment recurrence, the collected coefficient is exactly the
certified coefficient `M (m+1) * q13 m`.
-/
theorem integratedCoefficient13_eq (m : ℕ) :
    integratedCoefficient13 m = M (m + 1) * (q13 m : ℝ) := by
  rw [← rawQ13_eq_q13]
  unfold integratedCoefficient13 collectedMomentCoeff13 collectedNextCoeff13
  rw [M_eq_ratio_mul_succ m, rawQ13_cast_eq]
  ring

/-- Integration of a moment density recovers `M`. -/
private theorem integral_momentDensity13 (j : ℕ) :
    (∫ x in (0 : ℝ)..1, momentDensity13 j x) = M j := by
  rfl

/--
The integral of the target-indexed collected integrand is the `m`th term of
the certified series.
-/
theorem integral_collectedIntegrand13 (s : ℝ) (m : ℕ) :
    (∫ x in (0 : ℝ)..1, collectedIntegrand13 s x m)
      = seriesTerm13 (s ^ 2) m := by
  calc
    (∫ x in (0 : ℝ)..1, collectedIntegrand13 s x m)
        = (s ^ 2) ^ m * integratedCoefficient13 m := by
      unfold collectedIntegrand13 integratedCoefficient13
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_add
        ((by
          unfold momentDensity13
          fun_prop : Continuous fun x : ℝ =>
            collectedMomentCoeff13 m * momentDensity13 m x).intervalIntegrable 0 1)
        ((by
          unfold momentDensity13
          fun_prop : Continuous fun x : ℝ =>
            collectedNextCoeff13 m *
              momentDensity13 (m + 1) x).intervalIntegrable 0 1)]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        integral_momentDensity13, integral_momentDensity13]
    _ = seriesTerm13 (s ^ 2) m := by
      rw [integratedCoefficient13_eq]
      unfold seriesTerm13
      ring

/--
Per target power, the visibly collected seven monomial contributions
integrate to the certified series term.
-/
theorem integral_collectedSevenIntegrand13 (s : ℝ) (m : ℕ) :
    (∫ x in (0 : ℝ)..1, collectedSevenIntegrand13 s x m)
      = seriesTerm13 (s ^ 2) m := by
  apply (intervalIntegral.integral_congr fun x hx =>
    collectedSevenIntegrand13_eq s x m).trans
  exact integral_collectedIntegrand13 s m

/-- The collected integral sequence has `tsum` equal to `seriesSum13`. -/
theorem tsum_integral_collectedSevenIntegrand13 (s : ℝ) :
    (∑' m : ℕ, ∫ x in (0 : ℝ)..1, collectedSevenIntegrand13 s x m)
      = seriesSum13 (s ^ 2) := by
  unfold seriesSum13
  apply tsum_congr
  intro m
  exact integral_collectedSevenIntegrand13 s m

end

end GraybillDeal
