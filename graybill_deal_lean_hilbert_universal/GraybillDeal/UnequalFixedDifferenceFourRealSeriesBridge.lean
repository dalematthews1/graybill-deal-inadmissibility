import GraybillDeal.UnequalFixedDifferenceFourSeriesBridge
import GraybillDeal.UnequalFixedDifferenceFourRealCoordinates
import GraybillDeal.UnequalFixedDifferenceFourRealMoments
import GraybillDeal.UnequalFixedDifferenceFourRealSeriesSign

/-!
# Real-parameter integral/series bridge for the difference-four family

The generic collected-polynomial and termwise-integration machinery is
independent of the family parameter.  This module instantiates it with the
real-parameter beta moments and coordinates for every `m ≥ 7`.

The large rational normalization identifying the polynomial coefficients
with the certified coefficient sequences is deliberately not performed here.
Instead, the final `HasSum` and uniform-bound theorems expose that exact
coefficient identity as a hypothesis.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

/-! ## Polynomial-moment coefficients -/

/--
Purely algebraic right-chart coefficient obtained by applying the real beta
moment sequence to the four collected polynomials.
-/
def unequalFixedDifferenceFourRealPlusPolynomialCoefficient
    (m : ℝ) (n : ℕ) : ℝ :=
  (Nat.choose (n + 5) 5 : ℝ)
      * unequalDampedPolynomialMoment
        (unequalFixedDifferenceFourRealPlusMoment m) n
        (unequalDampedG0Polynomial
          (unequalFixedDifferenceFourRealQ m)
          (unequalFixedDifferenceFourRealKappa m)
          (unequalFixedDifferenceFourRealC m)
          (unequalFixedDifferenceFourRealK m))
    + (Nat.choose (n + 4) 5 : ℝ)
      * unequalDampedPolynomialMoment
        (unequalFixedDifferenceFourRealPlusMoment m) n
        (unequalDampedG1Polynomial
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealQ m)
          (unequalFixedDifferenceFourRealKappa m)
          (unequalFixedDifferenceFourRealC m)
          (unequalFixedDifferenceFourRealK m))
    + (Nat.choose (n + 3) 5 : ℝ)
      * unequalDampedPolynomialMoment
        (unequalFixedDifferenceFourRealPlusMoment m) n
        (unequalDampedG2Polynomial
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealQ m)
          (unequalFixedDifferenceFourRealKappa m)
          (unequalFixedDifferenceFourRealC m)
          (unequalFixedDifferenceFourRealK m))
    + (Nat.choose (n + 2) 5 : ℝ)
      * unequalDampedPolynomialMoment
        (unequalFixedDifferenceFourRealPlusMoment m) n
        (unequalDampedG3Polynomial
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealQ m)
          (unequalFixedDifferenceFourRealC m)
          (unequalFixedDifferenceFourRealK m))

/-- Swapped-chart analogue of
`unequalFixedDifferenceFourRealPlusPolynomialCoefficient`. -/
def unequalFixedDifferenceFourRealMinusPolynomialCoefficient
    (m : ℝ) (n : ℕ) : ℝ :=
  (Nat.choose (n + 5) 5 : ℝ)
      * unequalDampedPolynomialMoment
        (unequalFixedDifferenceFourRealMinusMoment m) n
        (unequalDampedG0Polynomial
          (unequalFixedDifferenceFourRealT m)
          (-unequalFixedDifferenceFourRealKappa m)
          (unequalFixedDifferenceFourRealC m)
          (unequalFixedDifferenceFourRealK m))
    + (Nat.choose (n + 4) 5 : ℝ)
      * unequalDampedPolynomialMoment
        (unequalFixedDifferenceFourRealMinusMoment m) n
        (unequalDampedG1Polynomial
          (unequalFixedDifferenceFourRealQ m)
          (unequalFixedDifferenceFourRealT m)
          (-unequalFixedDifferenceFourRealKappa m)
          (unequalFixedDifferenceFourRealC m)
          (unequalFixedDifferenceFourRealK m))
    + (Nat.choose (n + 3) 5 : ℝ)
      * unequalDampedPolynomialMoment
        (unequalFixedDifferenceFourRealMinusMoment m) n
        (unequalDampedG2Polynomial
          (unequalFixedDifferenceFourRealQ m)
          (unequalFixedDifferenceFourRealT m)
          (-unequalFixedDifferenceFourRealKappa m)
          (unequalFixedDifferenceFourRealC m)
          (unequalFixedDifferenceFourRealK m))
    + (Nat.choose (n + 2) 5 : ℝ)
      * unequalDampedPolynomialMoment
        (unequalFixedDifferenceFourRealMinusMoment m) n
        (unequalDampedG3Polynomial
          (unequalFixedDifferenceFourRealQ m)
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealC m)
          (unequalFixedDifferenceFourRealK m))

/-! ## Integrated coefficients -/

/--
The integrated real-parameter right-chart coefficient equals its algebraic
polynomial-moment expression.
-/
theorem unequalFixedDifferenceFourRealPlusIntegratedCoefficient_eq_polynomial
    {m : ℝ} (hm : 7 ≤ m) (n : ℕ) :
    unequalDampedIntegratedCoefficient
      (unequalFixedDifferenceFourRealPlusDensity m)
      (unequalFixedDifferenceFourRealT m)
      (unequalFixedDifferenceFourRealQ m)
      (unequalFixedDifferenceFourRealKappa m)
      (unequalFixedDifferenceFourRealC m)
      (unequalFixedDifferenceFourRealK m) n
      =
    unequalFixedDifferenceFourRealPlusPolynomialCoefficient m n := by
  obtain ⟨h0, h1, h2, h3⟩ :=
    unequalDampedIntegratedGs_eq_polynomialMoments
      (continuous_unequalFixedDifferenceFourRealPlusDensity hm)
      (integral_unequalFixedDifferenceFourRealPlusDensity_pow hm)
      (unequalFixedDifferenceFourRealT m)
      (unequalFixedDifferenceFourRealQ m)
      (unequalFixedDifferenceFourRealKappa m)
      (unequalFixedDifferenceFourRealC m)
      (unequalFixedDifferenceFourRealK m) n
  unfold unequalDampedIntegratedCoefficient
    unequalFixedDifferenceFourRealPlusPolynomialCoefficient
  rw [h0, h1, h2, h3]

/--
The integrated real-parameter swapped-chart coefficient equals its algebraic
polynomial-moment expression.
-/
theorem unequalFixedDifferenceFourRealMinusIntegratedCoefficient_eq_polynomial
    {m : ℝ} (hm : 7 ≤ m) (n : ℕ) :
    unequalDampedIntegratedCoefficient
      (unequalFixedDifferenceFourRealMinusDensity m)
      (unequalFixedDifferenceFourRealQ m)
      (unequalFixedDifferenceFourRealT m)
      (-unequalFixedDifferenceFourRealKappa m)
      (unequalFixedDifferenceFourRealC m)
      (unequalFixedDifferenceFourRealK m) n
      =
    unequalFixedDifferenceFourRealMinusPolynomialCoefficient m n := by
  obtain ⟨h0, h1, h2, h3⟩ :=
    unequalDampedIntegratedGs_eq_polynomialMoments
      (continuous_unequalFixedDifferenceFourRealMinusDensity hm)
      (integral_unequalFixedDifferenceFourRealMinusDensity_pow hm)
      (unequalFixedDifferenceFourRealQ m)
      (unequalFixedDifferenceFourRealT m)
      (-unequalFixedDifferenceFourRealKappa m)
      (unequalFixedDifferenceFourRealC m)
      (unequalFixedDifferenceFourRealK m) n
  unfold unequalDampedIntegratedCoefficient
    unequalFixedDifferenceFourRealMinusPolynomialCoefficient
  rw [h0, h1, h2, h3]

/-! ## Analytic integrals and conditional series identification -/

/-- Right-chart analytic integral, for an explicitly supplied density. -/
def unequalFixedDifferenceFourRealPlusH
    (density : ℝ → ℝ) (m s : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1,
    unequalDampedHIntegrand density
      (unequalFixedDifferenceFourRealT m)
      (unequalFixedDifferenceFourRealQ m)
      (unequalFixedDifferenceFourRealKappa m)
      (unequalFixedDifferenceFourRealC m)
      (unequalFixedDifferenceFourRealK m) s y

/-- Left-chart analytic integral, for an explicitly supplied density. -/
def unequalFixedDifferenceFourRealMinusH
    (density : ℝ → ℝ) (m s : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1,
    unequalDampedHIntegrand density
      (unequalFixedDifferenceFourRealQ m)
      (unequalFixedDifferenceFourRealT m)
      (-unequalFixedDifferenceFourRealKappa m)
      (unequalFixedDifferenceFourRealC m)
      (unequalFixedDifferenceFourRealK m) s y

/--
Once the exact integrated-coefficient identity is supplied, the certified
real-parameter right-chart series sums to the analytic integral.
-/
theorem hasSum_unequalFixedDifferenceFourRealPlusSeries_of_coefficient_identity
    {density : ℝ → ℝ} (hdensity : Continuous density)
    {m : ℝ}
    (hcoeff : ∀ n : ℕ,
      unequalDampedIntegratedCoefficient density
        (unequalFixedDifferenceFourRealT m)
        (unequalFixedDifferenceFourRealQ m)
        (unequalFixedDifferenceFourRealKappa m)
        (unequalFixedDifferenceFourRealC m)
        (unequalFixedDifferenceFourRealK m) n
        =
      unequalFixedDifferenceFourRealPlusCoeff m n)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasSum
      (unequalFixedDifferenceFourRealPlusSeriesTerm m s)
      (unequalFixedDifferenceFourRealPlusH density m s) := by
  have h := hasSum_integral_unequalDampedPointwiseSeries
    hdensity
    (unequalFixedDifferenceFourRealT m)
    (unequalFixedDifferenceFourRealQ m)
    (unequalFixedDifferenceFourRealKappa m)
    (unequalFixedDifferenceFourRealC m)
    (unequalFixedDifferenceFourRealK m)
    hs0 hs1
  unfold unequalFixedDifferenceFourRealPlusH
  convert h using 1
  funext n
  rw [integral_unequalDampedPointwiseSeriesTerm_eq_integratedCoefficient
    hdensity]
  rw [hcoeff n]
  unfold unequalFixedDifferenceFourRealPlusSeriesTerm
  ring

/--
Once the exact integrated-coefficient identity is supplied, the certified
real-parameter left-chart series sums to the analytic integral.
-/
theorem hasSum_unequalFixedDifferenceFourRealMinusSeries_of_coefficient_identity
    {density : ℝ → ℝ} (hdensity : Continuous density)
    {m : ℝ}
    (hcoeff : ∀ n : ℕ,
      unequalDampedIntegratedCoefficient density
        (unequalFixedDifferenceFourRealQ m)
        (unequalFixedDifferenceFourRealT m)
        (-unequalFixedDifferenceFourRealKappa m)
        (unequalFixedDifferenceFourRealC m)
        (unequalFixedDifferenceFourRealK m) n
        =
      unequalFixedDifferenceFourRealMinusCoeff m n)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasSum
      (unequalFixedDifferenceFourRealMinusSeriesTerm m s)
      (unequalFixedDifferenceFourRealMinusH density m s) := by
  have h := hasSum_integral_unequalDampedPointwiseSeries
    hdensity
    (unequalFixedDifferenceFourRealQ m)
    (unequalFixedDifferenceFourRealT m)
    (-unequalFixedDifferenceFourRealKappa m)
    (unequalFixedDifferenceFourRealC m)
    (unequalFixedDifferenceFourRealK m)
    hs0 hs1
  unfold unequalFixedDifferenceFourRealMinusH
  convert h using 1
  funext n
  rw [integral_unequalDampedPointwiseSeriesTerm_eq_integratedCoefficient
    hdensity]
  rw [hcoeff n]
  unfold unequalFixedDifferenceFourRealMinusSeriesTerm
  ring

/-! ## Uniform bounds under coefficient identification -/

/--
The right-chart integral is uniformly bounded by the negative pivot margin
once its exact coefficient identity is known.
-/
theorem unequalFixedDifferenceFourRealPlusH_le_neg_b0_of_coefficient_identity
    {density : ℝ → ℝ} (hdensity : Continuous density)
    {m : ℝ} (hm : 7 ≤ m)
    (hcoeff : ∀ n : ℕ,
      unequalDampedIntegratedCoefficient density
        (unequalFixedDifferenceFourRealT m)
        (unequalFixedDifferenceFourRealQ m)
        (unequalFixedDifferenceFourRealKappa m)
        (unequalFixedDifferenceFourRealC m)
        (unequalFixedDifferenceFourRealK m) n
        =
      unequalFixedDifferenceFourRealPlusCoeff m n)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourRealPlusH density m s
      ≤ -unequalFixedDifferenceFourRealB0 m := by
  have hsum :=
    hasSum_unequalFixedDifferenceFourRealPlusSeries_of_coefficient_identity
      hdensity hcoeff hs0 hs1
  rw [← hsum.tsum_eq]
  exact unequalFixedDifferenceFourRealPlusSeries_le_neg_b0
    hm hs0 hsum.summable

/--
The left-chart integral has the same uniform negative bound once its exact
coefficient identity is known.
-/
theorem unequalFixedDifferenceFourRealMinusH_le_neg_b0_of_coefficient_identity
    {density : ℝ → ℝ} (hdensity : Continuous density)
    {m : ℝ} (hm : 7 ≤ m)
    (hcoeff : ∀ n : ℕ,
      unequalDampedIntegratedCoefficient density
        (unequalFixedDifferenceFourRealQ m)
        (unequalFixedDifferenceFourRealT m)
        (-unequalFixedDifferenceFourRealKappa m)
        (unequalFixedDifferenceFourRealC m)
        (unequalFixedDifferenceFourRealK m) n
        =
      unequalFixedDifferenceFourRealMinusCoeff m n)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourRealMinusH density m s
      ≤ -unequalFixedDifferenceFourRealB0 m := by
  have hsum :=
    hasSum_unequalFixedDifferenceFourRealMinusSeries_of_coefficient_identity
      hdensity hcoeff hs0 hs1
  rw [← hsum.tsum_eq]
  exact unequalFixedDifferenceFourRealMinusSeries_le_neg_b0
    hm hs0 hsum.summable

end

end GraybillDeal
