import GraybillDeal.UnequalDampedSeriesIntegration
import GraybillDeal.UnequalFixedDifferenceFourMoments
import GraybillDeal.UnequalFixedDifferenceFourCoordinates

/-!
# Integral/series bridge for the fixed-difference-four family

The pointwise negative-binomial expansion and its termwise interval
integration are already completely generic in the density and in the five
algebraic parameters.  This file supplies the missing generic collection
lemma: the integral of the `n`th pointwise term is `s^n` times the four
collected beta moments.

The final family theorems deliberately isolate the only remaining exact
calculation.  They assume that the four collected moments collapse to the
already-certified coefficient sequence.  Once the beta-moment module proves
that hypothesis, no further analytic interchange of sums and integrals is
needed.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

/-! ## Polynomial beta densities for interval integration -/

/--
Polynomial density of the right-chart `Beta(m+1,m-1)` law.

The natural exponents make this function continuous on all of `ℝ`, which
is the interface required by the generic termwise-integration theorem.
-/
def unequalFixedDifferenceFourPlusDensity (m : ℕ) (y : ℝ) : ℝ :=
  (1 /
      ProbabilityTheory.beta
        ((m : ℝ) + 1) ((m : ℝ) - 1))
    * y ^ m * (1 - y) ^ (m - 2)

/-- Polynomial density of the left-chart `Beta(m-1,m+1)` law. -/
def unequalFixedDifferenceFourMinusDensity (m : ℕ) (y : ℝ) : ℝ :=
  (1 /
      ProbabilityTheory.beta
        ((m : ℝ) - 1) ((m : ℝ) + 1))
    * y ^ (m - 2) * (1 - y) ^ m

theorem continuous_unequalFixedDifferenceFourPlusDensity (m : ℕ) :
    Continuous (unequalFixedDifferenceFourPlusDensity m) := by
  unfold unequalFixedDifferenceFourPlusDensity
  fun_prop

theorem continuous_unequalFixedDifferenceFourMinusDensity (m : ℕ) :
    Continuous (unequalFixedDifferenceFourMinusDensity m) := by
  unfold unequalFixedDifferenceFourMinusDensity
  fun_prop

/--
Every monomial interval moment of the polynomial right-chart density is the
finite-product beta moment used in the coefficient certificate.
-/
theorem integral_unequalFixedDifferenceFourPlusDensity_pow
    {m : ℕ} (hm : 7 ≤ m) (n : ℕ) :
    (∫ y in (0 : ℝ)..1,
      unequalFixedDifferenceFourPlusDensity m y * y ^ n)
      =
    unequalFixedDifferenceFourPlusMoment m n := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have ha : 0 < (m : ℝ) + 1 := by linarith
  have hb : 0 < (m : ℝ) - 1 := by linarith
  have hmeasure :=
    integral_pow_betaMeasure_unequalFixedDifferenceFourPlus hm n
  rw [integral_betaMeasure_eq_interval_of_shapes_pos ha hb] at hmeasure
  rw [← hmeasure]
  apply intervalIntegral.integral_congr_uIoo
  intro y hy
  rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
  have hy0 : 0 < y := hy.1
  have hy1 : 0 < 1 - y := sub_pos.mpr hy.2
  unfold unequalFixedDifferenceFourPlusDensity
  dsimp only
  have hm2 : 2 ≤ m := by omega
  have hfirst :
      y ^ ((m : ℝ) + 1 - 1) = y ^ m := by
    rw [show (m : ℝ) + 1 - 1 = (m : ℝ) by ring,
      Real.rpow_natCast]
  have hsecond :
      (1 - y) ^ ((m : ℝ) - 1 - 1) = (1 - y) ^ (m - 2) := by
    rw [show (m : ℝ) - 1 - 1 = ((m - 2 : ℕ) : ℝ) by
      rw [Nat.cast_sub hm2]
      push_cast
      ring,
      Real.rpow_natCast]
  rw [hfirst, hsecond]

/--
Every monomial interval moment of the polynomial left-chart density is the
finite-product beta moment used in the coefficient certificate.
-/
theorem integral_unequalFixedDifferenceFourMinusDensity_pow
    {m : ℕ} (hm : 7 ≤ m) (n : ℕ) :
    (∫ y in (0 : ℝ)..1,
      unequalFixedDifferenceFourMinusDensity m y * y ^ n)
      =
    unequalFixedDifferenceFourMinusMoment m n := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have ha : 0 < (m : ℝ) - 1 := by linarith
  have hb : 0 < (m : ℝ) + 1 := by linarith
  have hmeasure :=
    integral_pow_betaMeasure_unequalFixedDifferenceFourMinus hm n
  rw [integral_betaMeasure_eq_interval_of_shapes_pos ha hb] at hmeasure
  rw [← hmeasure]
  apply intervalIntegral.integral_congr_uIoo
  intro y hy
  rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
  have hy0 : 0 < y := hy.1
  have hy1 : 0 < 1 - y := sub_pos.mpr hy.2
  unfold unequalFixedDifferenceFourMinusDensity
  dsimp only
  have hm2 : 2 ≤ m := by omega
  have hfirst :
      y ^ ((m : ℝ) - 1 - 1) = y ^ (m - 2) := by
    rw [show (m : ℝ) - 1 - 1 = ((m - 2 : ℕ) : ℝ) by
      rw [Nat.cast_sub hm2]
      push_cast
      ring,
      Real.rpow_natCast]
  have hsecond :
      (1 - y) ^ ((m : ℝ) + 1 - 1) = (1 - y) ^ m := by
    rw [show (m : ℝ) + 1 - 1 = (m : ℝ) by ring,
      Real.rpow_natCast]
  rw [hfirst, hsecond]

/-! ## Generic collected integral coefficient -/

/-- Integral of the zeroth collected polynomial against `y^n density(y)`. -/
def unequalDampedIntegratedG0
    (density : ℝ → ℝ) (q κ c k : ℝ) (n : ℕ) : ℝ :=
  ∫ y in (0 : ℝ)..1,
    density y * y ^ n * unequalDampedG0 q κ c k y

/-- Integral of the first collected polynomial against `y^n density(y)`. -/
def unequalDampedIntegratedG1
    (density : ℝ → ℝ) (t q κ c k : ℝ) (n : ℕ) : ℝ :=
  ∫ y in (0 : ℝ)..1,
    density y * y ^ n * unequalDampedG1 t q κ c k y

/-- Integral of the second collected polynomial against `y^n density(y)`. -/
def unequalDampedIntegratedG2
    (density : ℝ → ℝ) (t q κ c k : ℝ) (n : ℕ) : ℝ :=
  ∫ y in (0 : ℝ)..1,
    density y * y ^ n * unequalDampedG2 t q κ c k y

/-- Integral of the third collected polynomial against `y^n density(y)`. -/
def unequalDampedIntegratedG3
    (density : ℝ → ℝ) (t q c k : ℝ) (n : ℕ) : ℝ :=
  ∫ y in (0 : ℝ)..1,
    density y * y ^ n * unequalDampedG3 t q c k y

/--
The coefficient obtained after integrating the four target-indexed
negative-binomial summands.
-/
def unequalDampedIntegratedCoefficient
    (density : ℝ → ℝ) (t q κ c k : ℝ) (n : ℕ) : ℝ :=
  (Nat.choose (n + 5) 5 : ℝ)
      * unequalDampedIntegratedG0 density q κ c k n
    + (Nat.choose (n + 4) 5 : ℝ)
      * unequalDampedIntegratedG1 density t q κ c k n
    + (Nat.choose (n + 3) 5 : ℝ)
      * unequalDampedIntegratedG2 density t q κ c k n
    + (Nat.choose (n + 2) 5 : ℝ)
      * unequalDampedIntegratedG3 density t q c k n

/-! ## Reduction of collected moments to monomial moments -/

/--
Apply a monomial moment sequence to a polynomial, with every exponent
shifted by `n`.
-/
def unequalDampedPolynomialMoment
    (moment : ℕ → ℝ) (n : ℕ) (p : Polynomial ℝ) : ℝ :=
  p.sum fun i a => a * moment (n + i)

/--
Six-term form of the polynomial moment.  All four collected polynomials
have degree at most five, so this is the convenient form for exact
coefficient normalization.
-/
def unequalDampedPolynomialMoment6
    (moment : ℕ → ℝ) (n : ℕ) (p : Polynomial ℝ) : ℝ :=
  ∑ i ∈ Finset.range 6, p.coeff i * moment (n + i)

theorem unequalDampedPolynomialMoment_eq_six
    {moment : ℕ → ℝ} {n : ℕ} {p : Polynomial ℝ}
    (hp : p.natDegree < 6) :
    unequalDampedPolynomialMoment moment n p
      = unequalDampedPolynomialMoment6 moment n p := by
  unfold unequalDampedPolynomialMoment unequalDampedPolynomialMoment6
  rw [Polynomial.sum_def]
  apply Finset.sum_subset
  · intro i hi
    rw [Finset.mem_range]
    exact
      (Polynomial.le_natDegree_of_ne_zero
        (Polynomial.mem_support_iff.mp hi)).trans_lt hp
  · intro i hiRange hiSupport
    have hcoeff : p.coeff i = 0 := by
      simpa only [Polynomial.mem_support_iff, not_ne_iff] using hiSupport
    rw [hcoeff, zero_mul]

/-- Polynomial whose evaluation is `unequalDampedWBar`. -/
def unequalDampedWBarPolynomial (q : ℝ) : Polynomial ℝ :=
  Polynomial.C q
    - Polynomial.C (q + 1) * Polynomial.X
    + Polynomial.X ^ 2

/-- Polynomial whose evaluation is `unequalDampedF0`. -/
def unequalDampedF0Polynomial (q κ : ℝ) : Polynomial ℝ :=
  Polynomial.C (-q)
    + Polynomial.C (1 + κ) * Polynomial.X
    - Polynomial.C κ * Polynomial.X ^ 2

/-- Polynomial whose evaluation is `unequalDampedF1Hat`. -/
def unequalDampedF1HatPolynomial (t q κ : ℝ) : Polynomial ℝ :=
  Polynomial.C (q - t - κ)
    + Polynomial.C (κ - 1) * Polynomial.X

/-- Polynomial whose evaluation is `unequalDampedPsi1`. -/
def unequalDampedPsi1Polynomial (q c k : ℝ) : Polynomial ℝ :=
  Polynomial.C (k * q) - Polynomial.C c * Polynomial.X

/-- Polynomial realization of `G₀`. -/
def unequalDampedG0Polynomial
    (q κ c k : ℝ) : Polynomial ℝ :=
  Polynomial.X
    * unequalDampedWBarPolynomial q
    * unequalDampedF0Polynomial q κ
    * Polynomial.C (c - k)

/-- Polynomial realization of `G₁`. -/
def unequalDampedG1Polynomial
    (t q κ c k : ℝ) : Polynomial ℝ :=
  unequalDampedWBarPolynomial q
    * (unequalDampedF0Polynomial q κ
        * unequalDampedPsi1Polynomial q c k
      + Polynomial.X
        * unequalDampedF1HatPolynomial t q κ
        * Polynomial.C (c - k))

/-- Polynomial realization of `G₂`. -/
def unequalDampedG2Polynomial
    (t q κ c k : ℝ) : Polynomial ℝ :=
  unequalDampedWBarPolynomial q
    * (unequalDampedF1HatPolynomial t q κ
        * unequalDampedPsi1Polynomial q c k
      + Polynomial.X * Polynomial.C t * Polynomial.C (c - k))

/-- Polynomial realization of `G₃`. -/
def unequalDampedG3Polynomial
    (t q c k : ℝ) : Polynomial ℝ :=
  unequalDampedWBarPolynomial q
    * Polynomial.C t
    * unequalDampedPsi1Polynomial q c k

theorem unequalDampedG0Polynomial_natDegree_lt_six
    (q κ c k : ℝ) :
    (unequalDampedG0Polynomial q κ c k).natDegree < 6 := by
  unfold unequalDampedG0Polynomial unequalDampedWBarPolynomial
    unequalDampedF0Polynomial
  compute_degree
  omega

theorem unequalDampedG1Polynomial_natDegree_lt_six
    (t q κ c k : ℝ) :
    (unequalDampedG1Polynomial t q κ c k).natDegree < 6 := by
  unfold unequalDampedG1Polynomial unequalDampedWBarPolynomial
    unequalDampedF0Polynomial unequalDampedF1HatPolynomial
    unequalDampedPsi1Polynomial
  compute_degree
  omega

theorem unequalDampedG2Polynomial_natDegree_lt_six
    (t q κ c k : ℝ) :
    (unequalDampedG2Polynomial t q κ c k).natDegree < 6 := by
  unfold unequalDampedG2Polynomial unequalDampedWBarPolynomial
    unequalDampedF1HatPolynomial unequalDampedPsi1Polynomial
  compute_degree
  omega

theorem unequalDampedG3Polynomial_natDegree_lt_six
    (t q c k : ℝ) :
    (unequalDampedG3Polynomial t q c k).natDegree < 6 := by
  unfold unequalDampedG3Polynomial unequalDampedWBarPolynomial
    unequalDampedPsi1Polynomial
  compute_degree
  omega

theorem eval_unequalDampedG0Polynomial
    (q κ c k y : ℝ) :
    Polynomial.eval y (unequalDampedG0Polynomial q κ c k)
      = unequalDampedG0 q κ c k y := by
  simp only [unequalDampedG0Polynomial, unequalDampedWBarPolynomial,
    unequalDampedF0Polynomial, unequalDampedG0,
    unequalDampedWBar, unequalDampedF0, unequalDampedPsi0,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem eval_unequalDampedG1Polynomial
    (t q κ c k y : ℝ) :
    Polynomial.eval y (unequalDampedG1Polynomial t q κ c k)
      = unequalDampedG1 t q κ c k y := by
  simp only [unequalDampedG1Polynomial, unequalDampedWBarPolynomial,
    unequalDampedF0Polynomial, unequalDampedF1HatPolynomial,
    unequalDampedPsi1Polynomial, unequalDampedG1,
    unequalDampedWBar, unequalDampedF0, unequalDampedF1Hat,
    unequalDampedPsi0, unequalDampedPsi1,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem eval_unequalDampedG2Polynomial
    (t q κ c k y : ℝ) :
    Polynomial.eval y (unequalDampedG2Polynomial t q κ c k)
      = unequalDampedG2 t q κ c k y := by
  simp only [unequalDampedG2Polynomial, unequalDampedWBarPolynomial,
    unequalDampedF1HatPolynomial, unequalDampedPsi1Polynomial,
    unequalDampedG2, unequalDampedWBar, unequalDampedF1Hat,
    unequalDampedPsi0, unequalDampedPsi1,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem eval_unequalDampedG3Polynomial
    (t q c k y : ℝ) :
    Polynomial.eval y (unequalDampedG3Polynomial t q c k)
      = unequalDampedG3 t q c k y := by
  simp only [unequalDampedG3Polynomial, unequalDampedWBarPolynomial,
    unequalDampedPsi1Polynomial, unequalDampedG3,
    unequalDampedWBar, unequalDampedPsi1,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

/--
Integrating a polynomial against `density(y)y^n` is completely determined
by the monomial moments of `density`.
-/
theorem integral_density_pow_mul_polynomial
    {density : ℝ → ℝ} (hdensity : Continuous density)
    {moment : ℕ → ℝ}
    (hmoment : ∀ j : ℕ,
      (∫ y in (0 : ℝ)..1, density y * y ^ j) = moment j)
    (n : ℕ) (p : Polynomial ℝ) :
    (∫ y in (0 : ℝ)..1,
      density y * y ^ n * Polynomial.eval y p)
      =
    unequalDampedPolynomialMoment moment n p := by
  rw [show
    (fun y : ℝ => density y * y ^ n * Polynomial.eval y p)
      =
    (fun y : ℝ =>
      ∑ i ∈ p.support,
        p.coeff i * (density y * y ^ (n + i))) by
      funext y
      rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_add]
      ring]
  rw [intervalIntegral.integral_finsetSum]
  · unfold unequalDampedPolynomialMoment
    rw [Polynomial.sum_def]
    apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_const_mul, hmoment (n + i)]
  · intro i hi
    exact
      ((hdensity.mul (continuous_id.pow (n + i))).intervalIntegrable 0 1)
        |>.const_mul (p.coeff i)

/--
The four generic collected integrals are fixed by the monomial moments.
-/
theorem unequalDampedIntegratedGs_eq_polynomialMoments
    {density : ℝ → ℝ} (hdensity : Continuous density)
    {moment : ℕ → ℝ}
    (hmoment : ∀ j : ℕ,
      (∫ y in (0 : ℝ)..1, density y * y ^ j) = moment j)
    (t q κ c k : ℝ) (n : ℕ) :
    unequalDampedIntegratedG0 density q κ c k n
        =
      unequalDampedPolynomialMoment moment n
        (unequalDampedG0Polynomial q κ c k)
    ∧ unequalDampedIntegratedG1 density t q κ c k n
        =
      unequalDampedPolynomialMoment moment n
        (unequalDampedG1Polynomial t q κ c k)
    ∧ unequalDampedIntegratedG2 density t q κ c k n
        =
      unequalDampedPolynomialMoment moment n
        (unequalDampedG2Polynomial t q κ c k)
    ∧ unequalDampedIntegratedG3 density t q c k n
        =
      unequalDampedPolynomialMoment moment n
        (unequalDampedG3Polynomial t q c k) := by
  constructor
  · unfold unequalDampedIntegratedG0
    calc
      (∫ y in (0 : ℝ)..1,
          density y * y ^ n * unequalDampedG0 q κ c k y)
          =
        ∫ y in (0 : ℝ)..1,
          density y * y ^ n
            * Polynomial.eval y
              (unequalDampedG0Polynomial q κ c k) := by
              apply intervalIntegral.integral_congr
              intro y hy
              dsimp only
              rw [eval_unequalDampedG0Polynomial]
      _ = _ := integral_density_pow_mul_polynomial hdensity hmoment n _
  constructor
  · unfold unequalDampedIntegratedG1
    calc
      (∫ y in (0 : ℝ)..1,
          density y * y ^ n * unequalDampedG1 t q κ c k y)
          =
        ∫ y in (0 : ℝ)..1,
          density y * y ^ n
            * Polynomial.eval y
              (unequalDampedG1Polynomial t q κ c k) := by
              apply intervalIntegral.integral_congr
              intro y hy
              dsimp only
              rw [eval_unequalDampedG1Polynomial]
      _ = _ := integral_density_pow_mul_polynomial hdensity hmoment n _
  constructor
  · unfold unequalDampedIntegratedG2
    calc
      (∫ y in (0 : ℝ)..1,
          density y * y ^ n * unequalDampedG2 t q κ c k y)
          =
        ∫ y in (0 : ℝ)..1,
          density y * y ^ n
            * Polynomial.eval y
              (unequalDampedG2Polynomial t q κ c k) := by
              apply intervalIntegral.integral_congr
              intro y hy
              dsimp only
              rw [eval_unequalDampedG2Polynomial]
      _ = _ := integral_density_pow_mul_polynomial hdensity hmoment n _
  · unfold unequalDampedIntegratedG3
    calc
      (∫ y in (0 : ℝ)..1,
          density y * y ^ n * unequalDampedG3 t q c k y)
          =
        ∫ y in (0 : ℝ)..1,
          density y * y ^ n
            * Polynomial.eval y
              (unequalDampedG3Polynomial t q c k) := by
              apply intervalIntegral.integral_congr
              intro y hy
              dsimp only
              rw [eval_unequalDampedG3Polynomial]
      _ = _ := integral_density_pow_mul_polynomial hdensity hmoment n _

private theorem continuous_unequalDampedIntegratedG0_integrand
    {density : ℝ → ℝ} (hdensity : Continuous density)
    (q κ c k : ℝ) (n : ℕ) :
    Continuous
      (fun y : ℝ =>
        density y * y ^ n * unequalDampedG0 q κ c k y) := by
  unfold unequalDampedG0 unequalDampedWBar unequalDampedF0
    unequalDampedPsi0
  fun_prop

private theorem continuous_unequalDampedIntegratedG1_integrand
    {density : ℝ → ℝ} (hdensity : Continuous density)
    (t q κ c k : ℝ) (n : ℕ) :
    Continuous
      (fun y : ℝ =>
        density y * y ^ n * unequalDampedG1 t q κ c k y) := by
  unfold unequalDampedG1 unequalDampedWBar unequalDampedF0
    unequalDampedF1Hat unequalDampedPsi0 unequalDampedPsi1
  fun_prop

private theorem continuous_unequalDampedIntegratedG2_integrand
    {density : ℝ → ℝ} (hdensity : Continuous density)
    (t q κ c k : ℝ) (n : ℕ) :
    Continuous
      (fun y : ℝ =>
        density y * y ^ n * unequalDampedG2 t q κ c k y) := by
  unfold unequalDampedG2 unequalDampedWBar unequalDampedF1Hat
    unequalDampedPsi0 unequalDampedPsi1
  fun_prop

private theorem continuous_unequalDampedIntegratedG3_integrand
    {density : ℝ → ℝ} (hdensity : Continuous density)
    (t q c k : ℝ) (n : ℕ) :
    Continuous
      (fun y : ℝ =>
        density y * y ^ n * unequalDampedG3 t q c k y) := by
  unfold unequalDampedG3 unequalDampedWBar unequalDampedPsi1
  fun_prop

/--
The integral of the generic target-indexed pointwise summand is `s^n`
times its collected coefficient.
-/
theorem integral_unequalDampedPointwiseSeriesTerm_eq_integratedCoefficient
    {density : ℝ → ℝ} (hdensity : Continuous density)
    (t q κ c k s : ℝ) (n : ℕ) :
    (∫ y in (0 : ℝ)..1,
      unequalDampedPointwiseSeriesTerm
        density t q κ c k s y n)
      =
    s ^ n * unequalDampedIntegratedCoefficient
      density t q κ c k n := by
  let f0 : ℝ → ℝ := fun y =>
    density y * y ^ n * unequalDampedG0 q κ c k y
  let f1 : ℝ → ℝ := fun y =>
    density y * y ^ n * unequalDampedG1 t q κ c k y
  let f2 : ℝ → ℝ := fun y =>
    density y * y ^ n * unequalDampedG2 t q κ c k y
  let f3 : ℝ → ℝ := fun y =>
    density y * y ^ n * unequalDampedG3 t q c k y
  have hf0 : Continuous f0 :=
    continuous_unequalDampedIntegratedG0_integrand
      hdensity q κ c k n
  have hf1 : Continuous f1 :=
    continuous_unequalDampedIntegratedG1_integrand
      hdensity t q κ c k n
  have hf2 : Continuous f2 :=
    continuous_unequalDampedIntegratedG2_integrand
      hdensity t q κ c k n
  have hf3 : Continuous f3 :=
    continuous_unequalDampedIntegratedG3_integrand
      hdensity t q c k n
  have hpointwise :
      ∀ y : ℝ,
        unequalDampedPointwiseSeriesTerm
            density t q κ c k s y n
          =
        s ^ n *
          ((Nat.choose (n + 5) 5 : ℝ) * f0 y
            + (Nat.choose (n + 4) 5 : ℝ) * f1 y
            + (Nat.choose (n + 3) 5 : ℝ) * f2 y
            + (Nat.choose (n + 2) 5 : ℝ) * f3 y) := by
    intro y
    unfold unequalDampedPointwiseSeriesTerm unequalBinomialC0
      unequalBinomialC1 unequalBinomialC2 unequalBinomialC3
    dsimp only [f0, f1, f2, f3]
    rw [mul_pow]
    ring
  rw [intervalIntegral.integral_congr
    (fun y hy => hpointwise y)]
  rw [intervalIntegral.integral_const_mul]
  have h0 :
      IntervalIntegrable
        (fun y => (Nat.choose (n + 5) 5 : ℝ) * f0 y)
        volume 0 1 :=
    (hf0.intervalIntegrable 0 1).const_mul _
  have h1 :
      IntervalIntegrable
        (fun y => (Nat.choose (n + 4) 5 : ℝ) * f1 y)
        volume 0 1 :=
    (hf1.intervalIntegrable 0 1).const_mul _
  have h2 :
      IntervalIntegrable
        (fun y => (Nat.choose (n + 3) 5 : ℝ) * f2 y)
        volume 0 1 :=
    (hf2.intervalIntegrable 0 1).const_mul _
  have h3 :
      IntervalIntegrable
        (fun y => (Nat.choose (n + 2) 5 : ℝ) * f3 y)
        volume 0 1 :=
    (hf3.intervalIntegrable 0 1).const_mul _
  rw [intervalIntegral.integral_add ((h0.add h1).add h2) h3,
    intervalIntegral.integral_add (h0.add h1) h2,
    intervalIntegral.integral_add h0 h1]
  simp only [intervalIntegral.integral_const_mul]
  unfold unequalDampedIntegratedCoefficient unequalDampedIntegratedG0
    unequalDampedIntegratedG1 unequalDampedIntegratedG2
    unequalDampedIntegratedG3
  dsimp only [f0, f1, f2, f3]

/-! ## Family analytic integrals -/

/--
Purely algebraic right-chart coefficient obtained by applying the certified
beta moment sequence to the four collected polynomials.
-/
def unequalFixedDifferenceFourPlusPolynomialCoefficient
    (m n : ℕ) : ℝ :=
  (Nat.choose (n + 5) 5 : ℝ)
      * unequalDampedPolynomialMoment
        (unequalFixedDifferenceFourPlusMoment m) n
        (unequalDampedG0Polynomial
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourKappa m)
          (unequalFixedDifferenceFourC m)
          (unequalFixedDifferenceFourK m))
    + (Nat.choose (n + 4) 5 : ℝ)
      * unequalDampedPolynomialMoment
        (unequalFixedDifferenceFourPlusMoment m) n
        (unequalDampedG1Polynomial
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourKappa m)
          (unequalFixedDifferenceFourC m)
          (unequalFixedDifferenceFourK m))
    + (Nat.choose (n + 3) 5 : ℝ)
      * unequalDampedPolynomialMoment
        (unequalFixedDifferenceFourPlusMoment m) n
        (unequalDampedG2Polynomial
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourKappa m)
          (unequalFixedDifferenceFourC m)
          (unequalFixedDifferenceFourK m))
    + (Nat.choose (n + 2) 5 : ℝ)
      * unequalDampedPolynomialMoment
        (unequalFixedDifferenceFourPlusMoment m) n
        (unequalDampedG3Polynomial
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourC m)
          (unequalFixedDifferenceFourK m))

/-- Swapped-chart analogue of
`unequalFixedDifferenceFourPlusPolynomialCoefficient`. -/
def unequalFixedDifferenceFourMinusPolynomialCoefficient
    (m n : ℕ) : ℝ :=
  (Nat.choose (n + 5) 5 : ℝ)
      * unequalDampedPolynomialMoment
        (unequalFixedDifferenceFourMinusMoment m) n
        (unequalDampedG0Polynomial
          (unequalFixedDifferenceFourT m)
          (-unequalFixedDifferenceFourKappa m)
          (unequalFixedDifferenceFourC m)
          (unequalFixedDifferenceFourK m))
    + (Nat.choose (n + 4) 5 : ℝ)
      * unequalDampedPolynomialMoment
        (unequalFixedDifferenceFourMinusMoment m) n
        (unequalDampedG1Polynomial
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourT m)
          (-unequalFixedDifferenceFourKappa m)
          (unequalFixedDifferenceFourC m)
          (unequalFixedDifferenceFourK m))
    + (Nat.choose (n + 3) 5 : ℝ)
      * unequalDampedPolynomialMoment
        (unequalFixedDifferenceFourMinusMoment m) n
        (unequalDampedG2Polynomial
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourT m)
          (-unequalFixedDifferenceFourKappa m)
          (unequalFixedDifferenceFourC m)
          (unequalFixedDifferenceFourK m))
    + (Nat.choose (n + 2) 5 : ℝ)
      * unequalDampedPolynomialMoment
        (unequalFixedDifferenceFourMinusMoment m) n
        (unequalDampedG3Polynomial
          (unequalFixedDifferenceFourQ m)
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourC m)
          (unequalFixedDifferenceFourK m))

/--
The actual integrated right-chart coefficient equals its purely algebraic
polynomial-moment expression.
-/
theorem unequalFixedDifferenceFourPlusIntegratedCoefficient_eq_polynomial
    {m : ℕ} (hm : 7 ≤ m) (n : ℕ) :
    unequalDampedIntegratedCoefficient
      (unequalFixedDifferenceFourPlusDensity m)
      (unequalFixedDifferenceFourT m)
      (unequalFixedDifferenceFourQ m)
      (unequalFixedDifferenceFourKappa m)
      (unequalFixedDifferenceFourC m)
      (unequalFixedDifferenceFourK m) n
      =
    unequalFixedDifferenceFourPlusPolynomialCoefficient m n := by
  obtain ⟨h0, h1, h2, h3⟩ :=
    unequalDampedIntegratedGs_eq_polynomialMoments
      (continuous_unequalFixedDifferenceFourPlusDensity m)
      (integral_unequalFixedDifferenceFourPlusDensity_pow hm)
      (unequalFixedDifferenceFourT m)
      (unequalFixedDifferenceFourQ m)
      (unequalFixedDifferenceFourKappa m)
      (unequalFixedDifferenceFourC m)
      (unequalFixedDifferenceFourK m) n
  unfold unequalDampedIntegratedCoefficient
    unequalFixedDifferenceFourPlusPolynomialCoefficient
  rw [h0, h1, h2, h3]

/--
The actual integrated swapped-chart coefficient equals its purely
algebraic polynomial-moment expression.
-/
theorem unequalFixedDifferenceFourMinusIntegratedCoefficient_eq_polynomial
    {m : ℕ} (hm : 7 ≤ m) (n : ℕ) :
    unequalDampedIntegratedCoefficient
      (unequalFixedDifferenceFourMinusDensity m)
      (unequalFixedDifferenceFourQ m)
      (unequalFixedDifferenceFourT m)
      (-unequalFixedDifferenceFourKappa m)
      (unequalFixedDifferenceFourC m)
      (unequalFixedDifferenceFourK m) n
      =
    unequalFixedDifferenceFourMinusPolynomialCoefficient m n := by
  obtain ⟨h0, h1, h2, h3⟩ :=
    unequalDampedIntegratedGs_eq_polynomialMoments
      (continuous_unequalFixedDifferenceFourMinusDensity m)
      (integral_unequalFixedDifferenceFourMinusDensity_pow hm)
      (unequalFixedDifferenceFourQ m)
      (unequalFixedDifferenceFourT m)
      (-unequalFixedDifferenceFourKappa m)
      (unequalFixedDifferenceFourC m)
      (unequalFixedDifferenceFourK m) n
  unfold unequalDampedIntegratedCoefficient
    unequalFixedDifferenceFourMinusPolynomialCoefficient
  rw [h0, h1, h2, h3]

/-- Right-chart analytic integral, for an explicitly supplied density. -/
def unequalFixedDifferenceFourPlusH
    (density : ℝ → ℝ) (m : ℕ) (s : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1,
    unequalDampedHIntegrand density
      (unequalFixedDifferenceFourT m)
      (unequalFixedDifferenceFourQ m)
      (unequalFixedDifferenceFourKappa m)
      (unequalFixedDifferenceFourC m)
      (unequalFixedDifferenceFourK m) s y

/-- Left-chart analytic integral, for an explicitly supplied density. -/
def unequalFixedDifferenceFourMinusH
    (density : ℝ → ℝ) (m : ℕ) (s : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1,
    unequalDampedHIntegrand density
      (unequalFixedDifferenceFourQ m)
      (unequalFixedDifferenceFourT m)
      (-unequalFixedDifferenceFourKappa m)
      (unequalFixedDifferenceFourC m)
      (unequalFixedDifferenceFourK m) s y

/--
Once the exact integrated-coefficient identity is supplied, the certified
right-chart coefficient series sums to the analytic integral.
-/
theorem hasSum_unequalFixedDifferenceFourPlusSeries_of_coefficient_identity
    {density : ℝ → ℝ} (hdensity : Continuous density)
    {m : ℕ}
    (hcoeff : ∀ n : ℕ,
      unequalDampedIntegratedCoefficient density
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourQ m)
        (unequalFixedDifferenceFourKappa m)
        (unequalFixedDifferenceFourC m)
        (unequalFixedDifferenceFourK m) n
        =
      unequalFixedDifferenceFourPlusCoeff m n)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasSum
      (unequalFixedDifferenceFourPlusSeriesTerm m s)
      (unequalFixedDifferenceFourPlusH density m s) := by
  have h := hasSum_integral_unequalDampedPointwiseSeries
    hdensity
    (unequalFixedDifferenceFourT m)
    (unequalFixedDifferenceFourQ m)
    (unequalFixedDifferenceFourKappa m)
    (unequalFixedDifferenceFourC m)
    (unequalFixedDifferenceFourK m)
    hs0 hs1
  unfold unequalFixedDifferenceFourPlusH
  convert h using 1
  funext n
  rw [integral_unequalDampedPointwiseSeriesTerm_eq_integratedCoefficient
    hdensity]
  rw [hcoeff n]
  unfold unequalFixedDifferenceFourPlusSeriesTerm
  ring

/--
Once the exact integrated-coefficient identity is supplied, the certified
left-chart coefficient series sums to the analytic integral.
-/
theorem hasSum_unequalFixedDifferenceFourMinusSeries_of_coefficient_identity
    {density : ℝ → ℝ} (hdensity : Continuous density)
    {m : ℕ}
    (hcoeff : ∀ n : ℕ,
      unequalDampedIntegratedCoefficient density
        (unequalFixedDifferenceFourQ m)
        (unequalFixedDifferenceFourT m)
        (-unequalFixedDifferenceFourKappa m)
        (unequalFixedDifferenceFourC m)
        (unequalFixedDifferenceFourK m) n
        =
      unequalFixedDifferenceFourMinusCoeff m n)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasSum
      (unequalFixedDifferenceFourMinusSeriesTerm m s)
      (unequalFixedDifferenceFourMinusH density m s) := by
  have h := hasSum_integral_unequalDampedPointwiseSeries
    hdensity
    (unequalFixedDifferenceFourQ m)
    (unequalFixedDifferenceFourT m)
    (-unequalFixedDifferenceFourKappa m)
    (unequalFixedDifferenceFourC m)
    (unequalFixedDifferenceFourK m)
    hs0 hs1
  unfold unequalFixedDifferenceFourMinusH
  convert h using 1
  funext n
  rw [integral_unequalDampedPointwiseSeriesTerm_eq_integratedCoefficient
    hdensity]
  rw [hcoeff n]
  unfold unequalFixedDifferenceFourMinusSeriesTerm
  ring

/-!
The following two variants split the coefficient-identification hypothesis
into the four moment evaluations and one purely algebraic collection
identity.  This is the interface intended for the beta-moment layer.
-/

/--
Right-chart series identification from four exact collected moments.
-/
theorem hasSum_unequalFixedDifferenceFourPlusSeries_of_moment_identities
    {density : ℝ → ℝ} (hdensity : Continuous density)
    {m : ℕ} (M0 M1 M2 M3 : ℕ → ℝ)
    (hM0 : ∀ n : ℕ,
      unequalDampedIntegratedG0 density
        (unequalFixedDifferenceFourQ m)
        (unequalFixedDifferenceFourKappa m)
        (unequalFixedDifferenceFourC m)
        (unequalFixedDifferenceFourK m) n = M0 n)
    (hM1 : ∀ n : ℕ,
      unequalDampedIntegratedG1 density
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourQ m)
        (unequalFixedDifferenceFourKappa m)
        (unequalFixedDifferenceFourC m)
        (unequalFixedDifferenceFourK m) n = M1 n)
    (hM2 : ∀ n : ℕ,
      unequalDampedIntegratedG2 density
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourQ m)
        (unequalFixedDifferenceFourKappa m)
        (unequalFixedDifferenceFourC m)
        (unequalFixedDifferenceFourK m) n = M2 n)
    (hM3 : ∀ n : ℕ,
      unequalDampedIntegratedG3 density
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourQ m)
        (unequalFixedDifferenceFourC m)
        (unequalFixedDifferenceFourK m) n = M3 n)
    (hcollect : ∀ n : ℕ,
      (Nat.choose (n + 5) 5 : ℝ) * M0 n
        + (Nat.choose (n + 4) 5 : ℝ) * M1 n
        + (Nat.choose (n + 3) 5 : ℝ) * M2 n
        + (Nat.choose (n + 2) 5 : ℝ) * M3 n
        =
      unequalFixedDifferenceFourPlusCoeff m n)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasSum
      (unequalFixedDifferenceFourPlusSeriesTerm m s)
      (unequalFixedDifferenceFourPlusH density m s) := by
  apply
    hasSum_unequalFixedDifferenceFourPlusSeries_of_coefficient_identity
      hdensity (m := m) ?_ hs0 hs1
  intro n
  unfold unequalDampedIntegratedCoefficient
  rw [hM0 n, hM1 n, hM2 n, hM3 n]
  exact hcollect n

/--
Left-chart series identification from four exact collected moments.
-/
theorem hasSum_unequalFixedDifferenceFourMinusSeries_of_moment_identities
    {density : ℝ → ℝ} (hdensity : Continuous density)
    {m : ℕ} (M0 M1 M2 M3 : ℕ → ℝ)
    (hM0 : ∀ n : ℕ,
      unequalDampedIntegratedG0 density
        (unequalFixedDifferenceFourT m)
        (-unequalFixedDifferenceFourKappa m)
        (unequalFixedDifferenceFourC m)
        (unequalFixedDifferenceFourK m) n = M0 n)
    (hM1 : ∀ n : ℕ,
      unequalDampedIntegratedG1 density
        (unequalFixedDifferenceFourQ m)
        (unequalFixedDifferenceFourT m)
        (-unequalFixedDifferenceFourKappa m)
        (unequalFixedDifferenceFourC m)
        (unequalFixedDifferenceFourK m) n = M1 n)
    (hM2 : ∀ n : ℕ,
      unequalDampedIntegratedG2 density
        (unequalFixedDifferenceFourQ m)
        (unequalFixedDifferenceFourT m)
        (-unequalFixedDifferenceFourKappa m)
        (unequalFixedDifferenceFourC m)
        (unequalFixedDifferenceFourK m) n = M2 n)
    (hM3 : ∀ n : ℕ,
      unequalDampedIntegratedG3 density
        (unequalFixedDifferenceFourQ m)
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourC m)
        (unequalFixedDifferenceFourK m) n = M3 n)
    (hcollect : ∀ n : ℕ,
      (Nat.choose (n + 5) 5 : ℝ) * M0 n
        + (Nat.choose (n + 4) 5 : ℝ) * M1 n
        + (Nat.choose (n + 3) 5 : ℝ) * M2 n
        + (Nat.choose (n + 2) 5 : ℝ) * M3 n
        =
      unequalFixedDifferenceFourMinusCoeff m n)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasSum
      (unequalFixedDifferenceFourMinusSeriesTerm m s)
      (unequalFixedDifferenceFourMinusH density m s) := by
  apply
    hasSum_unequalFixedDifferenceFourMinusSeries_of_coefficient_identity
      hdensity (m := m) ?_ hs0 hs1
  intro n
  unfold unequalDampedIntegratedCoefficient
  rw [hM0 n, hM1 n, hM2 n, hM3 n]
  exact hcollect n

/--
The right-chart integral is uniformly bounded by the negative pivot margin
once its exact coefficient identity is known.
-/
theorem unequalFixedDifferenceFourPlusH_le_neg_b0_of_coefficient_identity
    {density : ℝ → ℝ} (hdensity : Continuous density)
    {m : ℕ} (hm : 7 ≤ m)
    (hcoeff : ∀ n : ℕ,
      unequalDampedIntegratedCoefficient density
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourQ m)
        (unequalFixedDifferenceFourKappa m)
        (unequalFixedDifferenceFourC m)
        (unequalFixedDifferenceFourK m) n
        =
      unequalFixedDifferenceFourPlusCoeff m n)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourPlusH density m s
      ≤ -unequalFixedDifferenceFourB0 m := by
  have hsum :=
    hasSum_unequalFixedDifferenceFourPlusSeries_of_coefficient_identity
      hdensity hcoeff hs0 hs1
  rw [← hsum.tsum_eq]
  exact unequalFixedDifferenceFourPlusSeries_le_neg_b0
    hm hs0 hsum.summable

/--
The left-chart integral has the same uniform negative bound once its exact
coefficient identity is known.
-/
theorem unequalFixedDifferenceFourMinusH_le_neg_b0_of_coefficient_identity
    {density : ℝ → ℝ} (hdensity : Continuous density)
    {m : ℕ} (hm : 7 ≤ m)
    (hcoeff : ∀ n : ℕ,
      unequalDampedIntegratedCoefficient density
        (unequalFixedDifferenceFourQ m)
        (unequalFixedDifferenceFourT m)
        (-unequalFixedDifferenceFourKappa m)
        (unequalFixedDifferenceFourC m)
        (unequalFixedDifferenceFourK m) n
        =
      unequalFixedDifferenceFourMinusCoeff m n)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    unequalFixedDifferenceFourMinusH density m s
      ≤ -unequalFixedDifferenceFourB0 m := by
  have hsum :=
    hasSum_unequalFixedDifferenceFourMinusSeries_of_coefficient_identity
      hdensity hcoeff hs0 hs1
  rw [← hsum.tsum_eq]
  exact unequalFixedDifferenceFourMinusSeries_le_neg_b0
    hm hs0 hsum.summable

end

end GraybillDeal
