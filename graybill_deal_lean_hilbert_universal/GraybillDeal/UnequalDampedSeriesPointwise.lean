import GraybillDeal.UnequalDampedBinomial
import GraybillDeal.UnequalDampedCoordinates

/-!
# Pointwise series for the damped unequal-size certificate

The numerator of each one-sided beta integral is cubic in the series
coordinate `s`.  More precisely, after writing `t = s*y`, it has the form

`G₀(y) + t G₁(y) + t² G₂(y) + t³ G₃(y)`.

This factorization is useful because the four shifted order-five binomial
series from `UnequalDampedBinomial` then have the same target index.  The
result below is the pointwise analytic expansion; termwise integration and
the exact coefficient collection are handled in later files.
-/

namespace GraybillDeal

noncomputable section

/-- Constant-in-`s` part of the inner numerator `F`. -/
def unequalDampedF0 (q κ y : ℝ) : ℝ :=
  -q + (1 + κ) * y - κ * y ^ 2

/--
After removing one factor of `y`, the coefficient of `s` in `F`.
-/
def unequalDampedF1Hat (t q κ y : ℝ) : ℝ :=
  q - t - κ + (κ - 1) * y

/-- Constant-in-`s` part of the affine numerator `Ψ`. -/
def unequalDampedPsi0 (c k : ℝ) : ℝ :=
  c - k

/-- Coefficient of `s` in the affine numerator `Ψ`. -/
def unequalDampedPsi1 (q c k y : ℝ) : ℝ :=
  k * q - c * y

/-- The factor left after removing the common `y` from
`(q-y)y(1-y)`. -/
def unequalDampedWBar (q y : ℝ) : ℝ :=
  (q - y) * (1 - y)

/-- Zeroth collected numerator. -/
def unequalDampedG0 (q κ c k y : ℝ) : ℝ :=
  y * unequalDampedWBar q y
    * unequalDampedF0 q κ y
    * unequalDampedPsi0 c k

/-- First collected numerator, after removing one factor of `y`. -/
def unequalDampedG1 (t q κ c k y : ℝ) : ℝ :=
  unequalDampedWBar q y
    * (unequalDampedF0 q κ y * unequalDampedPsi1 q c k y
      + y * unequalDampedF1Hat t q κ y
        * unequalDampedPsi0 c k)

/-- Second collected numerator, after removing two factors of `y`. -/
def unequalDampedG2 (t q κ c k y : ℝ) : ℝ :=
  unequalDampedWBar q y
    * (unequalDampedF1Hat t q κ y
        * unequalDampedPsi1 q c k y
      + y * t * unequalDampedPsi0 c k)

/-- Third collected numerator, after removing three factors of `y`. -/
def unequalDampedG3 (t q c k y : ℝ) : ℝ :=
  unequalDampedWBar q y * t * unequalDampedPsi1 q c k y

/--
The exact cubic numerator decomposition in powers of `s*y`.
-/
theorem unequalDampedNumerator_decomposition
    (t q κ c k s y : ℝ) :
    (q - y) * y * (1 - y)
        * unequalDampedF t q κ s y
        * unequalDampedPsiNumerator q c k s y
      =
    unequalDampedG0 q κ c k y
      + (s * y) * unequalDampedG1 t q κ c k y
      + (s * y) ^ 2 * unequalDampedG2 t q κ c k y
      + (s * y) ^ 3 * unequalDampedG3 t q c k y := by
  simp only [unequalDampedF, unequalDampedPsiNumerator,
    unequalDampedDenom, unequalDampedF0, unequalDampedF1Hat,
    unequalDampedPsi0, unequalDampedPsi1, unequalDampedWBar,
    unequalDampedG0, unequalDampedG1, unequalDampedG2,
    unequalDampedG3]
  ring

/-- Polynomial density of `Beta(8,6)` on `[0,1]`. -/
def unequalDampedPlusDensity (y : ℝ) : ℝ :=
  10296 * y ^ 7 * (1 - y) ^ 5

/-- Polynomial density of `Beta(6,8)` on `[0,1]`. -/
def unequalDampedMinusDensity (y : ℝ) : ℝ :=
  10296 * y ^ 5 * (1 - y) ^ 7

/-- Generic one-sided beta-integrand before integration in `y`. -/
def unequalDampedHIntegrand
    (density : ℝ → ℝ) (t q κ c k s y : ℝ) : ℝ :=
  density y
    * ((q - y) * y * (1 - y)
      * unequalDampedF t q κ s y
      * unequalDampedPsiNumerator q c k s y)
    / unequalDampedDenom s y ^ 6

/--
The collected target-indexed pointwise summand.
-/
def unequalDampedPointwiseSeriesTerm
    (density : ℝ → ℝ) (t q κ c k s y : ℝ) (n : ℕ) : ℝ :=
  density y
    * (unequalDampedG0 q κ c k y
        * unequalBinomialC0 (s * y) n
      + unequalDampedG1 t q κ c k y
        * unequalBinomialC1 (s * y) n
      + unequalDampedG2 t q κ c k y
        * unequalBinomialC2 (s * y) n
      + unequalDampedG3 t q c k y
        * unequalBinomialC3 (s * y) n)

/--
For `0 ≤ s < 1` and `0 ≤ y ≤ 1`, the collected summands sum pointwise to
the one-sided beta-integrand.
-/
theorem hasSum_unequalDampedPointwiseSeries
    (density : ℝ → ℝ) (t q κ c k : ℝ)
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    HasSum
      (unequalDampedPointwiseSeriesTerm
        density t q κ c k s y)
      (unequalDampedHIntegrand density t q κ c k s y) := by
  have ht : ‖s * y‖ < 1 :=
    norm_mul_lt_one_of_mem_unit hs0 hs1 hy0 hy1
  have h0 :=
    (hasSum_choose_five_mul_geometric ht).mul_left
      (density y * unequalDampedG0 q κ c k y)
  have h1 :=
    (hasSum_unequalBinomialC1 ht).mul_left
      (density y * unequalDampedG1 t q κ c k y)
  have h2 :=
    (hasSum_unequalBinomialC2 ht).mul_left
      (density y * unequalDampedG2 t q κ c k y)
  have h3 :=
    (hasSum_unequalBinomialC3 ht).mul_left
      (density y * unequalDampedG3 t q c k y)
  have h := ((h0.add h1).add h2).add h3
  have h' :
      HasSum
        (unequalDampedPointwiseSeriesTerm
          density t q κ c k s y)
        (density y * unequalDampedG0 q κ c k y
            * unequalBinomialD6 (s * y)
          + density y * unequalDampedG1 t q κ c k y
            * ((s * y) * unequalBinomialD6 (s * y))
          + density y * unequalDampedG2 t q κ c k y
            * ((s * y) ^ 2 * unequalBinomialD6 (s * y))
          + density y * unequalDampedG3 t q c k y
            * ((s * y) ^ 3 * unequalBinomialD6 (s * y))) :=
    HasSum.congr_fun h (by
      intro n
      unfold unequalDampedPointwiseSeriesTerm
      ring)
  have htarget :
      unequalDampedHIntegrand density t q κ c k s y
        =
      density y * unequalDampedG0 q κ c k y
          * unequalBinomialD6 (s * y)
        + density y * unequalDampedG1 t q κ c k y
          * ((s * y) * unequalBinomialD6 (s * y))
        + density y * unequalDampedG2 t q κ c k y
          * ((s * y) ^ 2 * unequalBinomialD6 (s * y))
        + density y * unequalDampedG3 t q c k y
          * ((s * y) ^ 3 * unequalBinomialD6 (s * y)) := by
    unfold unequalDampedHIntegrand
    rw [unequalDampedNumerator_decomposition]
    unfold unequalBinomialD6 unequalDampedDenom
    ring
  rw [htarget]
  exact h'

/-- The plus-side specialization of the pointwise expansion. -/
theorem hasSum_unequalDampedPlusPointwiseSeries
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    HasSum
      (unequalDampedPointwiseSeriesTerm
        unequalDampedPlusDensity
        (3 / 7) (4 / 7) unequalDampedKappa13_17
        unequalDampedC13_17 unequalDampedK13_17 s y)
      (unequalDampedHIntegrand
        unequalDampedPlusDensity
        (3 / 7) (4 / 7) unequalDampedKappa13_17
        unequalDampedC13_17 unequalDampedK13_17 s y) :=
  hasSum_unequalDampedPointwiseSeries
    unequalDampedPlusDensity
    (3 / 7) (4 / 7) unequalDampedKappa13_17
    unequalDampedC13_17 unequalDampedK13_17
    hs0 hs1 hy0 hy1

/-- The swapped-side specialization of the pointwise expansion. -/
theorem hasSum_unequalDampedMinusPointwiseSeries
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    HasSum
      (unequalDampedPointwiseSeriesTerm
        unequalDampedMinusDensity
        (4 / 7) (3 / 7) (-unequalDampedKappa13_17)
        unequalDampedC13_17 unequalDampedK13_17 s y)
      (unequalDampedHIntegrand
        unequalDampedMinusDensity
        (4 / 7) (3 / 7) (-unequalDampedKappa13_17)
        unequalDampedC13_17 unequalDampedK13_17 s y) :=
  hasSum_unequalDampedPointwiseSeries
    unequalDampedMinusDensity
    (4 / 7) (3 / 7) (-unequalDampedKappa13_17)
    unequalDampedC13_17 unequalDampedK13_17
    hs0 hs1 hy0 hy1

end

end GraybillDeal
