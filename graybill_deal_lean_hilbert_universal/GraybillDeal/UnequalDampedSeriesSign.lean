import GraybillDeal.UnequalDampedAlgebra
import GraybillDeal.UnequalDampedCoefficients
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Sign of the two damped unequal-size power series

This file packages the exact coefficient certificate for the fixed
`(ν₁,ν₂) = (12,16)` construction.

On the side `θ ≥ 3/7`, the beta variable has shapes `(8,6)`; after swapping
the samples on the other side it has shapes `(6,8)`.  The first three
coefficients are explicit negative rationals.  Every later coefficient is a
strictly positive beta moment times the strictly negative rational tail
factor proved in `UnequalDampedCoefficients`.

The final two theorems are deliberately phrased with a summability
hypothesis.  The analytic integration layer supplies this hypothesis when it
identifies the series with the corresponding beta integral.
-/

namespace GraybillDeal

noncomputable section

/-- The raw `n`th moment of a `Beta(8,6)` variable. -/
def unequalDampedPlusMoment (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (8 + (i : ℝ)) / (14 + (i : ℝ))

/-- The raw `n`th moment of a `Beta(6,8)` variable. -/
def unequalDampedMinusMoment (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (6 + (i : ℝ)) / (14 + (i : ℝ))

theorem unequalDampedPlusMoment_pos (n : ℕ) :
    0 < unequalDampedPlusMoment n := by
  unfold unequalDampedPlusMoment
  exact Finset.prod_pos fun i hi => by positivity

theorem unequalDampedMinusMoment_pos (n : ℕ) :
    0 < unequalDampedMinusMoment n := by
  unfold unequalDampedMinusMoment
  exact Finset.prod_pos fun i hi => by positivity

/-- Integrated coefficient sequence on the side `θ ≥ 3/7`. -/
def unequalDampedPlusCoeff : ℕ → ℝ
  | 0 => -2927 / 12944820
  | 1 => -21079 / 45306870
  | 2 => -6257096 / 5595398445
  | n + 3 =>
      unequalDampedPlusMoment (n + 3)
        * unequalDampedPlusTailFactor (n + 3)

/-- Integrated coefficient sequence on the swapped side `θ ≤ 3/7`. -/
def unequalDampedMinusCoeff : ℕ → ℝ
  | 0 => -2927 / 12944820
  | 1 => -19309 / 90613740
  | 2 => -2290163 / 3730265630
  | n + 3 =>
      unequalDampedMinusMoment (n + 3)
        * unequalDampedMinusTailFactor (n + 3)

@[simp]
theorem unequalDampedPlusCoeff_zero :
    unequalDampedPlusCoeff 0 = -unequalDampedB0 := by
  norm_num [unequalDampedPlusCoeff, unequalDampedB0]

@[simp]
theorem unequalDampedMinusCoeff_zero :
    unequalDampedMinusCoeff 0 = -unequalDampedB0 := by
  norm_num [unequalDampedMinusCoeff, unequalDampedB0]

theorem unequalDampedPlusCoeff_neg : ∀ n : ℕ,
    unequalDampedPlusCoeff n < 0
  | 0 => by norm_num [unequalDampedPlusCoeff]
  | 1 => by norm_num [unequalDampedPlusCoeff]
  | 2 => by norm_num [unequalDampedPlusCoeff]
  | n + 3 => by
      simp only [unequalDampedPlusCoeff]
      exact mul_neg_of_pos_of_neg
        (unequalDampedPlusMoment_pos (n + 3))
        (unequalDampedPlusTailFactor_neg (n + 3) (by omega))

theorem unequalDampedMinusCoeff_neg : ∀ n : ℕ,
    unequalDampedMinusCoeff n < 0
  | 0 => by norm_num [unequalDampedMinusCoeff]
  | 1 => by norm_num [unequalDampedMinusCoeff]
  | 2 => by norm_num [unequalDampedMinusCoeff]
  | n + 3 => by
      simp only [unequalDampedMinusCoeff]
      exact mul_neg_of_pos_of_neg
        (unequalDampedMinusMoment_pos (n + 3))
        (unequalDampedMinusTailFactor_neg (n + 3) (by omega))

/-- The plus-side power-series summand. -/
def unequalDampedPlusSeriesTerm (s : ℝ) (n : ℕ) : ℝ :=
  unequalDampedPlusCoeff n * s ^ n

/-- The swapped-side power-series summand. -/
def unequalDampedMinusSeriesTerm (s : ℝ) (n : ℕ) : ℝ :=
  unequalDampedMinusCoeff n * s ^ n

/-- The plus-side power series `H₊`. -/
def unequalDampedPlusSeries (s : ℝ) : ℝ :=
  ∑' n : ℕ, unequalDampedPlusSeriesTerm s n

/-- The swapped-side power series `H₋`. -/
def unequalDampedMinusSeries (s : ℝ) : ℝ :=
  ∑' n : ℕ, unequalDampedMinusSeriesTerm s n

theorem unequalDampedPlusSeriesTerm_nonpos
    {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    unequalDampedPlusSeriesTerm s n ≤ 0 := by
  unfold unequalDampedPlusSeriesTerm
  exact mul_nonpos_of_nonpos_of_nonneg
    (unequalDampedPlusCoeff_neg n).le
    (pow_nonneg hs n)

theorem unequalDampedMinusSeriesTerm_nonpos
    {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    unequalDampedMinusSeriesTerm s n ≤ 0 := by
  unfold unequalDampedMinusSeriesTerm
  exact mul_nonpos_of_nonpos_of_nonneg
    (unequalDampedMinusCoeff_neg n).le
    (pow_nonneg hs n)

/--
A summable nonpositive real series is bounded above by its zeroth term.
-/
theorem tsum_le_zero_term_of_nonpos
    {f : ℕ → ℝ} (hsum : Summable f) (hf : ∀ n, f n ≤ 0) :
    ∑' n, f n ≤ f 0 := by
  have htail : ∑' n : ℕ, f (n + 1) ≤ 0 := by
    exact tsum_nonpos fun n => hf (n + 1)
  have hsplit := hsum.sum_add_tsum_nat_add 1
  calc
    (∑' n : ℕ, f n)
        =
      (∑ n ∈ Finset.range 1, f n)
        + ∑' n : ℕ, f (n + 1) := hsplit.symm
    _ = f 0 + ∑' n : ℕ, f (n + 1) := by
      simp
    _ ≤ f 0 := by linarith

/--
Every nonconstant plus-side coefficient only decreases the series, so the
constant coefficient gives the uniform bound `H₊(s) ≤ -b₀`.
-/
theorem unequalDampedPlusSeries_le_neg_b0
    {s : ℝ} (hs : 0 ≤ s)
    (hsum : Summable (unequalDampedPlusSeriesTerm s)) :
    unequalDampedPlusSeries s ≤ -unequalDampedB0 := by
  unfold unequalDampedPlusSeries
  calc
    (∑' n : ℕ, unequalDampedPlusSeriesTerm s n)
        ≤ unequalDampedPlusSeriesTerm s 0 :=
      tsum_le_zero_term_of_nonpos hsum
        (unequalDampedPlusSeriesTerm_nonpos hs)
    _ = -unequalDampedB0 := by
      simp [unequalDampedPlusSeriesTerm]

/--
The identical uniform bound for the sample-swapped series.
-/
theorem unequalDampedMinusSeries_le_neg_b0
    {s : ℝ} (hs : 0 ≤ s)
    (hsum : Summable (unequalDampedMinusSeriesTerm s)) :
    unequalDampedMinusSeries s ≤ -unequalDampedB0 := by
  unfold unequalDampedMinusSeries
  calc
    (∑' n : ℕ, unequalDampedMinusSeriesTerm s n)
        ≤ unequalDampedMinusSeriesTerm s 0 :=
      tsum_le_zero_term_of_nonpos hsum
        (unequalDampedMinusSeriesTerm_nonpos hs)
    _ = -unequalDampedB0 := by
      simp [unequalDampedMinusSeriesTerm]

theorem unequalDampedPlusSeries_neg
    {s : ℝ} (hs : 0 ≤ s)
    (hsum : Summable (unequalDampedPlusSeriesTerm s)) :
    unequalDampedPlusSeries s < 0 :=
  (unequalDampedPlusSeries_le_neg_b0 hs hsum).trans_lt
    (neg_neg_of_pos unequalDampedB0_pos)

theorem unequalDampedMinusSeries_neg
    {s : ℝ} (hs : 0 ≤ s)
    (hsum : Summable (unequalDampedMinusSeriesTerm s)) :
    unequalDampedMinusSeries s < 0 :=
  (unequalDampedMinusSeries_le_neg_b0 hs hsum).trans_lt
    (neg_neg_of_pos unequalDampedB0_pos)

end

end GraybillDeal
