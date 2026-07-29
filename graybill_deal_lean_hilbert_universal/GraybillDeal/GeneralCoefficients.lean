import GraybillDeal.GeneralMoments

/-!
# General series coefficients

This file packages the coefficient signs from the all-sample-size argument.
For `m ≥ 3`,

`4(ν-1)(2m+1) Qm`

is a nonnegative binomial combination of five explicit polynomials, with a
strictly positive constant term.  The polynomial signs were already proved
in `Algebra.lean`; here they are assembled into a positive coefficient
sequence for every `ν ≥ 9`.
-/

namespace GraybillDeal

noncomputable section

def generalTailP0 (ν : ℝ) : ℝ :=
  308 * ν ^ 2 - 896 * ν - 672

def generalTailP1 (ν : ℝ) : ℝ :=
  712 * ν ^ 2 - 1774 * ν - 648

def generalTailP2 (ν : ℝ) : ℝ :=
  798 * ν ^ 2 - 1804 * ν - 320

def generalTailP3 (ν : ℝ) : ℝ :=
  440 * ν ^ 2 - 928 * ν - 64

def generalTailP4 (ν : ℝ) : ℝ :=
  96 * ν ^ 2 - 192 * ν

/-- Numerator of the closed positive-tail formula. -/
def generalTailNumerator (ν : ℝ) (m : ℕ) : ℝ :=
  generalTailP0 ν
    + generalTailP1 ν * (Nat.choose (m - 3) 1 : ℝ)
    + generalTailP2 ν * (Nat.choose (m - 3) 2 : ℝ)
    + generalTailP3 ν * (Nat.choose (m - 3) 3 : ℝ)
    + generalTailP4 ν * (Nat.choose (m - 3) 4 : ℝ)

/-- The general coefficient formula for indices `m ≥ 3`. -/
def generalTailQ (ν : ℝ) (m : ℕ) : ℝ :=
  generalTailNumerator ν m /
    (4 * (ν - 1) * (2 * (m : ℝ) + 1))

theorem generalTailNumerator_pos {ν : ℝ} (hν : 9 ≤ ν) (m : ℕ) :
    0 < generalTailNumerator ν m := by
  have h8 : 8 ≤ ν := by linarith
  have h0 : 0 < generalTailP0 ν := by
    exact tail_D0_pos ν h8
  have h1 : 0 ≤
      generalTailP1 ν * (Nat.choose (m - 3) 1 : ℝ) :=
    mul_nonneg (le_of_lt (tail_D1_pos ν h8)) (by positivity)
  have h2 : 0 ≤
      generalTailP2 ν * (Nat.choose (m - 3) 2 : ℝ) :=
    mul_nonneg (le_of_lt (tail_D2_pos ν h8)) (by positivity)
  have h3 : 0 ≤
      generalTailP3 ν * (Nat.choose (m - 3) 3 : ℝ) :=
    mul_nonneg (le_of_lt (tail_D3_pos ν h8)) (by positivity)
  have h4 : 0 ≤
      generalTailP4 ν * (Nat.choose (m - 3) 4 : ℝ) :=
    mul_nonneg (le_of_lt (tail_D4_pos ν h8)) (by positivity)
  unfold generalTailNumerator
  simp only [generalTailP0, generalTailP1, generalTailP2, generalTailP3,
    generalTailP4] at h0 h1 h2 h3 h4 ⊢
  linarith

theorem generalTailQ_pos {ν : ℝ} (hν : 9 ≤ ν) (m : ℕ) :
    0 < generalTailQ ν m := by
  unfold generalTailQ
  apply div_pos (generalTailNumerator_pos hν m)
  have hνden : 0 < ν - 1 := by linarith
  have hmden : 0 < 2 * (m : ℝ) + 1 := by positivity
  positivity

/-- The complete generalized coefficient sequence. -/
def generalSeriesQ (ν : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then generalQ0 ν
  else if m = 1 then generalQ1 ν
  else if m = 2 then generalQ2 ν
  else generalTailQ ν m

@[simp]
theorem generalSeriesQ_zero (ν : ℝ) :
    generalSeriesQ ν 0 = generalQ0 ν := by
  simp [generalSeriesQ]

@[simp]
theorem generalSeriesQ_one (ν : ℝ) :
    generalSeriesQ ν 1 = generalQ1 ν := by
  simp [generalSeriesQ]

@[simp]
theorem generalSeriesQ_two (ν : ℝ) :
    generalSeriesQ ν 2 = generalQ2 ν := by
  simp [generalSeriesQ]

theorem generalSeriesQ_add_three_pos
    {ν : ℝ} (hν : 9 ≤ ν) (m : ℕ) :
    0 < generalSeriesQ ν (m + 3) := by
  have h0 : m + 3 ≠ 0 := by omega
  have h1 : m + 3 ≠ 1 := by omega
  have h2 : m + 3 ≠ 2 := by omega
  simp only [generalSeriesQ, if_neg h0, if_neg h1, if_neg h2]
  exact generalTailQ_pos hν (m + 3)

end

end GraybillDeal
