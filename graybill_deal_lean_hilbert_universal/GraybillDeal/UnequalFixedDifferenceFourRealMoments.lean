import GraybillDeal.UnequalFixedDifferenceFourSeriesBridge

/-!
# Real-parameter beta moments for the full difference-four diagonal

The existing fixed-difference-four theorem uses a natural parameter `m` and
therefore reaches the odd sample-size pairs

`(2m - 1, 2m + 3)`.

For an arbitrary pair `(n, n + 4)`, the same beta shapes are

`m - 1` and `m + 1`, where `m = (n + 1) / 2`.

Even `n` makes `m` half-integral.  This module removes the only analytic
parity restriction in the beta-moment bridge: it defines the chart densities
with real powers and proves their continuity and exact monomial moments for
every real `m ≥ 7`.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

def unequalFixedDifferenceFourRealPlusDensity (m y : ℝ) : ℝ :=
  (1 / ProbabilityTheory.beta (m + 1) (m - 1))
    * y ^ m * (1 - y) ^ (m - 2)

def unequalFixedDifferenceFourRealMinusDensity (m y : ℝ) : ℝ :=
  (1 / ProbabilityTheory.beta (m - 1) (m + 1))
    * y ^ (m - 2) * (1 - y) ^ m

def unequalFixedDifferenceFourRealPlusMoment (m : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n,
    (m + 1 + (i : ℝ)) / (2 * m + (i : ℝ))

def unequalFixedDifferenceFourRealMinusMoment (m : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n,
    (m - 1 + (i : ℝ)) / (2 * m + (i : ℝ))

theorem continuous_unequalFixedDifferenceFourRealPlusDensity
    {m : ℝ} (hm : 7 ≤ m) :
    Continuous (unequalFixedDifferenceFourRealPlusDensity m) := by
  unfold unequalFixedDifferenceFourRealPlusDensity
  apply Continuous.mul
  · apply Continuous.mul continuous_const
    exact Real.continuous_rpow_const (by linarith)
  · exact
      continuous_const.sub continuous_id
        |>.rpow_const (fun _ => Or.inr (by linarith))

theorem continuous_unequalFixedDifferenceFourRealMinusDensity
    {m : ℝ} (hm : 7 ≤ m) :
    Continuous (unequalFixedDifferenceFourRealMinusDensity m) := by
  unfold unequalFixedDifferenceFourRealMinusDensity
  apply Continuous.mul
  · apply Continuous.mul continuous_const
    exact Real.continuous_rpow_const (by linarith)
  · exact
      continuous_const.sub continuous_id
        |>.rpow_const (fun _ => Or.inr (by linarith))

theorem integral_pow_betaMeasure_unequalFixedDifferenceFourRealPlus
    {m : ℝ} (hm : 7 ≤ m) (n : ℕ) :
    (∫ y, y ^ n
      ∂ProbabilityTheory.betaMeasure (m + 1) (m - 1))
      = unequalFixedDifferenceFourRealPlusMoment m n := by
  have ha : 0 < m + 1 := by linarith
  have hb : 0 < m - 1 := by linarith
  rw [integral_pow_betaMeasure_eq_beta_ratio ha hb n]
  rw [beta_ratio_eq_finset_prod ha hb]
  unfold unequalFixedDifferenceFourRealPlusMoment
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  ring

theorem integral_pow_betaMeasure_unequalFixedDifferenceFourRealMinus
    {m : ℝ} (hm : 7 ≤ m) (n : ℕ) :
    (∫ y, y ^ n
      ∂ProbabilityTheory.betaMeasure (m - 1) (m + 1))
      = unequalFixedDifferenceFourRealMinusMoment m n := by
  have ha : 0 < m - 1 := by linarith
  have hb : 0 < m + 1 := by linarith
  rw [integral_pow_betaMeasure_eq_beta_ratio ha hb n]
  rw [beta_ratio_eq_finset_prod ha hb]
  unfold unequalFixedDifferenceFourRealMinusMoment
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  ring

theorem integral_unequalFixedDifferenceFourRealPlusDensity_pow
    {m : ℝ} (hm : 7 ≤ m) (n : ℕ) :
    (∫ y in (0 : ℝ)..1,
      unequalFixedDifferenceFourRealPlusDensity m y * y ^ n)
      = unequalFixedDifferenceFourRealPlusMoment m n := by
  have ha : 0 < m + 1 := by linarith
  have hb : 0 < m - 1 := by linarith
  have hmeasure :=
    integral_pow_betaMeasure_unequalFixedDifferenceFourRealPlus hm n
  rw [integral_betaMeasure_eq_interval_of_shapes_pos ha hb] at hmeasure
  rw [← hmeasure]
  apply intervalIntegral.integral_congr_uIoo
  intro y hy
  unfold unequalFixedDifferenceFourRealPlusDensity
  dsimp only
  congr 1 <;> ring

theorem integral_unequalFixedDifferenceFourRealMinusDensity_pow
    {m : ℝ} (hm : 7 ≤ m) (n : ℕ) :
    (∫ y in (0 : ℝ)..1,
      unequalFixedDifferenceFourRealMinusDensity m y * y ^ n)
      = unequalFixedDifferenceFourRealMinusMoment m n := by
  have ha : 0 < m - 1 := by linarith
  have hb : 0 < m + 1 := by linarith
  have hmeasure :=
    integral_pow_betaMeasure_unequalFixedDifferenceFourRealMinus hm n
  rw [integral_betaMeasure_eq_interval_of_shapes_pos ha hb] at hmeasure
  rw [← hmeasure]
  apply intervalIntegral.integral_congr_uIoo
  intro y hy
  unfold unequalFixedDifferenceFourRealMinusDensity
  dsimp only
  congr 1 <;> ring

end

end GraybillDeal
