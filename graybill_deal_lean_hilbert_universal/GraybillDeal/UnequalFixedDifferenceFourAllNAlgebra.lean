import GraybillDeal.UnequalFixedDifferenceFourRealAlgebra

/-!
# Sample-size algebra for the full difference-four diagonal

The natural-parameter theorem for

`(n₁, n₂) = (2m - 1, 2m + 3)`

only names odd sample sizes because `m` is a natural number.  For the full
diagonal `(n, n + 4)`, the correct analytic parameter is the real number

`mₙ = (n + 1) / 2`.

This file is the thin sample-size wrapper around the real-parameter
certificate.  It does not yet perform the probability-law or raw-estimator
transport.
-/

namespace GraybillDeal

noncomputable section

/-- Real analytic parameter associated with the sample-size pair
`(n, n + 4)`. -/
def unequalFixedDifferenceFourSampleM (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) / 2

theorem unequalFixedDifferenceFourSampleM_ge_seven
    {n : ℕ} (hn : 13 ≤ n) :
    7 ≤ unequalFixedDifferenceFourSampleM n := by
  have hnR : (13 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  unfold unequalFixedDifferenceFourSampleM
  linarith

/-- The lower Beta pivot written directly in terms of the first sample
size. -/
theorem unequalFixedDifferenceFourRealT_sampleM
    {n : ℕ} (hn : 13 ≤ n) :
    unequalFixedDifferenceFourRealT
        (unequalFixedDifferenceFourSampleM n)
      =
    ((n : ℝ) - 1) / (2 * ((n : ℝ) + 1)) := by
  have hnR : (13 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  unfold unequalFixedDifferenceFourRealT
    unequalFixedDifferenceFourSampleM
  field_simp
  ring

/-- The upper Beta pivot written directly in terms of the first sample
size. -/
theorem unequalFixedDifferenceFourRealQ_sampleM
    {n : ℕ} (hn : 13 ≤ n) :
    unequalFixedDifferenceFourRealQ
        (unequalFixedDifferenceFourSampleM n)
      =
    ((n : ℝ) + 3) / (2 * ((n : ℝ) + 1)) := by
  have hnR : (13 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  unfold unequalFixedDifferenceFourRealQ
    unequalFixedDifferenceFourSampleM
  field_simp
  ring

/-- Every pair `(n, n + 4)`, `n ≥ 13`, receives a strictly positive
sample-size-dependent perturbation coefficient. -/
theorem unequalFixedDifferenceFourSampleEpsilon_pos
    {n : ℕ} (hn : 13 ≤ n) :
    0 <
      unequalFixedDifferenceFourRealEpsilon
        (unequalFixedDifferenceFourSampleM n) := by
  exact unequalFixedDifferenceFourRealEpsilon_pos
    (unequalFixedDifferenceFourSampleM_ge_seven hn)

/--
Sample-size form of the ratio-free deterministic risk endgame.

Once the two chart bounds have been proved at
`m = (n + 1) / 2`, the same fixed coefficient works for the full pair
`(n, n + 4)`, without any parity assumption on `n`.
-/
theorem unequalFixedDifferenceFourAllN_reducedRisk_neg_of_bounds
    {n : ℕ} (hn : 13 ≤ n) {s B C : ℝ} (hs : s < 1)
    (hB :
      B ≤
        -unequalFixedDifferenceFourRealB0
            (unequalFixedDifferenceFourSampleM n)
          * (1 - s) ^ 2)
    (hC :
      C ≤
        unequalFixedDifferenceFourRealMPlus
            (unequalFixedDifferenceFourSampleM n)
          * (1 - s) ^ 2) :
    2
          * unequalFixedDifferenceFourRealEpsilon
              (unequalFixedDifferenceFourSampleM n)
          * B
        + unequalFixedDifferenceFourRealEpsilon
              (unequalFixedDifferenceFourSampleM n) ^ 2
          * C
      < 0 := by
  exact unequalFixedDifferenceFourReal_reducedRisk_neg_of_bounds
    (unequalFixedDifferenceFourSampleM_ge_seven hn) hs hB hC

/-! ## First missing even pair -/

@[simp]
theorem unequalFixedDifferenceFourSampleM_fourteen :
    unequalFixedDifferenceFourSampleM 14 = 15 / 2 := by
  norm_num [unequalFixedDifferenceFourSampleM]

theorem unequalFixedDifferenceFourSampleEpsilon_fourteen :
    unequalFixedDifferenceFourRealEpsilon
        (unequalFixedDifferenceFourSampleM 14)
      =
    21893897025 / 44864436152628256 := by
  norm_num [
    unequalFixedDifferenceFourSampleM,
    unequalFixedDifferenceFourRealEpsilon,
    unequalFixedDifferenceFourRealB0,
    unequalFixedDifferenceFourRealMPlus,
    unequalFixedDifferenceFourRealQ,
    unequalFixedDifferenceFourRealC,
    unequalFixedDifferenceFourRealD
  ]

end

end GraybillDeal
