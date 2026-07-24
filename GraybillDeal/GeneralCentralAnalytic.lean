import GraybillDeal.GeneralCollectedIntegration

/-!
# The central analytic theorem at every equal sample size

The preceding modules establish that, for residual degrees of freedom
`ν ≥ 9` and `|s| < 1`, the paired real-power integral `generalI ν s` is
the sum of the coefficient series at `z = s²`.

This file combines that exact identification with the algebraic positivity
certificate in `GeneralSeriesCertificate.lean`.  It is the all-sample-size
counterpart of the final conclusions in `CollectedIntegration.lean`.
-/

namespace GraybillDeal

noncomputable section

/--
The first-three-term polynomial gives a strict, uniform-in-`s` lower
certificate for the general integral.
-/
theorem general_certificate_le_generalI
    (ν : ℕ) (hν : 9 ≤ ν) {s : ℝ} (hs : |s| < 1) :
    generalMoment (ν : ℝ) 1
        * generalLowerQuadratic (ν : ℝ) (s ^ 2)
      ≤ generalI (ν : ℝ) s := by
  have hνR : (9 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
  rw [generalI_eq_generalSeriesSum_sq hνR hs]
  exact general_lower_certificate_le_seriesSum ν hν (sq_nonneg s)
    (hasSum_generalSeriesTerm_sq_eq_generalI hνR hs).summable

/--
The central linear-risk integral is strictly positive for every integer
residual degree of freedom `ν ≥ 9`, equivalently every equal sample size
`n = ν + 1 ≥ 10`.
-/
theorem generalI_pos
    (ν : ℕ) (hν : 9 ≤ ν) {s : ℝ} (hs : |s| < 1) :
    0 < generalI (ν : ℝ) s := by
  have hνR : (9 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
  have hs_bounds := abs_lt.mp hs
  have hs2_le : s ^ 2 ≤ 1 := by
    nlinarith [mul_pos (sub_pos.mpr hs_bounds.2)
      (by linarith : 0 < 1 + s)]
  rw [generalI_eq_generalSeriesSum_sq hνR hs]
  exact generalSeriesSum_pos ν hν (sq_nonneg s) hs2_le
    (hasSum_generalSeriesTerm_sq_eq_generalI hνR hs).summable

/--
The lower certificate stated directly in terms of the common sample size
`n`, with residual degrees of freedom `ν = n - 1`.
-/
theorem general_certificate_le_generalI_sampleSize
    (n : ℕ) (hn : 10 ≤ n) {s : ℝ} (hs : |s| < 1) :
    generalMoment ((n - 1 : ℕ) : ℝ) 1
        * generalLowerQuadratic ((n - 1 : ℕ) : ℝ) (s ^ 2)
      ≤ generalI ((n - 1 : ℕ) : ℝ) s := by
  have hν : 9 ≤ n - 1 := by
    have h := Nat.sub_le_sub_right hn 1
    norm_num at h ⊢
    exact h
  exact general_certificate_le_generalI (n - 1) hν hs

/--
The same positivity result stated directly in terms of the common sample
size `n`, with residual degrees of freedom `ν = n - 1`.
-/
theorem generalI_pos_sampleSize
    (n : ℕ) (hn : 10 ≤ n) {s : ℝ} (hs : |s| < 1) :
    0 < generalI ((n - 1 : ℕ) : ℝ) s := by
  have hν : 9 ≤ n - 1 := by
    have h := Nat.sub_le_sub_right hn 1
    norm_num at h ⊢
    exact h
  exact generalI_pos (n - 1) hν hs

end

end GraybillDeal
