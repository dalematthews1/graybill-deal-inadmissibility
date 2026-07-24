import GraybillDeal.GeneralKernel
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp

/-!
# Derivation of the generalized series coefficients

This module connects the coefficients obtained directly from the paired
kernel to the closed sequence in `GeneralCoefficients.lean`.  It is the
parameter-generic counterpart of `SeriesCoefficients.lean`.
-/

namespace GraybillDeal

noncomputable section

private theorem cast_choose_two_poly (m : ℕ) :
    (Nat.choose m 2 : ℝ) =
      (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  cases m with
  | zero => norm_num [Nat.choose]
  | succ m =>
      rw [Nat.cast_choose_two]

private theorem cast_choose_three_poly (m : ℕ) :
    (Nat.choose m 3 : ℝ) =
      (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) / 6 := by
  induction m with
  | zero => norm_num [Nat.choose]
  | succ m ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.cast_add, Nat.cast_succ]
      rw [cast_choose_two_poly, ih]
      ring

private theorem cast_choose_four_poly (m : ℕ) :
    (Nat.choose m 4 : ℝ) =
      (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2)
        * ((m : ℝ) - 3) / 24 := by
  induction m with
  | zero => norm_num [Nat.choose]
  | succ m ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.cast_add, Nat.cast_succ]
      rw [cast_choose_three_poly, ih]
      ring

/--
The coefficient obtained directly from `generalPairedPolynomial` and the
order-four negative-binomial series, after applying the generalized moment
recurrence.
-/
def generalRawQ (ν : ℝ) (m : ℕ) : ℝ :=
  let α := generalAlpha ν
  let ratio := (2 * (m : ℝ) + ν + 3) / (2 * (m : ℝ) + 1)
  (2 * α) * (Nat.choose (m + 4) 4 : ℝ)
    + (Nat.choose (m + 3) 4 : ℝ)
      * ((2 - 10 * α) * ratio + (-10 + 20 * α))
    + (Nat.choose (m + 2) 4 : ℝ)
      * ((20 - 20 * α) * ratio + (-20 + 10 * α))
    + (Nat.choose (m + 1) 4 : ℝ)
      * ((10 - 2 * α) * ratio - 2)

theorem generalRawQ_zero {ν : ℝ} (hν : ν ≠ 1) :
    generalRawQ ν 0 = generalSeriesQ ν 0 := by
  simp [generalRawQ, generalSeriesQ, generalAlpha, generalQ0, Nat.choose]
  field_simp [sub_ne_zero.mpr hν]
  ring

theorem generalRawQ_one {ν : ℝ} (hν : ν ≠ 1) :
    generalRawQ ν 1 = generalSeriesQ ν 1 := by
  simp [generalRawQ, generalSeriesQ, generalAlpha, generalQ1, Nat.choose]
  field_simp [sub_ne_zero.mpr hν]
  ring

theorem generalRawQ_two {ν : ℝ} (hν : ν ≠ 1) :
    generalRawQ ν 2 = generalSeriesQ ν 2 := by
  simp [generalRawQ, generalSeriesQ, generalAlpha, generalQ2, Nat.choose]
  field_simp [sub_ne_zero.mpr hν]
  ring

/-- Directly derived and closed-form generalized coefficients agree. -/
theorem generalRawQ_eq_generalSeriesQ
    {ν : ℝ} (hν : ν ≠ 1) (m : ℕ) :
    generalRawQ ν m = generalSeriesQ ν m := by
  rcases m with _ | m
  · exact generalRawQ_zero hν
  rcases m with _ | m
  · exact generalRawQ_one hν
  rcases m with _ | m
  · exact generalRawQ_two hν
  have hm0 : m + 3 ≠ 0 := by omega
  have hm1 : m + 3 ≠ 1 := by omega
  have hm2 : m + 3 ≠ 2 := by omega
  simp only [generalSeriesQ, if_neg hm0, if_neg hm1, if_neg hm2]
  unfold generalRawQ generalTailQ generalTailNumerator
  dsimp only
  unfold generalAlpha generalTailP0 generalTailP1 generalTailP2
    generalTailP3 generalTailP4
  simp only [Nat.cast_add]
  field_simp [sub_ne_zero.mpr hν]
  simp [Nat.choose]
  rw [cast_choose_two_poly, cast_choose_three_poly, cast_choose_four_poly]
  ring

end

end GraybillDeal
