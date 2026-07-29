import GraybillDeal.GeneralSeriesCoefficients

/-!
# Integrated coefficients for the generalized paired series

This is the algebraic half of the target-indexed integration argument.  The
real-power moment integral is supplied separately; here the moment recurrence
already identifies every collected coefficient with
`generalMoment ν (m+1) * generalSeriesQ ν m`.
-/

namespace GraybillDeal

noncomputable section

def generalCollectedMomentCoeff (ν : ℝ) (m : ℕ) : ℝ :=
  let α := generalAlpha ν
  ((m + 3).choose 4 : ℝ) * (2 - 10 * α)
    + ((m + 2).choose 4 : ℝ) * (20 - 20 * α)
    + ((m + 1).choose 4 : ℝ) * (10 - 2 * α)

def generalCollectedNextCoeff (ν : ℝ) (m : ℕ) : ℝ :=
  let α := generalAlpha ν
  ((m + 4).choose 4 : ℝ) * (2 * α)
    + ((m + 3).choose 4 : ℝ) * (-10 + 20 * α)
    + ((m + 2).choose 4 : ℝ) * (-20 + 10 * α)
    - ((m + 1).choose 4 : ℝ) * 2

def generalIntegratedCoefficient (ν : ℝ) (m : ℕ) : ℝ :=
  generalCollectedMomentCoeff ν m * generalMoment ν m
    + generalCollectedNextCoeff ν m * generalMoment ν (m + 1)

theorem generalMoment_eq_ratio_mul_succ
    {ν : ℝ} (hν : -2 < ν) (m : ℕ) :
    generalMoment ν m
      =
    ((2 * (m : ℝ) + ν + 3) / (2 * (m : ℝ) + 1))
      * generalMoment ν (m + 1) := by
  have hden : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hden).mpr
  simpa only [mul_comm] using generalMoment_recurrence hν m

/--
The target-indexed collected coefficient is exactly the certified general
series coefficient multiplied by its moment.
-/
theorem generalIntegratedCoefficient_eq
    {ν : ℝ} (hν : 9 ≤ ν) (m : ℕ) :
    generalIntegratedCoefficient ν m
      = generalMoment ν (m + 1) * generalSeriesQ ν m := by
  rw [← generalRawQ_eq_generalSeriesQ (by linarith : ν ≠ 1)]
  unfold generalIntegratedCoefficient generalCollectedMomentCoeff
    generalCollectedNextCoeff
  rw [generalMoment_eq_ratio_mul_succ (by linarith) m]
  unfold generalRawQ
  dsimp only
  ring

end

end GraybillDeal
