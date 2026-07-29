import GraybillDeal.GeneralKernel
import GraybillDeal.IntegralPairing
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Pairing the generalized Graybill--Deal integral

This file lifts the pointwise identity in `GeneralKernel.lean` to the
interval integral denoted by

`I_ν(s) = ∫ x in -1..1, generalLinearKernel ν s x`.

The only analytic issue not present in the fixed `n = 13` proof is the
real-power weight `(1 - x²)^(ν / 2)`.  For nonnegative `ν` this weight is
continuous, including at `x = ±1`, so the generalized kernel is interval
integrable on both halves of `[-1,1]`.
-/

namespace GraybillDeal

open Set
open MeasureTheory

noncomputable section

/--
The generalized linear kernel is continuous on `[-1,1]` whenever the
residual degrees of freedom are nonnegative and `|s| < 1`.
-/
theorem generalLinearKernel_continuousOn
    {ν s : ℝ} (hν : 0 ≤ ν) (hs : |s| < 1) :
    ContinuousOn (generalLinearKernel ν s) (Icc (-1) 1) := by
  have hden : ∀ x ∈ Icc (-1 : ℝ) 1, (1 + s * x) ^ 5 ≠ 0 := by
    intro x hx
    apply pow_ne_zero
    apply ne_of_gt
    apply one_add_sx_pos hs
    rw [abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hbase : Continuous (fun x : ℝ => 1 - x ^ 2) :=
    continuous_const.sub (continuous_id.pow 2)
  have hexponent : 0 ≤ ν / 2 := by positivity
  have hweight :
      Continuous (fun x : ℝ => (1 - x ^ 2) ^ (ν / 2)) :=
    (Real.continuous_rpow_const hexponent).comp hbase
  have hnumerator :
      Continuous
        (fun x : ℝ =>
          x * (s + x) * (generalAlpha ν + s * x)) :=
    (continuous_id.mul (continuous_const.add continuous_id)).mul
      (continuous_const.add (continuous_const.mul continuous_id))
  have hdenominator :
      Continuous (fun x : ℝ => (1 + s * x) ^ 5) :=
    (continuous_const.add (continuous_const.mul continuous_id)).pow 5
  unfold generalLinearKernel generalLinearCore
  exact hweight.continuousOn.mul
    (hnumerator.continuousOn.div hdenominator.continuousOn hden)

/--
The generalized kernel is interval integrable over the negative half of the
symmetric interval.
-/
theorem generalLinearKernel_intervalIntegrable_neg
    {ν s : ℝ} (hν : 0 ≤ ν) (hs : |s| < 1) :
    IntervalIntegrable (generalLinearKernel ν s) volume (-1) 0 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact (generalLinearKernel_continuousOn hν hs).mono (by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩)

/--
The generalized kernel is interval integrable over the positive half of the
symmetric interval.
-/
theorem generalLinearKernel_intervalIntegrable_pos
    {ν s : ℝ} (hν : 0 ≤ ν) (hs : |s| < 1) :
    IntervalIntegrable (generalLinearKernel ν s) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact (generalLinearKernel_continuousOn hν hs).mono (by
    intro x hx
    exact ⟨(by linarith [hx.1]), hx.2⟩)

/-- The generalized integral denoted by `I_ν(s)`. -/
def generalI (ν s : ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, generalLinearKernel ν s x

/--
Pairing the contributions at `x` and `-x` rewrites `I_ν(s)` as an integral
over `[0,1]`.  The assumption `9 ≤ ν` is exactly the range needed for equal
sample sizes `n = ν + 1 ≥ 10`.
-/
theorem generalI_eq_paired
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    generalI ν s
      =
    ∫ x in (0 : ℝ)..1,
      (1 - x ^ 2) ^ (ν / 2) * x ^ 2
        * generalPairedPolynomial ν (s ^ 2) (x ^ 2)
        / (1 - s ^ 2 * x ^ 2) ^ 5 := by
  unfold generalI
  rw [integral_neg_one_one_eq_pair
    (generalLinearKernel ν s)
    (generalLinearKernel_intervalIntegrable_neg (by linarith) hs)
    (generalLinearKernel_intervalIntegrable_pos (by linarith) hs)]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [uIcc_of_le zero_le_one] at hx
  apply generalLinearKernel_add_neg hs
  rw [abs_le]
  exact ⟨by linarith [hx.1], hx.2⟩

end

end GraybillDeal
