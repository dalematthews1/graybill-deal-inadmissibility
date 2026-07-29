import GraybillDeal.AnalyticKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Pairing an interval integral at `x` and `-x`

This file turns the pointwise identity from `AnalyticKernel.lean` into the
corresponding identity of interval integrals.
-/

namespace GraybillDeal

open Set
open MeasureTheory

noncomputable section

/-- Split a symmetric interval and reflect its negative half. -/
theorem integral_neg_one_one_eq_pair
    (f : ℝ → ℝ)
    (hneg : IntervalIntegrable f volume (-1) 0)
    (hpos : IntervalIntegrable f volume 0 1) :
    (∫ x in (-1 : ℝ)..1, f x)
      =
    ∫ x in (0 : ℝ)..1, (f x + f (-x)) := by
  have hcomp10 :
      IntervalIntegrable (fun x : ℝ => f (-x)) volume 1 0 :=
    by
      simpa using
        (IntervalIntegrable.iff_comp_neg
          (a := (-1 : ℝ)) (b := 0) (f := f) (by simp)).mp hneg
  have hcomp :
      IntervalIntegrable (fun x : ℝ => f (-x)) volume 0 1 :=
    hcomp10.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals hneg hpos]
  rw [intervalIntegral.integral_add hpos hcomp]
  rw [intervalIntegral.integral_comp_neg]
  norm_num
  ring

private theorem linearKernel13_continuousOn {s : ℝ} (hs : |s| < 1) :
    ContinuousOn (linearKernel13 s) (Icc (-1) 1) := by
  have hden : ∀ x ∈ Icc (-1 : ℝ) 1, (1 + s * x) ^ 5 ≠ 0 := by
    intro x hx
    apply pow_ne_zero
    apply ne_of_gt
    apply one_add_sx_pos hs
    rw [abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hweight : Continuous (fun x : ℝ => (1 - x ^ 2) ^ 6) :=
    (continuous_const.sub (continuous_id.pow 2)).pow 6
  have hnumerator :
      Continuous
        (fun x : ℝ => x * (s + x) * (alpha13 + s * x)) :=
    (continuous_id.mul (continuous_const.add continuous_id)).mul
      (continuous_const.add (continuous_const.mul continuous_id))
  have hdenominator :
      Continuous (fun x : ℝ => (1 + s * x) ^ 5) :=
    (continuous_const.add (continuous_const.mul continuous_id)).pow 5
  unfold linearKernel13 linearCore13
  exact hweight.continuousOn.mul
    (hnumerator.continuousOn.div hdenominator.continuousOn hden)

private theorem linearKernel13_intervalIntegrable_neg {s : ℝ}
    (hs : |s| < 1) :
    IntervalIntegrable (linearKernel13 s) volume (-1) 0 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact (linearKernel13_continuousOn hs).mono (by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩)

private theorem linearKernel13_intervalIntegrable_pos {s : ℝ}
    (hs : |s| < 1) :
    IntervalIntegrable (linearKernel13 s) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact (linearKernel13_continuousOn hs).mono (by
    intro x hx
    exact ⟨(by linarith [hx.1]), hx.2⟩)

/-- The integral denoted by `I(s)` in the counterexample note. -/
def I13 (s : ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, linearKernel13 s x

/--
Equation (8) after pairing the contributions at `x` and `-x`.
-/
theorem I13_eq_paired {s : ℝ} (hs : |s| < 1) :
    I13 s
      =
    ∫ x in (0 : ℝ)..1,
      (1 - x ^ 2) ^ 6 * x ^ 2
        * pairedPolynomial13 (s ^ 2) (x ^ 2)
        / (1 - s ^ 2 * x ^ 2) ^ 5 := by
  unfold I13
  rw [integral_neg_one_one_eq_pair
    (linearKernel13 s)
    (linearKernel13_intervalIntegrable_neg hs)
    (linearKernel13_intervalIntegrable_pos hs)]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [uIcc_of_le zero_le_one] at hx
  apply linearKernel13_add_neg hs
  rw [abs_le]
  exact ⟨by linarith [hx.1], hx.2⟩

end

end GraybillDeal
