import GraybillDeal.UniversalReducedKernel
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite-prior Bayes actions under squared loss

The complete-class theorem used by the universal argument produces priors
with finite support.  This module proves, directly and without any
probability formalism, that their unique Bayes action under squared loss is
the posterior weighted mean.
-/

namespace GraybillDeal

open scoped BigOperators

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- A finite weighted squared loss. -/
def finiteWeightedSquaredLoss
    (s : Finset ι) (weight parameter : ι → ℝ) (action : ℝ) : ℝ :=
  ∑ i ∈ s, weight i * (action - parameter i) ^ 2

/-- The total weight on a finite support. -/
def finiteWeightTotal (s : Finset ι) (weight : ι → ℝ) : ℝ :=
  ∑ i ∈ s, weight i

/-- The finite weighted mean. -/
def finiteWeightedMean
    (s : Finset ι) (weight parameter : ι → ℝ) : ℝ :=
  (∑ i ∈ s, weight i * parameter i) / finiteWeightTotal s weight

theorem finiteWeightTotal_const_mul
    (s : Finset ι) (weight : ι → ℝ) (c : ℝ) :
    finiteWeightTotal s (fun i => c * weight i)
      = c * finiteWeightTotal s weight := by
  unfold finiteWeightTotal
  rw [Finset.mul_sum]

theorem finiteWeightedMean_const_mul
    (s : Finset ι) (weight parameter : ι → ℝ)
    {c : ℝ} (hc : c ≠ 0)
    (hweight : finiteWeightTotal s weight ≠ 0) :
    finiteWeightedMean s (fun i => c * weight i) parameter
      = finiteWeightedMean s weight parameter := by
  unfold finiteWeightedMean
  rw [finiteWeightTotal_const_mul]
  have hnum :
      (∑ i ∈ s, (c * weight i) * parameter i)
        = c * ∑ i ∈ s, weight i * parameter i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hnum]
  field_simp [hc, hweight]

/-- Normalizing a positive endpoint reweighting does not change the
posterior mean: the normalizing constant is common to every posterior
weight and cancels. -/
theorem finiteWeightedMean_reweight_normalization
    (s : Finset ι)
    (prior endpoint kernel parameter : ι → ℝ)
    {normalizer : ℝ} (hnormalizer : normalizer ≠ 0)
    (hposterior :
      finiteWeightTotal s
        (fun i => prior i * endpoint i * kernel i) ≠ 0) :
    finiteWeightedMean s
        (fun i =>
          (prior i * endpoint i / normalizer) * kernel i)
        parameter
      =
    finiteWeightedMean s
        (fun i => prior i * endpoint i * kernel i)
        parameter := by
  have hfun :
      (fun i =>
          (prior i * endpoint i / normalizer) * kernel i)
        =
      (fun i =>
          (1 / normalizer)
            * (prior i * endpoint i * kernel i)) := by
    funext i
    ring
  rw [hfun]
  exact finiteWeightedMean_const_mul
    s (fun i => prior i * endpoint i * kernel i)
      parameter (one_div_ne_zero hnormalizer) hposterior

theorem finite_weighted_centered_sum_eq_zero
    (s : Finset ι) (weight parameter : ι → ℝ)
    (hweight : finiteWeightTotal s weight ≠ 0) :
    ∑ i ∈ s,
        weight i * (finiteWeightedMean s weight parameter - parameter i)
      = 0 := by
  have hsum : (∑ i ∈ s, weight i) ≠ 0 := by
    simpa [finiteWeightTotal] using hweight
  unfold finiteWeightedMean finiteWeightTotal
  calc
    ∑ i ∈ s,
        weight i *
          ((∑ j ∈ s, weight j * parameter j) /
            (∑ j ∈ s, weight j) - parameter i)
        =
      ((∑ j ∈ s, weight j * parameter j) /
          (∑ j ∈ s, weight j))
          * (∑ i ∈ s, weight i)
        - ∑ i ∈ s, weight i * parameter i := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib]
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = 0 := by
      rw [div_mul_cancel₀ _ hsum]
      ring

theorem finite_weighted_squared_loss_decomposition
    (s : Finset ι) (weight parameter : ι → ℝ)
    (hweight : finiteWeightTotal s weight ≠ 0)
    (action : ℝ) :
    finiteWeightedSquaredLoss s weight parameter action
      =
    finiteWeightedSquaredLoss s weight parameter
        (finiteWeightedMean s weight parameter)
      + finiteWeightTotal s weight
          * (action - finiteWeightedMean s weight parameter) ^ 2 := by
  let mean := finiteWeightedMean s weight parameter
  have hcenter :
      ∑ i ∈ s, weight i * (mean - parameter i) = 0 := by
    simpa only [mean] using
      finite_weighted_centered_sum_eq_zero
        s weight parameter hweight
  unfold finiteWeightedSquaredLoss
  have hpoint (i : ι) :
      weight i * (action - parameter i) ^ 2
        =
      weight i * (mean - parameter i) ^ 2
        + weight i * (action - mean) ^ 2
        + 2 * (action - mean) * (weight i * (mean - parameter i)) := by
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hcenter]
  simp only [mul_zero, add_zero]
  rfl

theorem finiteWeightedMean_unique_minimizer
    (s : Finset ι) (weight parameter : ι → ℝ)
    (hweight : 0 < finiteWeightTotal s weight)
    {action : ℝ}
    (haction :
      action ≠ finiteWeightedMean s weight parameter) :
    finiteWeightedSquaredLoss s weight parameter
        (finiteWeightedMean s weight parameter)
      <
    finiteWeightedSquaredLoss s weight parameter action := by
  rw [finite_weighted_squared_loss_decomposition
    s weight parameter (ne_of_gt hweight) action]
  have hsquare :
      0 < (action - finiteWeightedMean s weight parameter) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr haction)
  nlinarith

theorem finiteWeightedMean_is_minimizer
    (s : Finset ι) (weight parameter : ι → ℝ)
    (hweight : 0 < finiteWeightTotal s weight)
    (action : ℝ) :
    finiteWeightedSquaredLoss s weight parameter
        (finiteWeightedMean s weight parameter)
      ≤
    finiteWeightedSquaredLoss s weight parameter action := by
  by_cases h :
      action = finiteWeightedMean s weight parameter
  · simpa [h]
  · exact (finiteWeightedMean_unique_minimizer
      s weight parameter hweight h).le

end

end GraybillDeal
