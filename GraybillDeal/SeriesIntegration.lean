import GraybillDeal.IntegralPairing
import GraybillDeal.PointwiseSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Termwise integration of the paired kernel series

This file supplies an explicit summable uniform majorant for the pointwise
series in `PointwiseSeries.lean`, and applies interval-integral dominated
convergence.  The result is a `HasSum` theorem for the integrals of the raw
negative-binomial summands.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

/-- A deliberately coarse uniform majorant for the paired numerator. -/
def pointwiseMajorant13 (s : ℝ) (m : ℕ) : ℝ :=
  60 * ((m + 4).choose 4 : ℝ) * (s ^ 2) ^ m

theorem pairedPolynomial13_abs_le {s x : ℝ}
    (hs : |s| < 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    |pairedPolynomial13 (s ^ 2) (x ^ 2)| ≤ 60 := by
  have hs_bounds := abs_lt.mp hs
  have hz0 : 0 ≤ s ^ 2 := sq_nonneg s
  have hz1 : s ^ 2 ≤ 1 := by
    nlinarith [mul_pos (sub_pos.mpr hs_bounds.2) (by linarith : 0 < 1 + s)]
  have hy0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hy1 : x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hz2 : 0 ≤ (s ^ 2) ^ 2 := sq_nonneg (s ^ 2)
  have hz3 : 0 ≤ (s ^ 2) ^ 3 := pow_nonneg hz0 3
  have hy2 : 0 ≤ (x ^ 2) ^ 2 := sq_nonneg (x ^ 2)
  have hy3 : 0 ≤ (x ^ 2) ^ 3 := pow_nonneg hy0 3
  have hz2le : (s ^ 2) ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ hz0 hz1 2
  have hz3le : (s ^ 2) ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ hz0 hz1 3
  have hy2le : (x ^ 2) ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ hy0 hy1 2
  have hy3le : (x ^ 2) ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ hy0 hy1 3
  have hzy0 : 0 ≤ s ^ 2 * x ^ 2 := mul_nonneg hz0 hy0
  have hz2y0 : 0 ≤ (s ^ 2) ^ 2 * x ^ 2 := mul_nonneg hz2 hy0
  have hz2y20 : 0 ≤ (s ^ 2) ^ 2 * (x ^ 2) ^ 2 := mul_nonneg hz2 hy2
  have hz3y20 : 0 ≤ (s ^ 2) ^ 3 * (x ^ 2) ^ 2 := mul_nonneg hz3 hy2
  have hz3y30 : 0 ≤ (s ^ 2) ^ 3 * (x ^ 2) ^ 3 := mul_nonneg hz3 hy3
  have hzy1 : s ^ 2 * x ^ 2 ≤ 1 :=
    (mul_le_mul hz1 hy1 hy0 (by norm_num)).trans_eq (by norm_num)
  have hz2y1 : (s ^ 2) ^ 2 * x ^ 2 ≤ 1 :=
    (mul_le_mul hz2le hy1 hy0 (by norm_num)).trans_eq (by norm_num)
  have hz2y21 : (s ^ 2) ^ 2 * (x ^ 2) ^ 2 ≤ 1 :=
    (mul_le_mul hz2le hy2le hy2 (by norm_num)).trans_eq (by norm_num)
  have hz3y21 : (s ^ 2) ^ 3 * (x ^ 2) ^ 2 ≤ 1 :=
    (mul_le_mul hz3le hy2le hy2 (by norm_num)).trans_eq (by norm_num)
  have hz3y31 : (s ^ 2) ^ 3 * (x ^ 2) ^ 3 ≤ 1 :=
    (mul_le_mul hz3le hy3le hy3 (by norm_num)).trans_eq (by norm_num)
  rw [abs_le]
  constructor <;> unfold pairedPolynomial13 <;> nlinarith

theorem pairedSeriesPrefactor13_abs_le {s x : ℝ}
    (hs : |s| < 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    |pairedSeriesPrefactor13 s x| ≤ 60 := by
  have hx2_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hx2_le : x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hbase_nonneg : 0 ≤ 1 - x ^ 2 := sub_nonneg.mpr hx2_le
  have hbase_le : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hweight_le : (1 - x ^ 2) ^ 6 ≤ 1 := by
    simpa using pow_le_pow_left₀ hbase_nonneg hbase_le 6
  have hpoly := pairedPolynomial13_abs_le hs hx
  unfold pairedSeriesPrefactor13
  rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hbase_nonneg,
    abs_of_nonneg hx2_nonneg]
  calc
    (1 - x ^ 2) ^ 6 * x ^ 2
          * |pairedPolynomial13 (s ^ 2) (x ^ 2)|
        ≤ 1 * 1 * 60 := by gcongr
    _ = 60 := by norm_num

theorem pointwiseSeriesTerm13_norm_le {s x : ℝ} (m : ℕ)
    (hs : |s| < 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖pointwiseSeriesTerm13 s x m‖ ≤ pointwiseMajorant13 s m := by
  have hz0 : 0 ≤ s ^ 2 := sq_nonneg s
  have hy0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hy1 : x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hzy0 : 0 ≤ s ^ 2 * x ^ 2 := mul_nonneg hz0 hy0
  have hzy_le : s ^ 2 * x ^ 2 ≤ s ^ 2 := by
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hy1)]
  have hpow : (s ^ 2 * x ^ 2) ^ m ≤ (s ^ 2) ^ m :=
    pow_le_pow_left₀ hzy0 hzy_le m
  have hpref := pairedSeriesPrefactor13_abs_le hs hx
  have hchoose : 0 ≤ ((m + 4).choose 4 : ℝ) := by positivity
  unfold pointwiseSeriesTerm13 pointwiseMajorant13
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hchoose,
    abs_pow, abs_of_nonneg hzy0]
  calc
    |pairedSeriesPrefactor13 s x|
          * (((m + 4).choose 4 : ℝ) * (s ^ 2 * x ^ 2) ^ m)
        ≤ 60 * (((m + 4).choose 4 : ℝ) * (s ^ 2 * x ^ 2) ^ m) := by
          gcongr
    _ ≤ 60 * (((m + 4).choose 4 : ℝ) * (s ^ 2) ^ m) := by
          gcongr
    _ = 60 * ((m + 4).choose 4 : ℝ) * (s ^ 2) ^ m := by ring

theorem summable_pointwiseMajorant13 {s : ℝ} (hs : |s| < 1) :
    Summable (pointwiseMajorant13 s) := by
  have hs2 : ‖s ^ 2‖ < 1 := by
    simpa using
      (sq_mul_sq_norm_lt_one hs (x := (1 : ℝ)) (by norm_num))
  have h :=
    (summable_choose_four_mul_geometric hs2).mul_left (60 : ℝ)
  change Summable
    (fun m => 60 * ((m + 4).choose 4 : ℝ) * (s ^ 2) ^ m)
  simpa only [mul_assoc] using h

/--
A reusable unit-interval form of dominated convergence for a uniformly
majorized series.
-/
theorem hasSum_intervalIntegral_of_uniform_majorant
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {c : ℕ → ℝ}
    (hF_cont : ∀ n, ContinuousOn (F n) (uIcc (0 : ℝ) 1))
    (hbound : ∀ n x, x ∈ uIcc (0 : ℝ) 1 → ‖F n x‖ ≤ c n)
    (hc : Summable c)
    (hsum : ∀ x, x ∈ uIcc (0 : ℝ) 1 → HasSum (fun n => F n x) (f x)) :
    HasSum (fun n => ∫ x in (0 : ℝ)..1, F n x)
      (∫ x in (0 : ℝ)..1, f x) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (fun n _ => c n) ?_ ?_ ?_ ?_ ?_
  · intro n
    exact ((hF_cont n).mono uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  · intro n
    exact ae_of_all _ fun x hx => hbound n x (uIoc_subset_uIcc hx)
  · exact ae_of_all _ fun _ _ => hc
  · simpa only using
      (intervalIntegrable_const :
        IntervalIntegrable (fun _ : ℝ => ∑' n, c n) volume 0 1)
  · exact ae_of_all _ fun x hx => hsum x (uIoc_subset_uIcc hx)

/--
The raw negative-binomial summands may be integrated term by term.
-/
theorem hasSum_integral_pointwiseSeries13 {s : ℝ} (hs : |s| < 1) :
    HasSum
      (fun m => ∫ x in (0 : ℝ)..1, pointwiseSeriesTerm13 s x m)
      (I13 s) := by
  have h :
      HasSum
        (fun m => ∫ x in (0 : ℝ)..1, pointwiseSeriesTerm13 s x m)
        (∫ x in (0 : ℝ)..1,
          (1 - x ^ 2) ^ 6 * x ^ 2
            * pairedPolynomial13 (s ^ 2) (x ^ 2)
            / (1 - s ^ 2 * x ^ 2) ^ 5) := by
    apply hasSum_intervalIntegral_of_uniform_majorant
      (c := pointwiseMajorant13 s)
    · intro m
      apply Continuous.continuousOn
      unfold pointwiseSeriesTerm13 pairedSeriesPrefactor13 pairedPolynomial13
      fun_prop
    · intro m x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le] using hx
      exact pointwiseSeriesTerm13_norm_le m hs hx'
    · exact summable_pointwiseMajorant13 hs
    · intro x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le] using hx
      exact hasSum_pointwiseSeries13 hs hx'
  simpa only [I13_eq_paired hs] using h

end

end GraybillDeal
