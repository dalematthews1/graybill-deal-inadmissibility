import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.HasLaw

/-!
# Centered beta-coordinate bridge at arbitrary shape

For `P ~ Beta(a,a)`, put `x = 2P - 1`.  The centered coordinate has
density proportional to

`(1 - x²) ^ (a - 1)` on `(-1,1)`.

This file proves the exact change-of-variables identity for every `a > 0`,
including nonintegral `a`, and transfers it through an arbitrary `HasLaw`
hypothesis.
-/

namespace GraybillDeal

open MeasureTheory Set ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/--
The normalizing constant of the centered symmetric beta density.

The form

`(1/2) * (1 / beta a a) * (1/4)^(a-1)`

keeps the density normalization, affine Jacobian, and real-power scaling
visibly separate.
-/
def centeredBetaKa (a : ℝ) : ℝ :=
  (1 / 2) * (1 / beta a a) * (1 / 4 : ℝ) ^ (a - 1)

theorem centeredBetaKa_pos {a : ℝ} (ha : 0 < a) :
    0 < centeredBetaKa a := by
  unfold centeredBetaKa
  exact mul_pos
    (mul_pos (by norm_num) (one_div_pos.mpr (beta_pos ha ha)))
    (Real.rpow_pos_of_pos (by norm_num) _)

/-- The real-valued symmetric beta density on its support. -/
theorem betaPDF_same_toReal
    {a : ℝ} (ha : 0 < a) (p : ℝ) :
    (betaPDF a a p).toReal =
      if 0 < p ∧ p < 1 then
        (1 / beta a a) * p ^ (a - 1) * (1 - p) ^ (a - 1)
      else 0 := by
  by_cases hp : 0 < p ∧ p < 1
  · rw [betaPDF, betaPDFReal, if_pos hp, ENNReal.toReal_ofReal]
    exact le_of_lt <| mul_pos
      (mul_pos (one_div_pos.mpr (beta_pos ha ha))
        (Real.rpow_pos_of_pos hp.1 _))
      (Real.rpow_pos_of_pos (sub_pos.mpr hp.2) _)
  · simp [betaPDF, betaPDFReal, hp]

/--
Integration against `Beta(a,a)` is ordinary integration against its
real-power density on `(0,1)`.
-/
theorem integral_betaMeasure_same_eq_interval
    {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    (∫ p, f p ∂betaMeasure a a)
      =
    ∫ p in (0 : ℝ)..1,
      (1 / beta a a) * p ^ (a - 1) * (1 - p) ^ (a - 1) * f p := by
  rw [betaMeasure]
  unfold betaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
      ((measurable_betaPDFReal a a).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  calc
    (∫ p, (betaPDF a a p).toReal * f p)
        =
      ∫ p, (Ioo (0 : ℝ) 1).indicator
        (fun q =>
          (1 / beta a a) * q ^ (a - 1)
            * (1 - q) ^ (a - 1) * f q) p := by
          apply integral_congr_ae
          filter_upwards [] with p
          rw [betaPDF_same_toReal ha p]
          by_cases hp : p ∈ Ioo (0 : ℝ) 1
          · simp only [mem_Ioo] at hp
            simp [hp]
          · have hp' : ¬ (0 < p ∧ p < 1) := by
              simpa only [mem_Ioo] using hp
            simp [hp, hp']
    _ =
      ∫ p in Ioo (0 : ℝ) 1,
        (1 / beta a a) * p ^ (a - 1)
          * (1 - p) ^ (a - 1) * f p :=
      integral_indicator measurableSet_Ioo
    _ =
      ∫ p in Ioc (0 : ℝ) 1,
        (1 / beta a a) * p ^ (a - 1)
          * (1 - p) ^ (a - 1) * f p := by
          apply setIntegral_congr_set
          exact Ioo_ae_eq_Ioc
    _ =
      ∫ p in (0 : ℝ)..1,
        (1 / beta a a) * p ^ (a - 1)
          * (1 - p) ^ (a - 1) * f p := by
          rw [intervalIntegral.integral_of_le (by norm_num)]

private theorem centered_beta_density_algebra
    {a x : ℝ} (f : ℝ → ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    (1 / 2 : ℝ) *
        ((1 / beta a a)
          * (x / 2 + 1 / 2) ^ (a - 1)
          * (1 - (x / 2 + 1 / 2)) ^ (a - 1)
          * f (x / 2 + 1 / 2))
      =
    centeredBetaKa a
      * (f ((1 + x) / 2) * (1 - x ^ 2) ^ (a - 1)) := by
  have hp0 : 0 ≤ x / 2 + 1 / 2 := by linarith [hx.1]
  have hq0 : 0 ≤ 1 - (x / 2 + 1 / 2) := by linarith [hx.2]
  have hbase0 : 0 ≤ 1 - x ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + x)
      (by linarith : 0 ≤ 1 - x)]
  rw [show
      (1 / beta a a)
            * (x / 2 + 1 / 2) ^ (a - 1)
            * (1 - (x / 2 + 1 / 2)) ^ (a - 1)
            * f (x / 2 + 1 / 2)
        =
      (1 / beta a a)
        * ((x / 2 + 1 / 2) ^ (a - 1)
          * (1 - (x / 2 + 1 / 2)) ^ (a - 1))
        * f (x / 2 + 1 / 2) by ring]
  rw [← Real.mul_rpow hp0 hq0]
  rw [show
      (x / 2 + 1 / 2) * (1 - (x / 2 + 1 / 2))
        = (1 / 4 : ℝ) * (1 - x ^ 2) by ring]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) hbase0]
  unfold centeredBetaKa
  have hfarg :
      f (x / 2 + 1 / 2) = f ((1 + x) / 2) := by
    congr 1
    ring
  rw [hfarg]
  ring

/--
The centered-coordinate expectation formula for a symmetric beta law.
-/
theorem integral_betaMeasure_same_eq_centered
    {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    (∫ p, f p ∂betaMeasure a a)
      =
    centeredBetaKa a * ∫ x in (-1 : ℝ)..1,
      f ((1 + x) / 2) * (1 - x ^ 2) ^ (a - 1) := by
  rw [integral_betaMeasure_same_eq_interval ha]
  have hsubst :
      (∫ x in (-1 : ℝ)..1,
        (1 / beta a a)
          * (x / 2 + 1 / 2) ^ (a - 1)
          * (1 - (x / 2 + 1 / 2)) ^ (a - 1)
          * f (x / 2 + 1 / 2))
        =
      2 * ∫ p in (0 : ℝ)..1,
        (1 / beta a a) * p ^ (a - 1)
          * (1 - p) ^ (a - 1) * f p := by
    have h :=
      intervalIntegral.integral_comp_div_add
        (f := fun p : ℝ =>
          (1 / beta a a) * p ^ (a - 1)
            * (1 - p) ^ (a - 1) * f p)
        (a := (-1 : ℝ)) (b := 1) (c := 2) (d := (1 / 2 : ℝ))
        (by norm_num : (2 : ℝ) ≠ 0)
    have hzero : (-1 : ℝ) / 2 + 1 / 2 = 0 := by norm_num
    have hone : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
    rw [hzero, hone] at h
    simpa only [smul_eq_mul] using h
  calc
    (∫ p in (0 : ℝ)..1,
      (1 / beta a a) * p ^ (a - 1)
        * (1 - p) ^ (a - 1) * f p)
        =
      (1 / 2 : ℝ) *
        (2 * ∫ p in (0 : ℝ)..1,
          (1 / beta a a) * p ^ (a - 1)
            * (1 - p) ^ (a - 1) * f p) := by ring
    _ =
      (1 / 2 : ℝ) * ∫ x in (-1 : ℝ)..1,
        (1 / beta a a)
          * (x / 2 + 1 / 2) ^ (a - 1)
          * (1 - (x / 2 + 1 / 2)) ^ (a - 1)
          * f (x / 2 + 1 / 2) := by rw [← hsubst]
    _ =
      centeredBetaKa a * ∫ x in (-1 : ℝ)..1,
        f ((1 + x) / 2) * (1 - x ^ 2) ^ (a - 1) := by
          rw [← intervalIntegral.integral_const_mul,
            ← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro x hx
          simp only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
          exact centered_beta_density_algebra f hx

/-- The centered beta density integrates to one. -/
theorem centeredBetaKa_normalizes
    {a : ℝ} (ha : 0 < a) :
    centeredBetaKa a
        * (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ (a - 1))
      = 1 := by
  letI : IsProbabilityMeasure (betaMeasure a a) :=
    isProbabilityMeasureBeta ha ha
  have h :=
    integral_betaMeasure_same_eq_centered ha (fun _ : ℝ => (1 : ℝ))
  simpa only [integral_const, probReal_univ, one_smul,
    one_mul] using h.symm

/--
Expectation of a measurable test function of a `Beta(a,a)` random variable,
expressed in the centered coordinate.
-/
theorem integral_comp_eq_centered_of_hasLaw_beta_same
    {a : ℝ} (ha : 0 < a)
    (P : Ω → ℝ) (mu : Measure Ω)
    (hP : HasLaw P (betaMeasure a a) mu)
    (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (betaMeasure a a)) :
    (∫ ω, f (P ω) ∂mu)
      =
    centeredBetaKa a * ∫ x in (-1 : ℝ)..1,
      f ((1 + x) / 2) * (1 - x ^ 2) ^ (a - 1) := by
  calc
    (∫ ω, f (P ω) ∂mu)
        = ∫ p, f p ∂betaMeasure a a := by
            simpa only [Function.comp_apply] using hP.integral_comp hf
    _ =
      centeredBetaKa a * ∫ x in (-1 : ℝ)..1,
        f ((1 + x) / 2) * (1 - x ^ 2) ^ (a - 1) :=
      integral_betaMeasure_same_eq_centered ha f

/--
Convenience version of the law-transfer theorem for measurable test
functions.
-/
theorem integral_comp_eq_centered_of_hasLaw_beta_same_of_measurable
    {a : ℝ} (ha : 0 < a)
    (P : Ω → ℝ) (mu : Measure Ω)
    (hP : HasLaw P (betaMeasure a a) mu)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ ω, f (P ω) ∂mu)
      =
    centeredBetaKa a * ∫ x in (-1 : ℝ)..1,
      f ((1 + x) / 2) * (1 - x ^ 2) ^ (a - 1) :=
  integral_comp_eq_centered_of_hasLaw_beta_same
    ha P mu hP f hf.aestronglyMeasurable

end

end GraybillDeal
