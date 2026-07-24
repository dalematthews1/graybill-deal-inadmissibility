import GraybillDeal.GeneralMoments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Integral realization of the generalized moments

This file identifies the beta-function quantity `generalMoment ν j` with
the real-power integral which occurs in the arbitrary-sample-size analytic
kernel:

`∫ x in 0..1, x^(2j) * (1-x²)^(ν/2)`.

The proof uses the substitution `t = x²`.  It is stated for the natural
range `-2 < ν`; in particular it applies to every residual degree of
freedom `ν ≥ 9`.
-/

namespace GraybillDeal

open MeasureTheory Set ProbabilityTheory Real

noncomputable section

/-- The real-power integrand whose integral is `generalMoment ν j`. -/
def generalMomentIntegrand (ν : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  x ^ (2 * j) * (1 - x ^ 2) ^ (ν / 2)

private theorem integral_rpow_mul_one_sub_rpow_eq_beta
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (b - 1))
      = beta a b := by
  have hcomplex :
      Complex.betaIntegral (a : ℂ) (b : ℂ)
        =
      ((∫ t in (0 : ℝ)..1,
        t ^ (a - 1) * (1 - t) ^ (b - 1) : ℝ) : ℂ) := by
    unfold Complex.betaIntegral
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.1.le,
      Complex.ofReal_cpow (sub_nonneg.mpr ht.2)]
    push_cast
    rfl
  calc
    (∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (b - 1))
        =
      (((∫ t in (0 : ℝ)..1,
        t ^ (a - 1) * (1 - t) ^ (b - 1) : ℝ) : ℂ)).re := by simp
    _ = (Complex.betaIntegral (a : ℂ) (b : ℂ)).re := by rw [hcomplex]
    _ = beta a b := (beta_eq_betaIntegralReal a b ha hb).symm

private theorem square_substitution_integrand
    (j : ℕ) {x : ℝ} (hx : 0 < x) :
    (((x ^ 2) ^ ((j : ℝ) + 1 / 2 - 1)
        * (1 - x ^ 2) ^ ((ν : ℝ) / 2 + 1 - 1)) * (2 * x))
      =
    2 * generalMomentIntegrand ν j x := by
  have hx0 : 0 ≤ x := hx.le
  have hpow :
      (x ^ 2) ^ ((j : ℝ) + 1 / 2 - 1) * x
        = x ^ (2 * j) := by
    calc
      (x ^ 2) ^ ((j : ℝ) + 1 / 2 - 1) * x
          =
        (x ^ (2 : ℝ)) ^ ((j : ℝ) + 1 / 2 - 1) * x := by
          rw [Real.rpow_two]
      _ =
        x ^ ((2 : ℝ) * ((j : ℝ) + 1 / 2 - 1)) * x := by
          rw [← Real.rpow_mul hx0]
      _ =
        x ^ ((2 : ℝ) * ((j : ℝ) + 1 / 2 - 1)) * x ^ (1 : ℝ) := by
          rw [Real.rpow_one]
      _ =
        x ^ ((2 : ℝ) * ((j : ℝ) + 1 / 2 - 1) + 1) := by
          rw [Real.rpow_add hx]
      _ = x ^ (((2 * j : ℕ) : ℝ)) := by
          congr 1
          norm_num
          ring
      _ = x ^ (2 * j) := Real.rpow_natCast x (2 * j)
  unfold generalMomentIntegrand
  rw [show (ν : ℝ) / 2 + 1 - 1 = ν / 2 by ring]
  calc
    (x ^ 2) ^ ((j : ℝ) + 1 / 2 - 1)
          * (1 - x ^ 2) ^ (ν / 2) * (2 * x)
        =
      2 * (((x ^ 2) ^ ((j : ℝ) + 1 / 2 - 1) * x)
        * (1 - x ^ 2) ^ (ν / 2)) := by ring
    _ = 2 * (x ^ (2 * j) * (1 - x ^ 2) ^ (ν / 2)) := by rw [hpow]

/--
The beta-function definition of `generalMoment` equals its real-power
integral representation.
-/
theorem generalMoment_eq_intervalIntegral
    {ν : ℝ} (hν : -2 < ν) (j : ℕ) :
    generalMoment ν j
      =
    ∫ x in (0 : ℝ)..1, generalMomentIntegrand ν j x := by
  have ha : 0 < (j : ℝ) + 1 / 2 := by positivity
  have hb : 0 < ν / 2 + 1 := by linarith
  let g : ℝ → ℝ := fun t =>
    t ^ ((j : ℝ) + 1 / 2 - 1)
      * (1 - t) ^ (ν / 2 + 1 - 1)
  have hsubst :
      (∫ x in (0 : ℝ)..1, (g ∘ fun x : ℝ => x ^ 2) x * (2 * x))
        =
      ∫ t in (0 : ℝ)..1, g t := by
    convert intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := 1)
      (f := fun x : ℝ => x ^ 2) (f' := fun x : ℝ => 2 * x) (g := g)
      (by fun_prop)
      (by
        intro x hx
        have h := hasDerivAt_pow 2 x
        have heq : ((2 : ℕ) : ℝ) * x ^ (2 - 1) = 2 * x := by norm_num
        rw [heq] at h
        exact h)
      (by
        intro x hx
        norm_num at hx
        linarith) using 1
    all_goals norm_num
  have hleft :
      (∫ x in (0 : ℝ)..1, (g ∘ fun x : ℝ => x ^ 2) x * (2 * x))
        =
      2 * ∫ x in (0 : ℝ)..1, generalMomentIntegrand ν j x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    dsimp only [g, Function.comp_apply]
    exact square_substitution_integrand j hx.1
  have hright :
      (∫ t in (0 : ℝ)..1, g t)
        = beta ((j : ℝ) + 1 / 2) (ν / 2 + 1) := by
    dsimp only [g]
    exact integral_rpow_mul_one_sub_rpow_eq_beta ha hb
  unfold generalMoment
  rw [← hright, ← hsubst, hleft]
  ring

/-- The integral identity with the integrand expanded. -/
theorem generalMoment_eq_integral_rpow
    {ν : ℝ} (hν : -2 < ν) (j : ℕ) :
    generalMoment ν j
      =
    ∫ x in (0 : ℝ)..1,
      x ^ (2 * j) * (1 - x ^ 2) ^ (ν / 2) := by
  simpa only [generalMomentIntegrand] using
    generalMoment_eq_intervalIntegral hν j

/-- The generalized moment integrand is nonnegative on `[0,1]`. -/
theorem generalMomentIntegrand_nonneg
    (ν : ℝ) (j : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ generalMomentIntegrand ν j x := by
  unfold generalMomentIntegrand
  apply mul_nonneg
  · exact pow_nonneg hx.1 _
  · apply Real.rpow_nonneg
    have hxmul : 0 ≤ x * (1 - x) :=
      mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
    nlinarith

/-- The generalized moment integrand is strictly positive on `(0,1)`. -/
theorem generalMomentIntegrand_pos
    (ν : ℝ) (j : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < generalMomentIntegrand ν j x := by
  unfold generalMomentIntegrand
  apply mul_pos
  · exact pow_pos hx.1 _
  · apply Real.rpow_pos_of_pos
    have hxmul : 0 < x * (1 - x) :=
      mul_pos hx.1 (sub_pos.mpr hx.2)
    nlinarith

/-- For nonnegative `ν`, the generalized moment integrand is continuous. -/
theorem continuous_generalMomentIntegrand
    {ν : ℝ} (hν : 0 ≤ ν) (j : ℕ) :
    Continuous (generalMomentIntegrand ν j) := by
  unfold generalMomentIntegrand
  exact (continuous_id.pow _).mul
    ((Real.continuous_rpow_const (by linarith : 0 ≤ ν / 2)).comp
      (continuous_const.sub (continuous_id.pow 2)))

/--
For the parameter range used in the general Graybill--Deal argument
(`ν ≥ 9`, hence in particular `ν ≥ 0`), the generalized moment integrand
is interval-integrable.
-/
theorem intervalIntegrable_generalMomentIntegrand
    {ν : ℝ} (hν : 0 ≤ ν) (j : ℕ) :
    IntervalIntegrable (generalMomentIntegrand ν j) volume 0 1 :=
  (continuous_generalMomentIntegrand hν j).intervalIntegrable 0 1

/-- The generalized real-power moment integral is nonnegative. -/
theorem integral_generalMomentIntegrand_nonneg (ν : ℝ) (j : ℕ) :
    0 ≤ ∫ x in (0 : ℝ)..1, generalMomentIntegrand ν j x := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  exact generalMomentIntegrand_nonneg ν j hx

/-- In its convergent range, the generalized real-power moment integral is positive. -/
theorem integral_generalMomentIntegrand_pos
    {ν : ℝ} (hν : -2 < ν) (j : ℕ) :
    0 < ∫ x in (0 : ℝ)..1, generalMomentIntegrand ν j x := by
  rw [← generalMoment_eq_intervalIntegral hν j]
  exact generalMoment_pos hν j

end

end GraybillDeal
