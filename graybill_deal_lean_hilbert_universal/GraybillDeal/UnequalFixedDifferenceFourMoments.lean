import GraybillDeal.UnequalFixedDifferenceFourSeriesSign
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Probability.Distributions.Beta

/-!
# Beta moments for the fixed-difference-four family

This file supplies the probability-integral foundation for the family

`(n₁, n₂) = (2m - 1, 2m + 3)`, `m ≥ 7`.

The two one-sided beta laws are `Beta(m+1,m-1)` and `Beta(m-1,m+1)`.
We first prove a reusable asymmetric beta-density bridge and a real-power
moment identity.  We then identify the ordinary monomial moments with the
finite products already used in
`UnequalFixedDifferenceFourSeriesSign`.
-/

namespace GraybillDeal

open MeasureTheory Set ProbabilityTheory Real

noncomputable section

/-! ## A reusable asymmetric beta-density bridge -/

/-- Real form of the beta density when both shape parameters are positive. -/
theorem betaPDF_toReal_of_shapes_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : ℝ) :
    (betaPDF a b p).toReal =
      if 0 < p ∧ p < 1 then
        (1 / beta a b) * p ^ (a - 1) * (1 - p) ^ (b - 1)
      else 0 := by
  by_cases hp : 0 < p ∧ p < 1
  · rw [betaPDF, betaPDFReal, if_pos hp, ENNReal.toReal_ofReal]
    exact le_of_lt <| mul_pos
      (mul_pos (one_div_pos.mpr (beta_pos ha hb))
        (Real.rpow_pos_of_pos hp.1 _))
      (Real.rpow_pos_of_pos (sub_pos.mpr hp.2) _)
  · simp [betaPDF, betaPDFReal, hp]

/--
Integration against an asymmetric beta law is ordinary interval integration
against its normalized real-power density.
-/
theorem integral_betaMeasure_eq_interval_of_shapes_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (f : ℝ → ℝ) :
    (∫ p, f p ∂betaMeasure a b)
      =
    ∫ p in (0 : ℝ)..1,
      (1 / beta a b) * p ^ (a - 1) * (1 - p) ^ (b - 1) * f p := by
  rw [betaMeasure]
  unfold betaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
      ((measurable_betaPDFReal a b).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  calc
    (∫ p, (betaPDF a b p).toReal * f p)
        =
      ∫ p, (Ioo (0 : ℝ) 1).indicator
        (fun q =>
          (1 / beta a b) * q ^ (a - 1)
            * (1 - q) ^ (b - 1) * f q) p := by
          apply integral_congr_ae
          filter_upwards [] with p
          rw [betaPDF_toReal_of_shapes_pos ha hb p]
          by_cases hp : p ∈ Ioo (0 : ℝ) 1
          · simp only [mem_Ioo] at hp
            simp [hp]
          · have hp' : ¬ (0 < p ∧ p < 1) := by
              simpa only [mem_Ioo] using hp
            simp [hp, hp']
    _ =
      ∫ p in Ioo (0 : ℝ) 1,
        (1 / beta a b) * p ^ (a - 1)
          * (1 - p) ^ (b - 1) * f p :=
      integral_indicator measurableSet_Ioo
    _ =
      ∫ p in Ioc (0 : ℝ) 1,
        (1 / beta a b) * p ^ (a - 1)
          * (1 - p) ^ (b - 1) * f p := by
          apply setIntegral_congr_set
          exact Ioo_ae_eq_Ioc
    _ =
      ∫ p in (0 : ℝ)..1,
        (1 / beta a b) * p ^ (a - 1)
          * (1 - p) ^ (b - 1) * f p := by
          rw [intervalIntegral.integral_of_le (by norm_num)]

/-- Euler's beta integral in real-power interval-integral form. -/
theorem intervalIntegral_rpow_mul_one_sub_rpow_eq_beta
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ p in (0 : ℝ)..1, p ^ (a - 1) * (1 - p) ^ (b - 1))
      = beta a b := by
  have hcomplex :
      Complex.betaIntegral (a : ℂ) (b : ℂ)
        =
      ((∫ p in (0 : ℝ)..1,
        p ^ (a - 1) * (1 - p) ^ (b - 1) : ℝ) : ℂ) := by
    unfold Complex.betaIntegral
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with p hp
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hp
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hp.1.le,
      Complex.ofReal_cpow (sub_nonneg.mpr hp.2)]
    push_cast
    rfl
  calc
    (∫ p in (0 : ℝ)..1, p ^ (a - 1) * (1 - p) ^ (b - 1))
        =
      (((∫ p in (0 : ℝ)..1,
        p ^ (a - 1) * (1 - p) ^ (b - 1) : ℝ) : ℂ)).re := by simp
    _ = (Complex.betaIntegral (a : ℂ) (b : ℂ)).re := by rw [hcomplex]
    _ = beta a b := (beta_eq_betaIntegralReal a b ha hb).symm

/--
The general real-power moment of an asymmetric beta law.

This deliberately permits negative `u` or `v`, provided the shifted beta
shapes remain positive.  It therefore also supports the inverse moments
needed by the quadratic-envelope calculation.
-/
theorem integral_rpow_mul_one_sub_rpow_betaMeasure_eq_beta_ratio
    {a b u v : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hau : 0 < a + u) (hbv : 0 < b + v) :
    (∫ p, p ^ u * (1 - p) ^ v ∂betaMeasure a b)
      = beta (a + u) (b + v) / beta a b := by
  rw [integral_betaMeasure_eq_interval_of_shapes_pos ha hb]
  calc
    (∫ p in (0 : ℝ)..1,
      (1 / beta a b) * p ^ (a - 1) * (1 - p) ^ (b - 1)
        * (p ^ u * (1 - p) ^ v))
        =
      (1 / beta a b) *
        ∫ p in (0 : ℝ)..1,
          p ^ (a + u - 1) * (1 - p) ^ (b + v - 1) := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr_ae
            filter_upwards [volume.ae_ne (1 : ℝ)] with p hpne hp
            rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hp
            have hp0 : 0 < p := hp.1
            have hp1 : p < 1 := lt_of_le_of_ne hp.2 hpne
            have hq0 : 0 < 1 - p := sub_pos.mpr hp1
            have hpPow :
                p ^ (a - 1) * p ^ u = p ^ (a + u - 1) := by
              rw [← Real.rpow_add hp0]
              congr 1
              ring
            have hqPow :
                (1 - p) ^ (b - 1) * (1 - p) ^ v
                  = (1 - p) ^ (b + v - 1) := by
              rw [← Real.rpow_add hq0]
              congr 1
              ring
            rw [← hpPow, ← hqPow]
            ring
    _ =
      (1 / beta a b) * beta (a + u) (b + v) := by
        rw [intervalIntegral_rpow_mul_one_sub_rpow_eq_beta hau hbv]
    _ = beta (a + u) (b + v) / beta a b := by ring

/-- Ordinary `n`th beta moment as a beta-function ratio. -/
theorem integral_pow_betaMeasure_eq_beta_ratio
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (∫ p, p ^ n ∂betaMeasure a b)
      = beta (a + n) b / beta a b := by
  have h :=
    integral_rpow_mul_one_sub_rpow_betaMeasure_eq_beta_ratio
      (a := a) (b := b) (u := (n : ℝ)) (v := 0)
      ha hb (by positivity) (by simpa using hb)
  simpa only [Real.rpow_natCast, Real.rpow_zero, mul_one, add_zero] using h

/-! ## Beta ratios as finite products -/

/-- One-step recurrence of Euler's beta function in its first argument. -/
theorem beta_add_one_left
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    beta (a + 1) b = (a / (a + b)) * beta a b := by
  have hab : 0 < a + b := add_pos ha hb
  have hGamma : Gamma (a + b) ≠ 0 := (Gamma_pos_of_pos hab).ne'
  unfold beta
  rw [Real.Gamma_add_one ha.ne']
  rw [show a + 1 + b = (a + b) + 1 by ring,
    Real.Gamma_add_one hab.ne']
  field_simp [hab.ne', hGamma]

/-- The beta-function ratio is the rising-factorial moment product. -/
theorem beta_ratio_eq_finset_prod
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ n : ℕ,
      beta (a + n) b / beta a b
        =
      ∏ i ∈ Finset.range n,
        (a + (i : ℝ)) / (a + b + (i : ℝ))
  | 0 => by
      have hbeta : beta a b ≠ 0 := (beta_pos ha hb).ne'
      simp [hbeta]
  | n + 1 => by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have han : 0 < a + (n : ℝ) := by linarith
      have habn : 0 < a + b + (n : ℝ) := by linarith
      rw [show (n + 1 : ℕ) = n + 1 by rfl]
      rw [show a + ((n + 1 : ℕ) : ℝ) = (a + (n : ℝ)) + 1 by
        norm_num
        ring]
      rw [beta_add_one_left han hb, Finset.prod_range_succ]
      calc
        (a + (n : ℝ)) / (a + (n : ℝ) + b)
              * beta (a + (n : ℝ)) b / beta a b
            =
          (beta (a + (n : ℝ)) b / beta a b)
            * ((a + (n : ℝ)) / (a + b + (n : ℝ))) := by ring
        _ =
          (∏ i ∈ Finset.range n,
              (a + (i : ℝ)) / (a + b + (i : ℝ)))
            * ((a + (n : ℝ)) / (a + b + (n : ℝ))) := by
              rw [beta_ratio_eq_finset_prod ha hb n]

/-! ## The two fixed-difference-four moment identifications -/

/--
Moment of the right-chart `Beta(m+1,m-1)` law, identified with the finite
product used by the plus coefficient sequence.
-/
theorem integral_pow_betaMeasure_unequalFixedDifferenceFourPlus
    {m : ℕ} (hm : 7 ≤ m) (n : ℕ) :
    (∫ y, y ^ n
      ∂betaMeasure ((m : ℝ) + 1) ((m : ℝ) - 1))
      = unequalFixedDifferenceFourPlusMoment m n := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have ha : 0 < (m : ℝ) + 1 := by linarith
  have hb : 0 < (m : ℝ) - 1 := by linarith
  rw [integral_pow_betaMeasure_eq_beta_ratio ha hb n]
  rw [beta_ratio_eq_finset_prod ha hb n]
  unfold unequalFixedDifferenceFourPlusMoment
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  ring

/--
Moment of the left-chart `Beta(m-1,m+1)` law, identified with the finite
product used by the minus coefficient sequence.
-/
theorem integral_pow_betaMeasure_unequalFixedDifferenceFourMinus
    {m : ℕ} (hm : 7 ≤ m) (n : ℕ) :
    (∫ y, y ^ n
      ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
      = unequalFixedDifferenceFourMinusMoment m n := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have ha : 0 < (m : ℝ) - 1 := by linarith
  have hb : 0 < (m : ℝ) + 1 := by linarith
  rw [integral_pow_betaMeasure_eq_beta_ratio ha hb n]
  rw [beta_ratio_eq_finset_prod ha hb n]
  unfold unequalFixedDifferenceFourMinusMoment
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  ring

end

end GraybillDeal
