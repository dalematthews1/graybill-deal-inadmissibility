import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Moments of Mathlib's gamma distribution

Mathlib defines the gamma probability measure but currently provides no
moment formula.  This file proves the Mellin-moment identity needed for the
Graybill--Deal probability bridge.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace GraybillDeal

noncomputable section

theorem integral_rpow_gammaMeasure {a r q : ℝ}
    (ha : 0 < a) (hr : 0 < r) (haq : 0 < a + q) :
    (∫ x : ℝ, x ^ q ∂gammaMeasure a r)
      = (1 / r) ^ (a + q) * Gamma (a + q)
          * (r ^ a / Gamma a) := by
  rw [gammaMeasure]
  unfold gammaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
      (measurable_gammaPDFReal a r).ennreal_ofReal
      (by simp)]
  simp_rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _),
    smul_eq_mul]
  calc
    (∫ x : ℝ, gammaPDFReal a r x * x ^ q)
        =
      ∫ x : ℝ in Ioi 0,
        (r ^ a / Gamma a) * (x ^ (a + q - 1) * exp (-(r * x))) := by
          rw [← integral_indicator measurableSet_Ioi]
          apply integral_congr_ae
          filter_upwards [volume.ae_ne 0] with x hx
          by_cases hxpos : 0 < x
          · simp only [Set.indicator, mem_Ioi, hxpos, ↓reduceIte,
              gammaPDFReal, if_pos hxpos.le]
            rw [show a + q - 1 = (a - 1) + q by ring]
            rw [Real.rpow_add hxpos]
            ring
          · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx
            have hxnonneg : ¬0 ≤ x := not_le.mpr hxneg
            simp [Set.indicator, hxpos, gammaPDFReal, hxnonneg]
    _ =
      (r ^ a / Gamma a)
        * (∫ x : ℝ in Ioi 0, x ^ (a + q - 1) * exp (-(r * x))) := by
          rw [MeasureTheory.integral_const_mul]
    _ = (1 / r) ^ (a + q) * Gamma (a + q)
          * (r ^ a / Gamma a) := by
      rw [integral_rpow_mul_exp_neg_mul_Ioi haq hr]
      ring

/--
Every Mellin moment in the natural range `a + q > 0` is integrable.

The preceding formula gives the Bochner integral as a strictly positive
number.  Since Mathlib defines the Bochner integral of a non-integrable
function to be zero, non-vanishing also supplies the integrability fact.
-/
theorem integrable_rpow_gammaMeasure {a r q : ℝ}
    (ha : 0 < a) (hr : 0 < r) (haq : 0 < a + q) :
    Integrable (fun x : ℝ => x ^ q) (gammaMeasure a r) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_rpow_gammaMeasure ha hr haq]
  have hrate : 0 < (1 / r) ^ (a + q) := Real.rpow_pos_of_pos (one_div_pos.mpr hr) _
  have hgammaAq : 0 < Gamma (a + q) := Gamma_pos_of_pos haq
  have hgammaA : 0 < Gamma a := Gamma_pos_of_pos ha
  have hrpow : 0 < r ^ a := Real.rpow_pos_of_pos hr _
  positivity

/-- The gamma Mellin moment in its usual `Γ(a+q)/(Γ(a) r^q)` form. -/
theorem integral_rpow_gammaMeasure_eq {a r q : ℝ}
    (ha : 0 < a) (hr : 0 < r) (haq : 0 < a + q) :
    (∫ x : ℝ, x ^ q ∂gammaMeasure a r)
      = (1 / r) ^ q * Gamma (a + q) / Gamma a := by
  rw [integral_rpow_gammaMeasure ha hr haq]
  rw [Real.rpow_add (one_div_pos.mpr hr)]
  have hcancel : (1 / r) ^ a * r ^ a = 1 := by
    rw [← Real.mul_rpow (one_div_nonneg.mpr hr.le) hr.le,
      one_div_mul_cancel hr.ne', one_rpow]
  calc
    ((1 / r) ^ a * (1 / r) ^ q) * Gamma (a + q)
          * (r ^ a / Gamma a)
        =
      ((1 / r) ^ a * r ^ a)
        * ((1 / r) ^ q * Gamma (a + q) / Gamma a) := by ring
    _ = (1 / r) ^ q * Gamma (a + q) / Gamma a := by rw [hcancel, one_mul]

/-- The first inverse moment of a chi-square variable with 24 degrees of freedom. -/
theorem integral_inv_gammaMeasure_twelve_half :
    (∫ x : ℝ, x⁻¹ ∂gammaMeasure 12 (1 / 2)) = 1 / 22 := by
  calc
    (∫ x : ℝ, x⁻¹ ∂gammaMeasure 12 (1 / 2))
        = ∫ x : ℝ, x ^ (-1 : ℝ) ∂gammaMeasure 12 (1 / 2) := by
            congr 1 with x
            rw [Real.rpow_neg_one]
    _ = (1 / (1 / 2 : ℝ)) ^ (12 - 1 : ℝ) * Gamma (12 - 1)
          * ((1 / 2 : ℝ) ^ 12 / Gamma 12) :=
      integral_rpow_gammaMeasure (by norm_num) (by norm_num) (by norm_num)
    _ = 1 / 22 := by norm_num [Real.rpow_natCast]

/-- The second inverse moment of a chi-square variable with 24 degrees of freedom. -/
theorem integral_inv_sq_gammaMeasure_twelve_half :
    (∫ x : ℝ, (x ^ 2)⁻¹ ∂gammaMeasure 12 (1 / 2)) = 1 / 440 := by
  have h :=
    integral_rpow_gammaMeasure
      (a := (12 : ℝ)) (r := (1 / 2 : ℝ)) (q := (-2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  rw [show (fun x : ℝ => (x ^ 2)⁻¹) = fun x => x ^ (-2 : ℝ) by
    funext x
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_two]
    simp only [inv_pow]]
  rw [h]
  norm_num [Real.rpow_natCast]

/-- First moment of `Gamma(1/2, 1/2)`, equivalently `χ²₁`. -/
theorem integral_id_gammaMeasure_half_half :
    (∫ x : ℝ, x ∂gammaMeasure (1 / 2) (1 / 2)) = 1 := by
  calc
    (∫ x : ℝ, x ∂gammaMeasure (1 / 2) (1 / 2))
        = ∫ x : ℝ, x ^ (1 : ℝ) ∂gammaMeasure (1 / 2) (1 / 2) := by
            congr 1 with x
            rw [Real.rpow_one]
    _ = (1 / (1 / 2 : ℝ)) ^ (1 : ℝ)
          * Gamma ((1 / 2 : ℝ) + 1) / Gamma (1 / 2) :=
      integral_rpow_gammaMeasure_eq (by norm_num) (by norm_num) (by norm_num)
    _ = 1 := by
      rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)]
      field_simp [Real.Gamma_pos_of_pos (by norm_num : 0 < (1 / 2 : ℝ))]
      norm_num [Real.rpow_one]

/-- Second moment of `Gamma(1/2, 1/2)`, equivalently `χ²₁`. -/
theorem integral_sq_gammaMeasure_half_half :
    (∫ x : ℝ, x ^ 2 ∂gammaMeasure (1 / 2) (1 / 2)) = 3 := by
  calc
    (∫ x : ℝ, x ^ 2 ∂gammaMeasure (1 / 2) (1 / 2))
        = ∫ x : ℝ, x ^ (2 : ℝ) ∂gammaMeasure (1 / 2) (1 / 2) := by
            congr 1 with x
            rw [Real.rpow_two]
    _ = (1 / (1 / 2 : ℝ)) ^ (2 : ℝ)
          * Gamma ((1 / 2 : ℝ) + 2) / Gamma (1 / 2) :=
      integral_rpow_gammaMeasure_eq (by norm_num) (by norm_num) (by norm_num)
    _ = 3 := by
      rw [show (1 / 2 : ℝ) + 2 = ((1 / 2 : ℝ) + 1) + 1 by ring]
      rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) + 1 ≠ 0)]
      rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)]
      field_simp [Real.Gamma_pos_of_pos (by norm_num : 0 < (1 / 2 : ℝ))]
      norm_num [Real.rpow_two]

/-- Third moment of `Gamma(1/2, 1/2)`, equivalently `χ²₁`. -/
theorem integral_cube_gammaMeasure_half_half :
    (∫ x : ℝ, x ^ 3 ∂gammaMeasure (1 / 2) (1 / 2)) = 15 := by
  calc
    (∫ x : ℝ, x ^ 3 ∂gammaMeasure (1 / 2) (1 / 2))
        = ∫ x : ℝ, x ^ (3 : ℝ) ∂gammaMeasure (1 / 2) (1 / 2) := by
            congr 1 with x
            norm_num [Real.rpow_natCast]
    _ = (1 / (1 / 2 : ℝ)) ^ (3 : ℝ)
          * Gamma ((1 / 2 : ℝ) + 3) / Gamma (1 / 2) :=
      integral_rpow_gammaMeasure_eq (by norm_num) (by norm_num) (by norm_num)
    _ = 15 := by
      rw [show (1 / 2 : ℝ) + 3 = (((1 / 2 : ℝ) + 1) + 1) + 1 by ring]
      rw [Real.Gamma_add_one (by norm_num : ((1 / 2 : ℝ) + 1) + 1 ≠ 0)]
      rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) + 1 ≠ 0)]
      rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)]
      field_simp [Real.Gamma_pos_of_pos (by norm_num : 0 < (1 / 2 : ℝ))]
      norm_num [Real.rpow_natCast]

end

end GraybillDeal
