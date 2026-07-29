import GraybillDeal.GammaMoments

/-!
# Gamma inverse moments for arbitrary residual degrees of freedom

For equal sample size `n = ν + 1`, the sum of the two standardized residual
sums of squares has law `Gamma(ν, 1 / 2)`.  This file removes the
fixed-`ν = 12` arithmetic from the two inverse moments used in the canonical
risk reduction.
-/

open MeasureTheory ProbabilityTheory Real

namespace GraybillDeal

noncomputable section

/--
The first inverse moment of `Gamma(ν, 1/2)`.

For the Graybill--Deal application, `ν = n - 1`, and the assumption follows
from `n ≥ 10`.
-/
theorem integral_inv_gammaMeasure_half {ν : ℝ} (hν : 1 < ν) :
    (∫ x : ℝ, x⁻¹ ∂gammaMeasure ν (1 / 2))
      = 1 / (2 * (ν - 1)) := by
  have hνpos : 0 < ν := lt_trans (by norm_num) hν
  have hνsub : 0 < ν - 1 := sub_pos.mpr hν
  calc
    (∫ x : ℝ, x⁻¹ ∂gammaMeasure ν (1 / 2))
        = ∫ x : ℝ, x ^ (-1 : ℝ) ∂gammaMeasure ν (1 / 2) := by
            congr 1 with x
            rw [Real.rpow_neg_one]
    _ = (1 / (1 / 2 : ℝ)) ^ (-1 : ℝ)
          * Gamma (ν - 1) / Gamma ν :=
      integral_rpow_gammaMeasure_eq hνpos (by norm_num) hνsub
    _ = 1 / (2 * (ν - 1)) := by
      rw [show ν = (ν - 1) + 1 by ring,
        Real.Gamma_add_one hνsub.ne']
      have hgamma : Gamma (ν - 1) ≠ 0 :=
        (Gamma_pos_of_pos hνsub).ne'
      rw [Real.rpow_neg_one]
      field_simp [hνsub.ne', hgamma]
      ring

/--
The second inverse moment of `Gamma(ν, 1/2)`.
-/
theorem integral_inv_sq_gammaMeasure_half {ν : ℝ} (hν : 2 < ν) :
    (∫ x : ℝ, (x ^ 2)⁻¹ ∂gammaMeasure ν (1 / 2))
      = 1 / (4 * (ν - 1) * (ν - 2)) := by
  have hνpos : 0 < ν := lt_trans (by norm_num) hν
  have hνsubTwo : 0 < ν - 2 := sub_pos.mpr hν
  have hνsubOne : 0 < ν - 1 := by linarith
  have hνsubTwo' : -2 + ν ≠ 0 := by linarith
  rw [show (fun x : ℝ => (x ^ 2)⁻¹) = fun x => x ^ (-2 : ℝ) by
    funext x
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_two]
    simp only [inv_pow]]
  calc
    (∫ x : ℝ, x ^ (-2 : ℝ) ∂gammaMeasure ν (1 / 2))
        = (1 / (1 / 2 : ℝ)) ^ (-2 : ℝ)
            * Gamma (ν - 2) / Gamma ν :=
      integral_rpow_gammaMeasure_eq hνpos (by norm_num) hνsubTwo
    _ = 1 / (4 * (ν - 1) * (ν - 2)) := by
      have hgamma : Gamma (ν - 2) ≠ 0 :=
        (Gamma_pos_of_pos hνsubTwo).ne'
      have hgammaν :
          Gamma ν = (ν - 1) * (ν - 2) * Gamma (ν - 2) := by
        rw [show ν = (ν - 1) + 1 by ring,
          Real.Gamma_add_one hνsubOne.ne',
          show ν - 1 = (ν - 2) + 1 by ring,
          Real.Gamma_add_one hνsubTwo.ne']
        ring
      rw [hgammaν, Real.rpow_neg_eq_inv_rpow, Real.rpow_two]
      norm_num
      field_simp [hνsubOne.ne', hνsubTwo.ne', hνsubTwo', hgamma]

/-- Integrability accompanying the first inverse-moment formula. -/
theorem integrable_inv_gammaMeasure_half {ν : ℝ} (hν : 1 < ν) :
    Integrable (fun x : ℝ => x⁻¹) (gammaMeasure ν (1 / 2)) := by
  have hνpos : 0 < ν := lt_trans (by norm_num) hν
  have hνsub : 0 < ν - 1 := sub_pos.mpr hν
  simpa only [Real.rpow_neg_one] using
    (integrable_rpow_gammaMeasure
      (a := ν) (r := (1 / 2 : ℝ)) (q := (-1 : ℝ))
      hνpos (by norm_num) hνsub)

/-- Integrability accompanying the second inverse-moment formula. -/
theorem integrable_inv_sq_gammaMeasure_half {ν : ℝ} (hν : 2 < ν) :
    Integrable (fun x : ℝ => (x ^ 2)⁻¹)
      (gammaMeasure ν (1 / 2)) := by
  have hνpos : 0 < ν := lt_trans (by norm_num) hν
  have hνsub : 0 < ν - 2 := sub_pos.mpr hν
  convert
    (integrable_rpow_gammaMeasure
      (a := ν) (r := (1 / 2 : ℝ)) (q := (-2 : ℝ))
      hνpos (by norm_num) hνsub) using 1
  funext x
  rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_two]
  simp only [inv_pow]

end

end GraybillDeal
