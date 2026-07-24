import GraybillDeal.Elementary
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Squared-risk identities

This file lifts the elementary square expansions to Bochner integrals.  The
main theorem isolates the cancellation used in the Graybill--Deal risk
calculation: when the two common cross terms have integral zero, the
difference of risks is the integral of the difference of the two quadratic
terms.
-/

namespace GraybillDeal

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Squared-error risk of a real-valued estimator under a measure `P`. -/
noncomputable def sqRisk (μ : ℝ) (estimator : Ω → ℝ) (P : Measure Ω) : ℝ :=
  ∫ ω, (estimator ω - μ) ^ 2 ∂P

/-- Translating an error by the target parameter does not change that error. -/
theorem sqRisk_add_target (μ : ℝ) (error : Ω → ℝ) (P : Measure Ω) :
    sqRisk μ (fun ω => μ + error ω) P = ∫ ω, (error ω) ^ 2 ∂P := by
  unfold sqRisk
  apply integral_congr_ae
  filter_upwards [] with ω
  ring

/--
Risk decomposition for a centered common term `T` and a weight-dependent
term `D * (a - θ)`.  The assumptions list exactly the three integrable
summands used to distribute the integral.
-/
theorem sqRisk_centered_decomposition
    (μ θ : ℝ) (T D a : Ω → ℝ) (P : Measure Ω)
    (hT_sq : Integrable (fun ω => (T ω) ^ 2) P)
    (hcross : Integrable (fun ω => T ω * D ω * (a ω - θ)) P)
    (hquadratic : Integrable (fun ω => (D ω) ^ 2 * (a ω - θ) ^ 2) P)
    (hcross_zero : ∫ ω, T ω * D ω * (a ω - θ) ∂P = 0) :
    sqRisk μ (fun ω => μ + T ω + D ω * (a ω - θ)) P
      =
        (∫ ω, (T ω) ^ 2 ∂P)
          + ∫ ω, (D ω) ^ 2 * (a ω - θ) ^ 2 ∂P := by
  unfold sqRisk
  calc
    (∫ ω, (μ + T ω + D ω * (a ω - θ) - μ) ^ 2 ∂P)
        =
        ∫ ω,
          (T ω) ^ 2
            + 2 * (T ω * D ω * (a ω - θ))
            + (D ω) ^ 2 * (a ω - θ) ^ 2 ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          ring
    _ =
        (∫ ω,
          (T ω) ^ 2 + 2 * (T ω * D ω * (a ω - θ)) ∂P)
          + ∫ ω, (D ω) ^ 2 * (a ω - θ) ^ 2 ∂P := by
          simpa only [Pi.add_apply] using
            (integral_add (hT_sq.add (hcross.const_mul 2)) hquadratic)
    _ =
        (∫ ω, (T ω) ^ 2 ∂P)
          + (∫ ω, 2 * (T ω * D ω * (a ω - θ)) ∂P)
          + ∫ ω, (D ω) ^ 2 * (a ω - θ) ^ 2 ∂P := by
          have hadd :
              (∫ ω,
                (T ω) ^ 2 + 2 * (T ω * D ω * (a ω - θ)) ∂P)
                =
                (∫ ω, (T ω) ^ 2 ∂P)
                  + ∫ ω, 2 * (T ω * D ω * (a ω - θ)) ∂P := by
            simpa only [Pi.add_apply] using
              (integral_add hT_sq (hcross.const_mul 2))
          rw [hadd]
    _ =
        (∫ ω, (T ω) ^ 2 ∂P)
          + ∫ ω, (D ω) ^ 2 * (a ω - θ) ^ 2 ∂P := by
          rw [integral_const_mul, hcross_zero]
          ring

/--
Integral-level risk-difference identity for two weights.

The estimators are written as
`μ + T + D * (w - θ)` and `μ + T + D * (r - θ)`.  If both cross terms
with the common centered error `T` integrate to zero, their risks differ
only through the two quadratic terms.
-/
theorem sqRisk_weight_difference
    (μ θ : ℝ) (T D w r : Ω → ℝ) (P : Measure Ω)
    (hT_sq : Integrable (fun ω => (T ω) ^ 2) P)
    (hcross_w : Integrable (fun ω => T ω * D ω * (w ω - θ)) P)
    (hcross_r : Integrable (fun ω => T ω * D ω * (r ω - θ)) P)
    (hquadratic_w : Integrable (fun ω => (D ω) ^ 2 * (w ω - θ) ^ 2) P)
    (hquadratic_r : Integrable (fun ω => (D ω) ^ 2 * (r ω - θ) ^ 2) P)
    (hcross_w_zero : ∫ ω, T ω * D ω * (w ω - θ) ∂P = 0)
    (hcross_r_zero : ∫ ω, T ω * D ω * (r ω - θ) ∂P = 0) :
    sqRisk μ (fun ω => μ + T ω + D ω * (w ω - θ)) P
        - sqRisk μ (fun ω => μ + T ω + D ω * (r ω - θ)) P
      =
        ∫ ω,
          (D ω) ^ 2
            * ((w ω - θ) ^ 2 - (r ω - θ) ^ 2) ∂P := by
  rw [sqRisk_centered_decomposition μ θ T D w P
      hT_sq hcross_w hquadratic_w hcross_w_zero]
  rw [sqRisk_centered_decomposition μ θ T D r P
      hT_sq hcross_r hquadratic_r hcross_r_zero]
  calc
    ((∫ ω, (T ω) ^ 2 ∂P)
          + ∫ ω, (D ω) ^ 2 * (w ω - θ) ^ 2 ∂P)
        - ((∫ ω, (T ω) ^ 2 ∂P)
          + ∫ ω, (D ω) ^ 2 * (r ω - θ) ^ 2 ∂P)
        =
        (∫ ω, (D ω) ^ 2 * (w ω - θ) ^ 2 ∂P)
          - ∫ ω, (D ω) ^ 2 * (r ω - θ) ^ 2 ∂P := by
          ring
    _ =
        ∫ ω,
          (D ω) ^ 2 * (w ω - θ) ^ 2
            - (D ω) ^ 2 * (r ω - θ) ^ 2 ∂P := by
          exact (integral_sub hquadratic_w hquadratic_r).symm
    _ =
        ∫ ω,
          (D ω) ^ 2
            * ((w ω - θ) ^ 2 - (r ω - θ) ^ 2) ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          ring

end GraybillDeal
