import GraybillDeal.GeneralCollectedBounds
import GraybillDeal.GeneralMomentIntegral

/-!
# Termwise integration of the generalized collected series

The target-indexed generalized summands have a summable uniform majorant on
`[0,1]`.  This file uses that domination to exchange their sum and interval
integral, identifies each integrated term with `generalSeriesTerm`, and
thereby proves that the analytic integral `generalI ν s` is exactly the
certified series `generalSeriesSum ν (s²)`.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

/-- Integration of the generalized moment density recovers its beta moment. -/
theorem integral_generalMomentDensity
    {ν : ℝ} (hν : -2 < ν) (j : ℕ) :
    (∫ x in (0 : ℝ)..1, generalMomentDensity ν j x)
      = generalMoment ν j := by
  simpa only [generalMomentDensity] using
    (generalMoment_eq_integral_rpow hν j).symm

/--
For nonnegative residual degrees of freedom, each generalized moment density
is continuous.
-/
theorem continuous_generalMomentDensity
    {ν : ℝ} (hν : 0 ≤ ν) (j : ℕ) :
    Continuous (generalMomentDensity ν j) := by
  unfold generalMomentDensity
  exact (continuous_id.pow _).mul
    ((Real.continuous_rpow_const (by linarith : 0 ≤ ν / 2)).comp
      (continuous_const.sub (continuous_id.pow 2)))

/--
The integral of the target-indexed collected integrand is the corresponding
term of the certified generalized series.
-/
theorem integral_generalCollectedIntegrand
    {ν : ℝ} (hν : 9 ≤ ν) (s : ℝ) (m : ℕ) :
    (∫ x in (0 : ℝ)..1, generalCollectedIntegrand ν s x m)
      = generalSeriesTerm ν (s ^ 2) m := by
  have hmoment (j : ℕ) :
      IntervalIntegrable (generalMomentDensity ν j) volume 0 1 :=
    (continuous_generalMomentDensity (by linarith) j).intervalIntegrable 0 1
  calc
    (∫ x in (0 : ℝ)..1, generalCollectedIntegrand ν s x m)
        = (s ^ 2) ^ m * generalIntegratedCoefficient ν m := by
      unfold generalCollectedIntegrand generalIntegratedCoefficient
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_add
        ((hmoment m).const_mul (generalCollectedMomentCoeff ν m))
        ((hmoment (m + 1)).const_mul
          (generalCollectedNextCoeff ν m))]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        integral_generalMomentDensity (by linarith),
        integral_generalMomentDensity (by linarith)]
    _ = generalSeriesTerm ν (s ^ 2) m := by
      rw [generalIntegratedCoefficient_eq hν]
      unfold generalSeriesTerm
      ring

/--
The generalized collected pointwise summands may be integrated term by term,
and their integrals sum to the paired analytic integral.
-/
theorem hasSum_integral_generalCollectedPointwiseSummand
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    HasSum
      (fun m =>
        ∫ x in (0 : ℝ)..1,
          generalCollectedPointwiseSummand ν s x m)
      (generalI ν s) := by
  have h :
      HasSum
        (fun m =>
          ∫ x in (0 : ℝ)..1,
            generalCollectedPointwiseSummand ν s x m)
        (∫ x in (0 : ℝ)..1,
          (1 - x ^ 2) ^ (ν / 2) * x ^ 2
            * generalPairedPolynomial ν (s ^ 2) (x ^ 2)
            / (1 - s ^ 2 * x ^ 2) ^ 5) := by
    apply hasSum_intervalIntegral_of_uniform_majorant
      (c := generalCollectedMajorant s)
    · intro m
      have hcontinuous :
          Continuous
            (fun x : ℝ => generalCollectedIntegrand ν s x m) := by
        unfold generalCollectedIntegrand
        exact continuous_const.mul
          ((continuous_const.mul
              (continuous_generalMomentDensity (by linarith) m)).add
            (continuous_const.mul
              (continuous_generalMomentDensity
                (by linarith) (m + 1))))
      rw [show
        (fun x : ℝ => generalCollectedPointwiseSummand ν s x m)
          =
        (fun x : ℝ => generalCollectedIntegrand ν s x m) by
          funext x
          exact
            generalCollectedPointwiseSummand_eq_collectedIntegrand
              ν s x m]
      exact hcontinuous.continuousOn
    · intro m x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le] using hx
      exact generalCollectedPointwiseSummand_norm_le m hν hs hx'
    · exact summable_generalCollectedMajorant hs
    · intro x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le] using hx
      exact hasSum_generalCollectedPointwiseSummand hs hx'
  simpa only [generalI_eq_paired hν hs] using h

/--
The equivalent collected-integrand sequence also sums, after integration, to
`generalI ν s`.
-/
theorem hasSum_integral_generalCollectedIntegrand
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    HasSum
      (fun m =>
        ∫ x in (0 : ℝ)..1, generalCollectedIntegrand ν s x m)
      (generalI ν s) := by
  have h :=
    hasSum_integral_generalCollectedPointwiseSummand hν hs
  convert h using 1
  funext m
  apply intervalIntegral.integral_congr
  intro x hx
  exact
    (generalCollectedPointwiseSummand_eq_collectedIntegrand
      ν s x m).symm

/-- The certified generalized coefficient series has sum `generalI ν s`. -/
theorem hasSum_generalSeriesTerm_sq_eq_generalI
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    HasSum (generalSeriesTerm ν (s ^ 2)) (generalI ν s) := by
  have h := hasSum_integral_generalCollectedIntegrand hν hs
  convert h using 1
  funext m
  exact (integral_generalCollectedIntegrand hν s m).symm

/--
Exact identification of the generalized analytic integral with its certified
coefficient series.
-/
theorem generalI_eq_generalSeriesSum_sq
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    generalI ν s = generalSeriesSum ν (s ^ 2) := by
  exact (hasSum_generalSeriesTerm_sq_eq_generalI hν hs).tsum_eq.symm

end

end GraybillDeal
