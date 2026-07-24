import GraybillDeal.GeneralCanonical
import GraybillDeal.GeneralBetaBridge

/-!
# Generic canonical integrands and their centered beta forms

After the independent `V,L` coordinates have been integrated out, the
linear and quadratic canonical moments reduce to functions of the beta
coordinate `P`.  This file defines those two functions for arbitrary
residual degrees of freedom `ν`, proves their exact forms under
`x = 2P - 1`, and identifies their centered-beta expectations with
`generalBg` and `generalCg`.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/--
The generic linear `P`-integrand obtained after taking the required
`V,L` moments.
-/
def generalCanonicalLinearPIntegrand
    (ν s pcoord : ℝ) : ℝ :=
  (canonicalR s pcoord - canonicalTheta s)
    * weightPolynomial (canonicalR s pcoord)
    * (1 -
      3 * ν /
        (8 * (ν - 1) * canonicalDenom s pcoord))

/--
The generic quadratic `P`-integrand obtained after taking the required
`V,L` moments.
-/
def generalCanonicalQuadraticPIntegrand
    (ν s pcoord : ℝ) : ℝ :=
  weightPolynomial (canonicalR s pcoord) ^ 2
    * (1 -
      3 * ν /
        (4 * (ν - 1) * canonicalDenom s pcoord)
      + 15 * ν ^ 2 /
        (64 * (ν - 1) * (ν - 2)
          * canonicalDenom s pcoord ^ 2))

/-- The generic canonical direction is exactly `4G`. -/
theorem generalCanonicalH_eq_four_mul_G
    (ν s pcoord l v : ℝ) :
    generalCanonicalH ν s pcoord l v
      =
    4 * canonicalG ν (canonicalTheta s) pcoord l v := rfl

/--
Exact centered-coordinate form of the generic linear `P`-integrand.
-/
theorem generalCanonicalLinearPIntegrand_centered
    {ν s x : ℝ} (hν : 9 ≤ ν)
    (hs : |s| < 1) (hx : |x| ≤ 1) :
    generalCanonicalLinearPIntegrand ν s ((1 + x) / 2)
      =
    -((1 - s ^ 2) ^ 2 / 8)
      * ((1 - x ^ 2) * x * (s + x)
        * (generalAlpha ν + s * x)
        / (1 + s * x) ^ 5) := by
  have hne : 1 + s * x ≠ 0 :=
    ne_of_gt (one_add_sx_pos hs hx)
  have hν1 : ν - 1 ≠ 0 := by linarith
  unfold generalCanonicalLinearPIntegrand
  rw [canonicalR_centered hs hx, canonicalDenom_centered]
  change
    (rSX s x - thetaOfS s) * p (rSX s x)
        * (1 - 3 * ν / (8 * (ν - 1) * dSX s x))
      =
    -((1 - s ^ 2) ^ 2 / 8)
      * ((1 - x ^ 2) * x * (s + x)
        * (generalAlpha ν + s * x)
        / (1 + s * x) ^ 5)
  rw [rSX_sub_thetaOfS hs hx, p_rSX hs hx]
  unfold dSX generalAlpha
  field_simp [hne, hν1]
  ring

/--
Exact centered-coordinate form of the generic quadratic `P`-integrand.
-/
theorem generalCanonicalQuadraticPIntegrand_centered
    {ν s x : ℝ} (hν : 9 ≤ ν)
    (hs : |s| < 1) (hx : |x| ≤ 1) :
    generalCanonicalQuadraticPIntegrand ν s ((1 + x) / 2)
      =
    (1 - s ^ 2) ^ 2 / 16
      * ((1 - x ^ 2) ^ 2 * (s + x) ^ 2
            / (1 + s * x) ^ 6
        - generalQuadraticMiddleCoefficient ν
            * ((1 - x ^ 2) ^ 2 * (s + x) ^ 2)
              / (1 + s * x) ^ 7
        + generalQuadraticTopCoefficient ν
            * ((1 - x ^ 2) ^ 2 * (s + x) ^ 2)
              / (1 + s * x) ^ 8) := by
  have hne : 1 + s * x ≠ 0 :=
    ne_of_gt (one_add_sx_pos hs hx)
  have hν1 : ν - 1 ≠ 0 := by linarith
  have hν2 : ν - 2 ≠ 0 := by linarith
  unfold generalCanonicalQuadraticPIntegrand
  rw [canonicalR_centered hs hx, canonicalDenom_centered]
  change
    p (rSX s x) ^ 2
        * (1 - 3 * ν / (4 * (ν - 1) * dSX s x)
          + 15 * ν ^ 2 /
            (64 * (ν - 1) * (ν - 2) * dSX s x ^ 2))
      =
    (1 - s ^ 2) ^ 2 / 16
      * ((1 - x ^ 2) ^ 2 * (s + x) ^ 2
            / (1 + s * x) ^ 6
        - generalQuadraticMiddleCoefficient ν
            * ((1 - x ^ 2) ^ 2 * (s + x) ^ 2)
              / (1 + s * x) ^ 7
        + generalQuadraticTopCoefficient ν
            * ((1 - x ^ 2) ^ 2 * (s + x) ^ 2)
              / (1 + s * x) ^ 8)
  rw [p_rSX hs hx]
  unfold dSX generalQuadraticMiddleCoefficient
    generalQuadraticTopCoefficient
  field_simp [hne, hν1, hν2]
  ring

private theorem one_sub_sq_mul_centeredBetaWeight
    {ν x : ℝ} (hν : 9 ≤ ν) (hx : |x| ≤ 1) :
    (1 - x ^ 2) * (1 - x ^ 2) ^ (ν / 2 - 1)
      =
    (1 - x ^ 2) ^ (ν / 2) := by
  have hbase : 0 ≤ 1 - x ^ 2 := by
    rcases abs_le.mp hx with ⟨hxl, hxu⟩
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + x)
      (by linarith : 0 ≤ 1 - x)]
  calc
    (1 - x ^ 2) * (1 - x ^ 2) ^ (ν / 2 - 1)
        =
      (1 - x ^ 2) ^ (1 : ℝ)
        * (1 - x ^ 2) ^ (ν / 2 - 1) := by
          rw [Real.rpow_one]
    _ =
      (1 - x ^ 2) ^ ((1 : ℝ) + (ν / 2 - 1)) := by
        rw [Real.rpow_add_of_nonneg hbase (by norm_num)
          (by linarith)]
    _ = (1 - x ^ 2) ^ (ν / 2) := by
      congr 1
      ring

private theorem one_sub_sq_sq_mul_centeredBetaWeight
    {ν x : ℝ} (hν : 9 ≤ ν) (hx : |x| ≤ 1) :
    (1 - x ^ 2) ^ 2 * (1 - x ^ 2) ^ (ν / 2 - 1)
      =
    (1 - x ^ 2) ^ (ν / 2 + 1) := by
  have hbase : 0 ≤ 1 - x ^ 2 := by
    rcases abs_le.mp hx with ⟨hxl, hxu⟩
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + x)
      (by linarith : 0 ≤ 1 - x)]
  calc
    (1 - x ^ 2) ^ 2 * (1 - x ^ 2) ^ (ν / 2 - 1)
        =
      (1 - x ^ 2) ^ (2 : ℝ)
        * (1 - x ^ 2) ^ (ν / 2 - 1) := by
          congr 1
          exact (Real.rpow_natCast (1 - x ^ 2) 2).symm
    _ =
      (1 - x ^ 2) ^ ((2 : ℝ) + (ν / 2 - 1)) := by
        rw [Real.rpow_add_of_nonneg hbase (by norm_num)
          (by linarith)]
    _ = (1 - x ^ 2) ^ (ν / 2 + 1) := by
      congr 1
      ring

/--
The centered-beta integration formula identifies the generic linear
expectation with `generalBg`.
-/
theorem generalCanonicalLinearPExpectation_eq_generalBg
    (Ka ν s : ℝ) (P : Ω → ℝ) (ℙ : Measure Ω)
    (hν : 9 ≤ ν) (hs : |s| < 1)
    (hbeta :
      (∫ ω,
        generalCanonicalLinearPIntegrand ν s (P ω) ∂ℙ)
        =
      Ka * ∫ x in (-1 : ℝ)..1,
        generalCanonicalLinearPIntegrand ν s ((1 + x) / 2)
          * (1 - x ^ 2) ^ (ν / 2 - 1)) :
    (∫ ω, generalCanonicalLinearPIntegrand ν s (P ω) ∂ℙ)
      = generalBg Ka ν s := by
  have hcentered :
      (∫ x in (-1 : ℝ)..1,
        generalCanonicalLinearPIntegrand ν s ((1 + x) / 2)
          * (1 - x ^ 2) ^ (ν / 2 - 1))
        =
      -((1 - s ^ 2) ^ 2 / 8) * generalI ν s := by
    unfold generalI
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    have hxabs : |x| ≤ 1 := by
      rw [abs_le]
      exact hx
    dsimp only
    rw [generalCanonicalLinearPIntegrand_centered hν hs hxabs]
    unfold generalLinearKernel generalLinearCore
    rw [← one_sub_sq_mul_centeredBetaWeight hν hxabs]
    ring
  rw [hbeta, hcentered]
  unfold generalBg
  ring

/--
The centered-beta integration formula identifies the generic quadratic
expectation with `generalCg`.
-/
theorem generalCanonicalQuadraticPExpectation_eq_generalCg
    (Ka ν s : ℝ) (P : Ω → ℝ) (ℙ : Measure Ω)
    (hν : 9 ≤ ν) (hs : |s| < 1)
    (hbeta :
      (∫ ω,
        generalCanonicalQuadraticPIntegrand ν s (P ω) ∂ℙ)
        =
      Ka * ∫ x in (-1 : ℝ)..1,
        generalCanonicalQuadraticPIntegrand ν s ((1 + x) / 2)
          * (1 - x ^ 2) ^ (ν / 2 - 1)) :
    (∫ ω, generalCanonicalQuadraticPIntegrand ν s (P ω) ∂ℙ)
      = generalCg Ka ν s := by
  have hcentered :
      (∫ x in (-1 : ℝ)..1,
        generalCanonicalQuadraticPIntegrand ν s ((1 + x) / 2)
          * (1 - x ^ 2) ^ (ν / 2 - 1))
        =
      (1 - s ^ 2) ^ 2 / 16
        * (∫ x in (-1 : ℝ)..1, generalCgIntegrand ν s x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    have hxabs : |x| ≤ 1 := by
      rw [abs_le]
      exact hx
    dsimp only
    rw [generalCanonicalQuadraticPIntegrand_centered hν hs hxabs]
    unfold generalCgIntegrand generalQuadraticWeight
    rw [← one_sub_sq_sq_mul_centeredBetaWeight hν hxabs]
    ring
  rw [hbeta, hcentered]
  unfold generalCg
  ring

end

end GraybillDeal
