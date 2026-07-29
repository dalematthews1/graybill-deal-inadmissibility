import GraybillDeal.GeneralSeriesCoefficients

/-!
# Pointwise quadratic-risk bound at arbitrary sample size

This file generalizes the pointwise half of `Reduced.CgIntegrand13_le`.
The remaining integration step is to evaluate the endpoint suprema of the
two real-power kernels in beta-function form.
-/

namespace GraybillDeal

noncomputable section

def generalQuadraticMiddleCoefficient (ν : ℝ) : ℝ :=
  3 * ν / (2 * (ν - 1))

def generalQuadraticTopCoefficient (ν : ℝ) : ℝ :=
  15 * ν ^ 2 / (16 * (ν - 1) * (ν - 2))

def generalQuadraticWeight (ν x : ℝ) : ℝ :=
  (1 - x ^ 2) ^ (ν / 2 + 1)

def generalQuadraticKernel4 (ν s x : ℝ) : ℝ :=
  generalQuadraticWeight ν x / (1 + s * x) ^ 4

def generalQuadraticKernel6 (ν s x : ℝ) : ℝ :=
  generalQuadraticWeight ν x / (1 + s * x) ^ 6

/-- The exact centered-coordinate integrand from the general form of (6). -/
def generalCgIntegrand (ν s x : ℝ) : ℝ :=
  generalQuadraticWeight ν x * (s + x) ^ 2 / (1 + s * x) ^ 6
    - generalQuadraticMiddleCoefficient ν
        * (generalQuadraticWeight ν x * (s + x) ^ 2)
          / (1 + s * x) ^ 7
    + generalQuadraticTopCoefficient ν
        * (generalQuadraticWeight ν x * (s + x) ^ 2)
          / (1 + s * x) ^ 8

theorem generalQuadraticMiddleCoefficient_pos
    {ν : ℝ} (hν : 9 ≤ ν) :
    0 < generalQuadraticMiddleCoefficient ν := by
  unfold generalQuadraticMiddleCoefficient
  have hνpos : 0 < ν := by linarith
  have hden : 0 < ν - 1 := by linarith
  exact div_pos (mul_pos (by norm_num) hνpos)
    (mul_pos (by norm_num) hden)

theorem generalQuadraticTopCoefficient_pos
    {ν : ℝ} (hν : 9 ≤ ν) :
    0 < generalQuadraticTopCoefficient ν := by
  unfold generalQuadraticTopCoefficient
  have h1 : 0 < ν - 1 := by linarith
  have h2 : 0 < ν - 2 := by linarith
  positivity

/--
Discarding the negative middle term and using
`(s+x)² ≤ (1+s*x)²` leaves the two endpoint kernels.
-/
theorem generalCgIntegrand_le
    {ν s x : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) (hx : |x| ≤ 1) :
    generalCgIntegrand ν s x
      ≤ generalQuadraticKernel4 ν s x
        + generalQuadraticTopCoefficient ν
          * generalQuadraticKernel6 ν s x := by
  have hden : 0 < 1 + s * x := one_add_sx_pos hs hx
  have hbase : 0 ≤ 1 - x ^ 2 := by
    rcases abs_le.mp hx with ⟨hxl, hxu⟩
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + x)
      (by linarith : 0 ≤ 1 - x)]
  have hweight : 0 ≤ generalQuadraticWeight ν x := by
    unfold generalQuadraticWeight
    exact Real.rpow_nonneg hbase _
  have hsq : (s + x) ^ 2 ≤ (1 + s * x) ^ 2 :=
    sq_add_le_sq_one_add_mul (le_of_lt hs) hx
  have hfirst :
      generalQuadraticWeight ν x * (s + x) ^ 2
          / (1 + s * x) ^ 6
        ≤ generalQuadraticKernel4 ν s x := by
    unfold generalQuadraticKernel4
    calc
      generalQuadraticWeight ν x * (s + x) ^ 2
            / (1 + s * x) ^ 6
          ≤
        generalQuadraticWeight ν x * (1 + s * x) ^ 2
            / (1 + s * x) ^ 6 := by
              apply div_le_div_of_nonneg_right
              · exact mul_le_mul_of_nonneg_left hsq hweight
              · exact pow_nonneg (le_of_lt hden) 6
      _ = generalQuadraticWeight ν x / (1 + s * x) ^ 4 := by
        field_simp [ne_of_gt hden]
  have hthird :
      generalQuadraticWeight ν x * (s + x) ^ 2
          / (1 + s * x) ^ 8
        ≤ generalQuadraticKernel6 ν s x := by
    unfold generalQuadraticKernel6
    calc
      generalQuadraticWeight ν x * (s + x) ^ 2
            / (1 + s * x) ^ 8
          ≤
        generalQuadraticWeight ν x * (1 + s * x) ^ 2
            / (1 + s * x) ^ 8 := by
              apply div_le_div_of_nonneg_right
              · exact mul_le_mul_of_nonneg_left hsq hweight
              · exact pow_nonneg (le_of_lt hden) 8
      _ = generalQuadraticWeight ν x / (1 + s * x) ^ 6 := by
        field_simp [ne_of_gt hden]
  have hmiddle :
      0 ≤ generalQuadraticMiddleCoefficient ν
          * (generalQuadraticWeight ν x * (s + x) ^ 2)
            / (1 + s * x) ^ 7 := by
    have hm := le_of_lt (generalQuadraticMiddleCoefficient_pos hν)
    positivity
  unfold generalCgIntegrand
  calc
    generalQuadraticWeight ν x * (s + x) ^ 2 / (1 + s * x) ^ 6
          - generalQuadraticMiddleCoefficient ν
              * (generalQuadraticWeight ν x * (s + x) ^ 2)
                / (1 + s * x) ^ 7
          + generalQuadraticTopCoefficient ν
              * (generalQuadraticWeight ν x * (s + x) ^ 2)
                / (1 + s * x) ^ 8
        ≤
      generalQuadraticWeight ν x * (s + x) ^ 2 / (1 + s * x) ^ 6
          + generalQuadraticTopCoefficient ν
              * (generalQuadraticWeight ν x * (s + x) ^ 2)
                / (1 + s * x) ^ 8 := by
            linarith
    _ ≤
      generalQuadraticKernel4 ν s x
        + generalQuadraticTopCoefficient ν
          * generalQuadraticKernel6 ν s x := by
      apply add_le_add hfirst
      calc
        generalQuadraticTopCoefficient ν
              * (generalQuadraticWeight ν x * (s + x) ^ 2)
                / (1 + s * x) ^ 8
            =
          generalQuadraticTopCoefficient ν
            * (generalQuadraticWeight ν x * (s + x) ^ 2
                / (1 + s * x) ^ 8) := by ring
        _ ≤
          generalQuadraticTopCoefficient ν
            * generalQuadraticKernel6 ν s x :=
          mul_le_mul_of_nonneg_left hthird
            (le_of_lt (generalQuadraticTopCoefficient_pos hν))

end

end GraybillDeal
