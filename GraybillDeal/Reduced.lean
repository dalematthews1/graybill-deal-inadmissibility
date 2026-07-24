import GraybillDeal.CollectedIntegration
import GraybillDeal.QuadraticBounds
import GraybillDeal.Algebra

/-!
# The reduced `n = 13` risk certificate

This file packages the analytic estimates into the reduced quantities from
equations (5)--(7) and (12) of the counterexample note.  The positive
constant `Ka` is the normalizing constant of the centered beta density.

For `h = 4g`, the quantities in the risk difference are
`Btheta13 = 4 Bg13` and `Ctheta13 = 16 Cg13`.  The final theorem proves the
strict risk inequality directly at `ε = 1 / 2000`; in particular, it does
not divide by `Ctheta13`.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

/--
The exact reduced linear term from equation (7):

`Bg = -Ka (1-s²)² I(s) / 8`.
-/
def Bg13 (Ka s : ℝ) : ℝ :=
  -(Ka * (1 - s ^ 2) ^ 2 / 8) * I13 s

/--
The exact centered-coordinate integrand obtained from equation (6) at
`ν = 12` and `a = 6`.

The three coefficients in braces become
`1`, `-18 / (11(1+sx))`, and `27 / (22(1+sx)²)`.
-/
def CgIntegrand13 (s x : ℝ) : ℝ :=
  (1 - x ^ 2) ^ 7 * (s + x) ^ 2 / (1 + s * x) ^ 6
    - (18 / 11) * ((1 - x ^ 2) ^ 7 * (s + x) ^ 2)
        / (1 + s * x) ^ 7
    + (27 / 22) * ((1 - x ^ 2) ^ 7 * (s + x) ^ 2)
        / (1 + s * x) ^ 8

/--
The exact reduced quadratic term from equation (6), after the centered beta
change of variables.
-/
def Cg13 (Ka s : ℝ) : ℝ :=
  Ka * (1 - s ^ 2) ^ 2 / 16
    * (∫ x in (-1 : ℝ)..1, CgIntegrand13 s x)

/-- The linear risk coefficient for `h = 4g`. -/
def Btheta13 (Ka s : ℝ) : ℝ :=
  4 * Bg13 Ka s

/-- The quadratic risk coefficient for `h = 4g`. -/
def Ctheta13 (Ka s : ℝ) : ℝ :=
  16 * Cg13 Ka s

/-- The fixed perturbation size proposed in the counterexample. -/
def epsilon13 : ℝ := 1 / 2000

private theorem CgIntegrand13_continuousOn {s : ℝ} (hs : |s| < 1) :
    ContinuousOn (CgIntegrand13 s) (Icc (-1) 1) := by
  have hden :
      ∀ x ∈ Icc (-1 : ℝ) 1, 1 + s * x ≠ 0 := by
    intro x hx
    apply ne_of_gt
    apply one_add_sx_pos hs
    rw [abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hnum :
      Continuous
        (fun x : ℝ => (1 - x ^ 2) ^ 7 * (s + x) ^ 2) := by
    fun_prop
  have hbase :
      Continuous (fun x : ℝ => 1 + s * x) := by
    fun_prop
  unfold CgIntegrand13
  exact
    ((hnum.continuousOn.div (hbase.pow 6).continuousOn
        (fun x hx => pow_ne_zero 6 (hden x hx))).sub
      ((continuous_const.mul hnum).continuousOn.div
        (hbase.pow 7).continuousOn
        (fun x hx => pow_ne_zero 7 (hden x hx)))).add
      ((continuous_const.mul hnum).continuousOn.div
        (hbase.pow 8).continuousOn
        (fun x hx => pow_ne_zero 8 (hden x hx)))

private theorem quadraticKernel4_intervalIntegrable {s : ℝ}
    (hs : |s| < 1) :
    IntervalIntegrable (quadraticKernel4 s) volume (-1) 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hden :
      ∀ x ∈ Icc (-1 : ℝ) 1, (1 + s * x) ^ 4 ≠ 0 := by
    intro x hx
    apply pow_ne_zero
    apply ne_of_gt
    apply one_add_sx_pos hs
    rw [abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  unfold quadraticKernel4
  exact
    ((continuous_const.sub (continuous_id.pow 2)).pow 7).continuousOn.div
      ((continuous_const.add (continuous_const.mul continuous_id)).pow 4).continuousOn
      hden

private theorem quadraticKernel6_intervalIntegrable {s : ℝ}
    (hs : |s| < 1) :
    IntervalIntegrable (quadraticKernel6 s) volume (-1) 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hden :
      ∀ x ∈ Icc (-1 : ℝ) 1, (1 + s * x) ^ 6 ≠ 0 := by
    intro x hx
    apply pow_ne_zero
    apply ne_of_gt
    apply one_add_sx_pos hs
    rw [abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  unfold quadraticKernel6
  exact
    ((continuous_const.sub (continuous_id.pow 2)).pow 7).continuousOn.div
      ((continuous_const.add (continuous_const.mul continuous_id)).pow 6).continuousOn
      hden

/--
The exact quadratic integrand is bounded by the two positive kernels retained
in equation (12).
-/
theorem CgIntegrand13_le {s x : ℝ}
    (hs : |s| < 1) (hx : |x| ≤ 1) :
    CgIntegrand13 s x
      ≤ quadraticKernel4 s x + (27 / 22) * quadraticKernel6 s x := by
  have hden : 0 < 1 + s * x := one_add_sx_pos hs hx
  have hweight : 0 ≤ (1 - x ^ 2) ^ 7 := by
    have hbase : 0 ≤ 1 - x ^ 2 := by
      rcases abs_le.mp hx with ⟨hxl, hxu⟩
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + x)
        (by linarith : 0 ≤ 1 - x)]
    positivity
  have hsq : (s + x) ^ 2 ≤ (1 + s * x) ^ 2 :=
    sq_add_le_sq_one_add_mul (le_of_lt hs) hx
  have hfirst :
      (1 - x ^ 2) ^ 7 * (s + x) ^ 2 / (1 + s * x) ^ 6
        ≤ quadraticKernel4 s x := by
    unfold quadraticKernel4
    calc
      (1 - x ^ 2) ^ 7 * (s + x) ^ 2 / (1 + s * x) ^ 6
          ≤
        (1 - x ^ 2) ^ 7 * (1 + s * x) ^ 2
          / (1 + s * x) ^ 6 := by
            apply div_le_div_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left hsq hweight
            · exact pow_nonneg (le_of_lt hden) 6
      _ = (1 - x ^ 2) ^ 7 / (1 + s * x) ^ 4 := by
        field_simp [ne_of_gt hden]
  have hthird :
      (1 - x ^ 2) ^ 7 * (s + x) ^ 2 / (1 + s * x) ^ 8
        ≤ quadraticKernel6 s x := by
    unfold quadraticKernel6
    calc
      (1 - x ^ 2) ^ 7 * (s + x) ^ 2 / (1 + s * x) ^ 8
          ≤
        (1 - x ^ 2) ^ 7 * (1 + s * x) ^ 2
          / (1 + s * x) ^ 8 := by
            apply div_le_div_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left hsq hweight
            · exact pow_nonneg (le_of_lt hden) 8
      _ = (1 - x ^ 2) ^ 7 / (1 + s * x) ^ 6 := by
        field_simp [ne_of_gt hden]
  have hmiddle :
      0 ≤
        (18 / 11) * ((1 - x ^ 2) ^ 7 * (s + x) ^ 2)
          / (1 + s * x) ^ 7 := by
    positivity
  unfold CgIntegrand13
  calc
    (1 - x ^ 2) ^ 7 * (s + x) ^ 2 / (1 + s * x) ^ 6
          - (18 / 11) * ((1 - x ^ 2) ^ 7 * (s + x) ^ 2)
              / (1 + s * x) ^ 7
          + (27 / 22) * ((1 - x ^ 2) ^ 7 * (s + x) ^ 2)
              / (1 + s * x) ^ 8
        ≤
      (1 - x ^ 2) ^ 7 * (s + x) ^ 2 / (1 + s * x) ^ 6
          + (27 / 22) * ((1 - x ^ 2) ^ 7 * (s + x) ^ 2)
              / (1 + s * x) ^ 8 := by
                linarith
    _ ≤ quadraticKernel4 s x + (27 / 22) * quadraticKernel6 s x := by
      have hcoef : (0 : ℝ) ≤ 27 / 22 := by norm_num
      apply add_le_add hfirst
      calc
        (27 / 22) * ((1 - x ^ 2) ^ 7 * (s + x) ^ 2)
              / (1 + s * x) ^ 8
            =
          (27 / 22) *
            ((1 - x ^ 2) ^ 7 * (s + x) ^ 2
              / (1 + s * x) ^ 8) := by ring
        _ ≤ (27 / 22) * quadraticKernel6 s x :=
          mul_le_mul_of_nonneg_left hthird hcoef

/--
Equation (12) specialized to `n = 13`:

`Cg ≤ Ka (1-s²)² (1696/165) / 16`.
-/
theorem Cg13_le (Ka : ℝ) {s : ℝ} (hKa : 0 ≤ Ka) (hs : |s| < 1) :
    Cg13 Ka s
      ≤ Ka * (1 - s ^ 2) ^ 2 / 16 * (1696 / 165) := by
  have hCgInt :
      IntervalIntegrable (CgIntegrand13 s) volume (-1) 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      (CgIntegrand13_continuousOn hs)
  have h4 := quadraticKernel4_intervalIntegrable hs
  have h6 := quadraticKernel6_intervalIntegrable hs
  have hsum :
      IntervalIntegrable
        (fun x => quadraticKernel4 s x
          + (27 / 22) * quadraticKernel6 s x) volume (-1) 1 :=
    h4.add (h6.const_mul (27 / 22))
  have hintegral :
      (∫ x in (-1 : ℝ)..1, CgIntegrand13 s x)
        ≤ 1696 / 165 := by
    calc
      (∫ x in (-1 : ℝ)..1, CgIntegrand13 s x)
          ≤
        ∫ x in (-1 : ℝ)..1,
          (quadraticKernel4 s x + (27 / 22) * quadraticKernel6 s x) := by
            apply intervalIntegral.integral_mono_on (by norm_num)
              hCgInt hsum
            intro x hx
            apply CgIntegrand13_le hs
            rw [abs_le]
            exact ⟨by linarith [hx.1], hx.2⟩
      _ =
        (∫ x in (-1 : ℝ)..1, quadraticKernel4 s x)
          + (27 / 22) *
            (∫ x in (-1 : ℝ)..1, quadraticKernel6 s x) := by
              rw [intervalIntegral.integral_add h4 (h6.const_mul (27 / 22))]
              rw [intervalIntegral.integral_const_mul]
      _ ≤ (256 / 165) + (27 / 22) * (64 / 9) := by
        exact add_le_add (integral_quadraticKernel4_le hs)
          (mul_le_mul_of_nonneg_left
            (integral_quadraticKernel6_le hs) (by norm_num))
      _ = 1696 / 165 := by norm_num
  unfold Cg13
  exact mul_le_mul_of_nonneg_left hintegral (by positivity)

/-- Equation (12), rescaled from `g` to `h = 4g`. -/
theorem Ctheta13_le (Ka : ℝ) {s : ℝ}
    (hKa : 0 ≤ Ka) (hs : |s| < 1) :
    Ctheta13 Ka s
      ≤ Ka * (1 - s ^ 2) ^ 2 * (1696 / 165) := by
  have hC := Cg13_le Ka hKa hs
  unfold Ctheta13
  calc
    16 * Cg13 Ka s
        ≤ 16 *
          (Ka * (1 - s ^ 2) ^ 2 / 16 * (1696 / 165)) :=
      mul_le_mul_of_nonneg_left hC (by norm_num)
    _ = Ka * (1 - s ^ 2) ^ 2 * (1696 / 165) := by ring

/--
The exact factorization obtained after replacing `Ctheta13` by its certified
upper bound.
-/
theorem reducedRiskUpperExpression13_eq (Ka s ε : ℝ) :
    2 * ε * Btheta13 Ka s
        + ε ^ 2 * (Ka * (1 - s ^ 2) ^ 2 * (1696 / 165))
      =
    Ka * (1 - s ^ 2) ^ 2 * ε
      * (ε * (1696 / 165) - I13 s) := by
  unfold Btheta13 Bg13
  ring

/--
Any epsilon satisfying the rational, `s`-independent threshold lies below
the actual linear integral.
-/
theorem epsilon_mul_quadraticBound_lt_I13 {s ε : ℝ}
    (hs : |s| < 1)
    (hεH :
      ε * (1696 / 165) < M 1 * (1489 / 5610)) :
    ε * (1696 / 165) < I13 s := by
  exact hεH.trans_le (certificate_le_I13 hs)

/-- The certified linear integral dominates the fixed quadratic allowance. -/
theorem epsilon13_mul_quadraticBound_lt_I13 {s : ℝ} (hs : |s| < 1) :
    epsilon13 * (1696 / 165) < I13 s := by
  apply epsilon_mul_quadraticBound_lt_I13 hs
  have harith :
      epsilon13 * (1696 / 165)
        < (1024 / 45045) * (1489 / 5610) := by
    unfold epsilon13
    norm_num
  simpa only [M_one] using harith

/--
Generic ratio-free reduced risk certificate for every positive perturbation
below the uniform threshold.
-/
theorem reducedRiskDifference13_neg_of_epsilon
    (Ka : ℝ) {s ε : ℝ}
    (hKa : 0 < Ka) (hs : |s| < 1) (hε : 0 < ε)
    (hεH :
      ε * (1696 / 165) < M 1 * (1489 / 5610)) :
    2 * ε * Btheta13 Ka s + ε ^ 2 * Ctheta13 Ka s < 0 := by
  have hCtheta := Ctheta13_le Ka (le_of_lt hKa) hs
  have hlinear :
      ε * (1696 / 165) - I13 s < 0 := by
    linarith [epsilon_mul_quadraticBound_lt_I13 hs hεH]
  have hsquare : 0 < (1 - s ^ 2) ^ 2 := by
    have : 0 < 1 - s ^ 2 := by
      rcases abs_lt.mp hs with ⟨hsl, hsu⟩
      nlinarith [mul_pos (by linarith : 0 < 1 + s)
        (by linarith : 0 < 1 - s)]
    positivity
  have hfactor :
      0 < Ka * (1 - s ^ 2) ^ 2 * ε := by
    positivity
  calc
    2 * ε * Btheta13 Ka s + ε ^ 2 * Ctheta13 Ka s
        ≤
      2 * ε * Btheta13 Ka s
        + ε ^ 2
          * (Ka * (1 - s ^ 2) ^ 2 * (1696 / 165)) := by
            gcongr
    _ =
      Ka * (1 - s ^ 2) ^ 2 * ε
        * (ε * (1696 / 165) - I13 s) :=
          reducedRiskUpperExpression13_eq Ka s ε
    _ < 0 := mul_neg_of_pos_of_neg hfactor hlinear

/--
The ratio-free reduced risk certificate at `ε = 1 / 2000`.

No sign assumption on, or division by, `Ctheta13` is needed.
-/
theorem reducedRiskDifference13_neg (Ka : ℝ) {s : ℝ}
    (hKa : 0 < Ka) (hs : |s| < 1) :
    2 * epsilon13 * Btheta13 Ka s
        + epsilon13 ^ 2 * Ctheta13 Ka s < 0 := by
  apply reducedRiskDifference13_neg_of_epsilon Ka hKa hs
  · unfold epsilon13
    norm_num
  · rw [M_one]
    unfold epsilon13
    norm_num

end

end GraybillDeal
