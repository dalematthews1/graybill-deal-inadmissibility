import GraybillDeal.GeneralCentralAnalytic
import GraybillDeal.GeneralQuadratic

/-!
# The reduced risk argument at arbitrary equal sample size

This file packages the parts of the all-sample-size reduced-risk proof that
do not depend on the still-separate endpoint evaluations of the two
quadratic kernels.

For residual degrees of freedom `ν`, define

`Hν = J₄ + generalQuadraticTopCoefficient ν * J₆`.

Once the endpoint layer proves uniform bounds for the integrals of
`generalQuadraticKernel4` and `generalQuadraticKernel6`, the results below
give the quadratic bound, the ratio-free strict risk inequality, and the
existence of a single positive perturbation coefficient for that fixed
sample size.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

/-- The exact reduced linear term for `g = p(r)(1-q/4)`. -/
def generalBg (Ka ν s : ℝ) : ℝ :=
  -(Ka * (1 - s ^ 2) ^ 2 / 8) * generalI ν s

/-- The exact reduced quadratic term for `g = p(r)(1-q/4)`. -/
def generalCg (Ka ν s : ℝ) : ℝ :=
  Ka * (1 - s ^ 2) ^ 2 / 16
    * (∫ x in (-1 : ℝ)..1, generalCgIntegrand ν s x)

/-- The linear risk coefficient for `h = 4g = p(r)(4-q)`. -/
def generalBtheta (Ka ν s : ℝ) : ℝ :=
  4 * generalBg Ka ν s

/-- The quadratic risk coefficient for `h = 4g = p(r)(4-q)`. -/
def generalCtheta (Ka ν s : ℝ) : ℝ :=
  16 * generalCg Ka ν s

/-- The quadratic allowance supplied by endpoint bounds `J₄,J₆`. -/
def generalQuadraticAllowance (ν J4 J6 : ℝ) : ℝ :=
  J4 + generalQuadraticTopCoefficient ν * J6

theorem generalCgIntegrand_continuousOn
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    ContinuousOn (generalCgIntegrand ν s) (Icc (-1 : ℝ) 1) := by
  have hden :
      ∀ x ∈ Icc (-1 : ℝ) 1, 1 + s * x ≠ 0 := by
    intro x hx
    apply ne_of_gt
    apply one_add_sx_pos hs
    rw [abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hweight :
      Continuous (generalQuadraticWeight ν) := by
    unfold generalQuadraticWeight
    exact
      (Real.continuous_rpow_const
        (by linarith : 0 ≤ ν / 2 + 1)).comp
          (continuous_const.sub (continuous_id.pow 2))
  have hnum :
      Continuous
        (fun x : ℝ =>
          generalQuadraticWeight ν x * (s + x) ^ 2) :=
    hweight.mul ((continuous_const.add continuous_id).pow 2)
  have hbase :
      Continuous (fun x : ℝ => 1 + s * x) := by
    fun_prop
  unfold generalCgIntegrand
  exact
    ((hnum.continuousOn.div (hbase.pow 6).continuousOn
        (fun x hx => pow_ne_zero 6 (hden x hx))).sub
      ((continuous_const.mul hnum).continuousOn.div
        (hbase.pow 7).continuousOn
        (fun x hx => pow_ne_zero 7 (hden x hx)))).add
      ((continuous_const.mul hnum).continuousOn.div
        (hbase.pow 8).continuousOn
        (fun x hx => pow_ne_zero 8 (hden x hx)))

theorem generalQuadraticKernel4_intervalIntegrable
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    IntervalIntegrable (generalQuadraticKernel4 ν s)
      volume (-1 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hden :
      ∀ x ∈ Icc (-1 : ℝ) 1, (1 + s * x) ^ 4 ≠ 0 := by
    intro x hx
    apply pow_ne_zero
    apply ne_of_gt
    apply one_add_sx_pos hs
    rw [abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hweight :
      Continuous (generalQuadraticWeight ν) := by
    unfold generalQuadraticWeight
    exact
      (Real.continuous_rpow_const
        (by linarith : 0 ≤ ν / 2 + 1)).comp
          (continuous_const.sub (continuous_id.pow 2))
  unfold generalQuadraticKernel4
  exact hweight.continuousOn.div
    ((continuous_const.add
      (continuous_const.mul continuous_id)).pow 4).continuousOn hden

theorem generalQuadraticKernel6_intervalIntegrable
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    IntervalIntegrable (generalQuadraticKernel6 ν s)
      volume (-1 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hden :
      ∀ x ∈ Icc (-1 : ℝ) 1, (1 + s * x) ^ 6 ≠ 0 := by
    intro x hx
    apply pow_ne_zero
    apply ne_of_gt
    apply one_add_sx_pos hs
    rw [abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hweight :
      Continuous (generalQuadraticWeight ν) := by
    unfold generalQuadraticWeight
    exact
      (Real.continuous_rpow_const
        (by linarith : 0 ≤ ν / 2 + 1)).comp
          (continuous_const.sub (continuous_id.pow 2))
  unfold generalQuadraticKernel6
  exact hweight.continuousOn.div
    ((continuous_const.add
      (continuous_const.mul continuous_id)).pow 6).continuousOn hden

/--
Pointwise reduction plus any two uniform kernel bounds gives the combined
quadratic-integral bound.
-/
theorem integral_generalCgIntegrand_le_of_kernel_bounds
    {ν s J4 J6 : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1)
    (hJ4 :
      (∫ x in (-1 : ℝ)..1, generalQuadraticKernel4 ν s x) ≤ J4)
    (hJ6 :
      (∫ x in (-1 : ℝ)..1, generalQuadraticKernel6 ν s x) ≤ J6) :
    (∫ x in (-1 : ℝ)..1, generalCgIntegrand ν s x)
      ≤ generalQuadraticAllowance ν J4 J6 := by
  have hCg :
      IntervalIntegrable (generalCgIntegrand ν s)
        volume (-1 : ℝ) 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      (generalCgIntegrand_continuousOn hν hs)
  have h4 := generalQuadraticKernel4_intervalIntegrable hν hs
  have h6 := generalQuadraticKernel6_intervalIntegrable hν hs
  have htop0 :
      0 ≤ generalQuadraticTopCoefficient ν :=
    le_of_lt (generalQuadraticTopCoefficient_pos hν)
  have hsum :
      IntervalIntegrable
        (fun x =>
          generalQuadraticKernel4 ν s x
            + generalQuadraticTopCoefficient ν
              * generalQuadraticKernel6 ν s x)
        volume (-1 : ℝ) 1 :=
    h4.add (h6.const_mul (generalQuadraticTopCoefficient ν))
  calc
    (∫ x in (-1 : ℝ)..1, generalCgIntegrand ν s x)
        ≤
      ∫ x in (-1 : ℝ)..1,
        (generalQuadraticKernel4 ν s x
          + generalQuadraticTopCoefficient ν
            * generalQuadraticKernel6 ν s x) := by
          apply intervalIntegral.integral_mono_on
            (by norm_num) hCg hsum
          intro x hx
          apply generalCgIntegrand_le hν hs
          rw [abs_le]
          exact ⟨by linarith [hx.1], hx.2⟩
    _ =
      (∫ x in (-1 : ℝ)..1, generalQuadraticKernel4 ν s x)
        + generalQuadraticTopCoefficient ν
          * (∫ x in (-1 : ℝ)..1,
              generalQuadraticKernel6 ν s x) := by
            rw [intervalIntegral.integral_add h4
              (h6.const_mul (generalQuadraticTopCoefficient ν))]
            rw [intervalIntegral.integral_const_mul]
    _ ≤
      J4 + generalQuadraticTopCoefficient ν * J6 :=
        add_le_add hJ4 (mul_le_mul_of_nonneg_left hJ6 htop0)
    _ = generalQuadraticAllowance ν J4 J6 := by
      rfl

/-- The resulting bound for the reduced quadratic coefficient `Cg`. -/
theorem generalCg_le_of_kernel_bounds
    (Ka : ℝ) {ν s J4 J6 : ℝ}
    (hKa : 0 ≤ Ka) (hν : 9 ≤ ν) (hs : |s| < 1)
    (hJ4 :
      (∫ x in (-1 : ℝ)..1, generalQuadraticKernel4 ν s x) ≤ J4)
    (hJ6 :
      (∫ x in (-1 : ℝ)..1, generalQuadraticKernel6 ν s x) ≤ J6) :
    generalCg Ka ν s
      ≤ Ka * (1 - s ^ 2) ^ 2 / 16
        * generalQuadraticAllowance ν J4 J6 := by
  unfold generalCg
  exact mul_le_mul_of_nonneg_left
    (integral_generalCgIntegrand_le_of_kernel_bounds hν hs hJ4 hJ6)
    (by positivity)

/-- The same bound after rescaling from `g` to `h = 4g`. -/
theorem generalCtheta_le_of_kernel_bounds
    (Ka : ℝ) {ν s J4 J6 : ℝ}
    (hKa : 0 ≤ Ka) (hν : 9 ≤ ν) (hs : |s| < 1)
    (hJ4 :
      (∫ x in (-1 : ℝ)..1, generalQuadraticKernel4 ν s x) ≤ J4)
    (hJ6 :
      (∫ x in (-1 : ℝ)..1, generalQuadraticKernel6 ν s x) ≤ J6) :
    generalCtheta Ka ν s
      ≤ Ka * (1 - s ^ 2) ^ 2
        * generalQuadraticAllowance ν J4 J6 := by
  have hC :=
    generalCg_le_of_kernel_bounds Ka hKa hν hs hJ4 hJ6
  unfold generalCtheta
  calc
    16 * generalCg Ka ν s
        ≤
      16 *
        (Ka * (1 - s ^ 2) ^ 2 / 16
          * generalQuadraticAllowance ν J4 J6) :=
      mul_le_mul_of_nonneg_left hC (by norm_num)
    _ =
      Ka * (1 - s ^ 2) ^ 2
        * generalQuadraticAllowance ν J4 J6 := by ring

/-- The general central theorem makes the exact reduced linear term negative. -/
theorem generalBg_neg
    (Ka : ℝ) (ν : ℕ) (hν : 9 ≤ ν) {s : ℝ}
    (hKa : 0 < Ka) (hs : |s| < 1) :
    generalBg Ka (ν : ℝ) s < 0 := by
  have hsquare : 0 < (1 - s ^ 2) ^ 2 := by
    have hs2 : 0 < 1 - s ^ 2 := by
      rcases abs_lt.mp hs with ⟨hsl, hsu⟩
      nlinarith [mul_pos (by linarith : 0 < 1 + s)
        (by linarith : 0 < 1 - s)]
    positivity
  have hfactor : 0 < Ka * (1 - s ^ 2) ^ 2 / 8 := by
    positivity
  have hI : 0 < generalI (ν : ℝ) s :=
    generalI_pos ν hν hs
  unfold generalBg
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hfactor) hI

theorem generalBtheta_neg
    (Ka : ℝ) (ν : ℕ) (hν : 9 ≤ ν) {s : ℝ}
    (hKa : 0 < Ka) (hs : |s| < 1) :
    generalBtheta Ka (ν : ℝ) s < 0 := by
  unfold generalBtheta
  exact mul_neg_of_pos_of_neg (by norm_num)
    (generalBg_neg Ka ν hν hKa hs)

/--
Exact factorization after replacing `generalCtheta` by a quadratic allowance
`H`.
-/
theorem generalReducedRiskUpperExpression_eq
    (Ka ν s ε H : ℝ) :
    2 * ε * generalBtheta Ka ν s
        + ε ^ 2 * (Ka * (1 - s ^ 2) ^ 2 * H)
      =
    Ka * (1 - s ^ 2) ^ 2 * ε
      * (ε * H - generalI ν s) := by
  unfold generalBtheta generalBg
  ring

/--
The certified first-three-term lower bound dominates any proposed
quadratic allowance satisfying the displayed strict inequality.
-/
theorem general_epsilon_mul_allowance_lt_generalI
    (ν : ℕ) (hν : 9 ≤ ν) {s ε H : ℝ}
    (hs : |s| < 1)
    (hεH :
      ε * H
        < generalMoment (ν : ℝ) 1
          * generalLowerQuadratic (ν : ℝ) (s ^ 2)) :
    ε * H < generalI (ν : ℝ) s := by
  exact hεH.trans_le
    (general_certificate_le_generalI ν hν hs)

/--
Ratio-free reduced risk certificate under an arbitrary valid quadratic
allowance.  No sign assumption on `generalCtheta`, and no division by it,
is required.
-/
theorem generalReducedRiskDifference_neg_of_epsilon
    (Ka H : ℝ) (ν : ℕ) (hν : 9 ≤ ν) {s ε : ℝ}
    (hKa : 0 < Ka) (hs : |s| < 1) (hε : 0 < ε)
    (hCtheta :
      generalCtheta Ka (ν : ℝ) s
        ≤ Ka * (1 - s ^ 2) ^ 2 * H)
    (hεH :
      ε * H
        < generalMoment (ν : ℝ) 1
          * generalLowerQuadratic (ν : ℝ) (s ^ 2)) :
    2 * ε * generalBtheta Ka (ν : ℝ) s
        + ε ^ 2 * generalCtheta Ka (ν : ℝ) s < 0 := by
  have hlinear : ε * H - generalI (ν : ℝ) s < 0 := by
    linarith [general_epsilon_mul_allowance_lt_generalI
      ν hν hs hεH]
  have hsquare : 0 < (1 - s ^ 2) ^ 2 := by
    have hs2 : 0 < 1 - s ^ 2 := by
      rcases abs_lt.mp hs with ⟨hsl, hsu⟩
      nlinarith [mul_pos (by linarith : 0 < 1 + s)
        (by linarith : 0 < 1 - s)]
    positivity
  have hfactor :
      0 < Ka * (1 - s ^ 2) ^ 2 * ε := by
    positivity
  calc
    2 * ε * generalBtheta Ka (ν : ℝ) s
          + ε ^ 2 * generalCtheta Ka (ν : ℝ) s
        ≤
      2 * ε * generalBtheta Ka (ν : ℝ) s
          + ε ^ 2 * (Ka * (1 - s ^ 2) ^ 2 * H) := by
            gcongr
    _ =
      Ka * (1 - s ^ 2) ^ 2 * ε
        * (ε * H - generalI (ν : ℝ) s) :=
          generalReducedRiskUpperExpression_eq
            Ka (ν : ℝ) s ε H
    _ < 0 := mul_neg_of_pos_of_neg hfactor hlinear

/--
For each fixed residual degree of freedom, any positive uniform quadratic
allowance yields a positive perturbation coefficient that works for every
interior variance ratio.
-/
theorem exists_generalReducedRisk_epsilon
    (Ka H : ℝ) (ν : ℕ) (hν : 9 ≤ ν)
    (hKa : 0 < Ka) (hH : 0 < H)
    (hCtheta :
      ∀ {s : ℝ}, |s| < 1 →
        generalCtheta Ka (ν : ℝ) s
          ≤ Ka * (1 - s ^ 2) ^ 2 * H) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℝ, |s| < 1 →
        2 * ε * generalBtheta Ka (ν : ℝ) s
          + ε ^ 2 * generalCtheta Ka (ν : ℝ) s < 0 := by
  have hM :
      0 < generalMoment (ν : ℝ) 1 := by
    apply generalMoment_pos
    have hνR : (9 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
    linarith
  obtain ⟨ε, hε, hεbound⟩ :=
    exists_general_epsilon ν hν
      (generalMoment (ν : ℝ) 1) H hM hH
  refine ⟨ε, hε, ?_⟩
  intro s hs
  apply generalReducedRiskDifference_neg_of_epsilon
    Ka H ν hν hKa hs hε (hCtheta hs)
  apply hεbound (s ^ 2) (sq_nonneg s)
  rcases abs_lt.mp hs with ⟨hsl, hsu⟩
  nlinarith [mul_pos (by linarith : 0 < 1 + s)
    (by linarith : 0 < 1 - s)]

/--
Endpoint bounds for `J₄,J₆` are sufficient to produce the all-variance-ratio
strict reduced-risk improvement.
-/
theorem exists_generalReducedRisk_epsilon_of_kernel_bounds
    (Ka J4 J6 : ℝ) (ν : ℕ) (hν : 9 ≤ ν)
    (hKa : 0 < Ka) (hJ4pos : 0 < J4) (hJ6nonneg : 0 ≤ J6)
    (hJ4 :
      ∀ {s : ℝ}, |s| < 1 →
        (∫ x in (-1 : ℝ)..1,
          generalQuadraticKernel4 (ν : ℝ) s x) ≤ J4)
    (hJ6 :
      ∀ {s : ℝ}, |s| < 1 →
        (∫ x in (-1 : ℝ)..1,
          generalQuadraticKernel6 (ν : ℝ) s x) ≤ J6) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℝ, |s| < 1 →
        2 * ε * generalBtheta Ka (ν : ℝ) s
          + ε ^ 2 * generalCtheta Ka (ν : ℝ) s < 0 := by
  have hνR : (9 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
  have htop0 :
      0 ≤ generalQuadraticTopCoefficient (ν : ℝ) :=
    le_of_lt (generalQuadraticTopCoefficient_pos hνR)
  have hH :
      0 < generalQuadraticAllowance (ν : ℝ) J4 J6 := by
    unfold generalQuadraticAllowance
    nlinarith [mul_nonneg htop0 hJ6nonneg]
  apply exists_generalReducedRisk_epsilon
    Ka (generalQuadraticAllowance (ν : ℝ) J4 J6)
      ν hν hKa hH
  intro s hs
  exact generalCtheta_le_of_kernel_bounds
    Ka (le_of_lt hKa) hνR hs (hJ4 hs) (hJ6 hs)

end

end GraybillDeal
