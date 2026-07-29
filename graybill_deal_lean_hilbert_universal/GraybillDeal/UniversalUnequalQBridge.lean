import GraybillDeal.UniversalUnequalMomentBridge
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The balanced `q`-derivative contradiction

This file closes the two derivative premises that remained after
`UniversalUnequalMomentBridge`.

At the unequal pivot `r₀=b/(a+b)`, normalize the `q`-dependent denominator
by its value `2c=2ab/(a+b)` at `q=0`:

`base(q,θ) = 1 + q θ(1-θ)/(2c)`.

The normalized posterior residual is

`Q(q) = ∫ (θ-r₀) base(q,θ)^(-p) dν`.

On `|q|<c` the base is uniformly at least `1/2`, so differentiation under
the integral sign is justified by a constant majorant.  At zero,

`Q'(0) = -(p/(2c)) ∫ (θ-r₀)θ(1-θ) dν`.

The centered cubic calculation identifies this with
`universalQDerivativeFromMoment`.  On the other hand, the posterior
identity makes `Q(q)=0` for every `q≥0`.  Uniqueness of the derivative
within `[0,∞)` therefore gives `Q'(0)=0`, contradicting the explicit
unequal obstruction whenever `a ≠ b`.
-/

namespace GraybillDeal

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction Topology

noncomputable section

/-- The normalized balanced denominator in the `q` direction. -/
def universalBalancedQBase
    (a b q : ℝ) (θ : UniversalTheta) : ℝ :=
  1
    + q * ((θ : ℝ) * (1 - (θ : ℝ))
        / (2 * universalUnequalC a b))

/-- The normalized balanced residual integrand. -/
def universalBalancedQIntegrand
    (a b q : ℝ) (θ : UniversalTheta) : ℝ :=
  ((θ : ℝ) - universalUnequalPivot a b)
    * universalBalancedQBase a b q θ ^ (-universalP a b)

/-- Its pointwise `q` derivative. -/
def universalBalancedQDerivIntegrand
    (a b q : ℝ) (θ : UniversalTheta) : ℝ :=
  ((θ : ℝ) - universalUnequalPivot a b)
    * (-universalP a b)
    * ((θ : ℝ) * (1 - (θ : ℝ))
        / (2 * universalUnequalC a b))
    * universalBalancedQBase a b q θ ^ (-universalP a b - 1)

/-- Integral of the normalized balanced residual. -/
def universalBalancedQResidual
    (ν : Measure UniversalTheta) (a b q : ℝ) : ℝ :=
  ∫ θ, universalBalancedQIntegrand a b q θ ∂ν

/-- Integral of its pointwise derivative. -/
def universalBalancedQResidualDeriv
    (ν : Measure UniversalTheta) (a b q : ℝ) : ℝ :=
  ∫ θ, universalBalancedQDerivIntegrand a b q θ ∂ν

/-- The cubic pivot moment occurring in the derivative at zero. -/
def universalPivotCubicMoment
    (ν : Measure UniversalTheta) (a b : ℝ) : ℝ :=
  ∫ θ : UniversalTheta,
    ((θ : ℝ) - universalUnequalPivot a b)
      * (θ : ℝ) * (1 - (θ : ℝ)) ∂ν

/-- Fixed neighborhood for the normalized `q` derivative. -/
def universalBalancedQLocalSet (a b : ℝ) : Set ℝ :=
  Ioo (-universalUnequalC a b) (universalUnequalC a b)

theorem zero_mem_universalBalancedQLocalSet
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (0 : ℝ) ∈ universalBalancedQLocalSet a b := by
  have hc := universalUnequalC_pos ha hb
  unfold universalBalancedQLocalSet
  constructor <;> linarith

theorem abs_q_lt_c_of_mem_universalBalancedQLocalSet
    {a b q : ℝ}
    (hq : q ∈ universalBalancedQLocalSet a b) :
    |q| < universalUnequalC a b := by
  unfold universalBalancedQLocalSet at hq
  rw [abs_lt]
  exact hq

theorem theta_mul_one_sub_nonneg (θ : UniversalTheta) :
    0 ≤ (θ : ℝ) * (1 - (θ : ℝ)) :=
  mul_nonneg θ.property.1 (sub_nonneg.mpr θ.property.2)

theorem theta_mul_one_sub_le_one (θ : UniversalTheta) :
    (θ : ℝ) * (1 - (θ : ℝ)) ≤ 1 := by
  have hθ0 : 0 ≤ (θ : ℝ) := θ.property.1
  have hθ1 : (θ : ℝ) ≤ 1 := θ.property.2
  have h1θ : 0 ≤ 1 - (θ : ℝ) := sub_nonneg.mpr hθ1
  calc
    (θ : ℝ) * (1 - (θ : ℝ))
        ≤ 1 * (1 - (θ : ℝ)) :=
      mul_le_mul_of_nonneg_right hθ1 h1θ
    _ ≤ 1 := by linarith

theorem abs_theta_sub_pivot_le_one
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalTheta) :
    |(θ : ℝ) - universalUnequalPivot a b| ≤ 1 := by
  have hr0 := universalUnequalPivot_pos ha hb
  have hr1 := universalUnequalPivot_lt_one ha hb
  rw [abs_le]
  constructor <;> linarith [θ.property.1, θ.property.2]

/-- Uniform positivity of the normalized `q` base. -/
theorem universalBalancedQBase_ge_half
    {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hq : q ∈ universalBalancedQLocalSet a b)
    (θ : UniversalTheta) :
    1 / 2 ≤ universalBalancedQBase a b q θ := by
  have hc : 0 < universalUnequalC a b :=
    universalUnequalC_pos ha hb
  have hqabs :=
    abs_q_lt_c_of_mem_universalBalancedQLocalSet hq
  have hu0 := theta_mul_one_sub_nonneg θ
  have hu1 := theta_mul_one_sub_le_one θ
  have hratio0 :
      0 ≤
        (θ : ℝ) * (1 - (θ : ℝ))
          / (2 * universalUnequalC a b) := by
    positivity
  have hratio :
      (θ : ℝ) * (1 - (θ : ℝ))
          / (2 * universalUnequalC a b)
        ≤ 1 / (2 * universalUnequalC a b) := by
    exact div_le_div_of_nonneg_right hu1 (by positivity)
  have hprod :
      |q * ((θ : ℝ) * (1 - (θ : ℝ))
          / (2 * universalUnequalC a b))| < 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hratio0]
    calc
      |q| *
          ((θ : ℝ) * (1 - (θ : ℝ))
            / (2 * universalUnequalC a b))
          ≤
        |q| * (1 / (2 * universalUnequalC a b)) :=
          mul_le_mul_of_nonneg_left hratio (abs_nonneg q)
      _ <
        universalUnequalC a b
          * (1 / (2 * universalUnequalC a b)) := by
            exact mul_lt_mul_of_pos_right hqabs (by positivity)
      _ = 1 / 2 := by
        field_simp [hc.ne']
  unfold universalBalancedQBase
  nlinarith
    [neg_abs_le
      (q * ((θ : ℝ) * (1 - (θ : ℝ))
        / (2 * universalUnequalC a b)))]

theorem universalBalancedQBase_pos
    {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hq : q ∈ universalBalancedQLocalSet a b)
    (θ : UniversalTheta) :
    0 < universalBalancedQBase a b q θ :=
  lt_of_lt_of_le (by norm_num)
    (universalBalancedQBase_ge_half ha hb hq θ)

theorem continuous_universalBalancedQBase_theta
    (a b q : ℝ) :
    Continuous
      (fun θ : UniversalTheta =>
        universalBalancedQBase a b q θ) := by
  unfold universalBalancedQBase universalUnequalC universalH
  fun_prop

theorem continuous_universalBalancedQIntegrand_theta
    {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hq : q ∈ universalBalancedQLocalSet a b) :
    Continuous
      (fun θ : UniversalTheta =>
        universalBalancedQIntegrand a b q θ) := by
  unfold universalBalancedQIntegrand
  apply Continuous.mul
  · unfold universalUnequalPivot universalH
    fun_prop
  · exact (continuous_universalBalancedQBase_theta a b q).rpow_const
      (fun θ => Or.inl
        (ne_of_gt (universalBalancedQBase_pos ha hb hq θ)))

theorem continuous_universalBalancedQDerivIntegrand_theta
    {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hq : q ∈ universalBalancedQLocalSet a b) :
    Continuous
      (fun θ : UniversalTheta =>
        universalBalancedQDerivIntegrand a b q θ) := by
  unfold universalBalancedQDerivIntegrand
  apply Continuous.mul
  · unfold universalUnequalPivot universalUnequalC universalH
    fun_prop
  · exact (continuous_universalBalancedQBase_theta a b q).rpow_const
      (fun θ => Or.inl
        (ne_of_gt (universalBalancedQBase_pos ha hb hq θ)))

/-- Pointwise `q` derivative of the normalized residual integrand. -/
theorem hasDerivAt_universalBalancedQIntegrand
    {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hq : q ∈ universalBalancedQLocalSet a b)
    (θ : UniversalTheta) :
    HasDerivAt
      (fun y => universalBalancedQIntegrand a b y θ)
      (universalBalancedQDerivIntegrand a b q θ) q := by
  let v : ℝ :=
    (θ : ℝ) * (1 - (θ : ℝ))
      / (2 * universalUnequalC a b)
  have hbase :
      HasDerivAt
        (fun y : ℝ => universalBalancedQBase a b y θ) v q := by
    unfold universalBalancedQBase
    change HasDerivAt
      ((fun _ : ℝ => (1 : ℝ)) + fun y : ℝ => y * v) v q
    exact
      ((hasDerivAt_const q (1 : ℝ)).add
        ((hasDerivAt_id q).mul_const v)).congr_deriv (by ring)
  have hpow :
      HasDerivAt
        (fun y : ℝ =>
          universalBalancedQBase a b y θ ^ (-universalP a b))
        (v * (-universalP a b)
          * universalBalancedQBase a b q θ
              ^ (-universalP a b - 1)) q :=
    hbase.rpow_const
      (Or.inl
        (ne_of_gt (universalBalancedQBase_pos ha hb hq θ)))
  have h :=
    hpow.const_mul
      ((θ : ℝ) - universalUnequalPivot a b)
  unfold universalBalancedQIntegrand
    universalBalancedQDerivIntegrand
  exact h.congr_deriv (by dsimp only [v]; ring)

/-- Explicit constant domination for the pointwise derivative. -/
theorem norm_universalBalancedQDerivIntegrand_le
    {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hq : q ∈ universalBalancedQLocalSet a b)
    (θ : UniversalTheta) :
    ‖universalBalancedQDerivIntegrand a b q θ‖
      ≤
    universalP a b * (1 / (2 * universalUnequalC a b))
      * (1 / 2 : ℝ) ^ (-universalP a b - 1) := by
  have hp : 0 < universalP a b := universalP_pos ha hb
  have hc : 0 < universalUnequalC a b :=
    universalUnequalC_pos ha hb
  have hx := abs_theta_sub_pivot_le_one ha hb θ
  have hu0 := theta_mul_one_sub_nonneg θ
  have hu1 := theta_mul_one_sub_le_one θ
  have hv0 :
      0 ≤
        (θ : ℝ) * (1 - (θ : ℝ))
          / (2 * universalUnequalC a b) := by
    positivity
  have hv :
      (θ : ℝ) * (1 - (θ : ℝ))
          / (2 * universalUnequalC a b)
        ≤ 1 / (2 * universalUnequalC a b) :=
    div_le_div_of_nonneg_right hu1 (by positivity)
  have hbasepow :
      universalBalancedQBase a b q θ
            ^ (-universalP a b - 1)
        ≤ (1 / 2 : ℝ) ^ (-universalP a b - 1) := by
    exact Real.rpow_le_rpow_of_nonpos
      (by norm_num)
      (universalBalancedQBase_ge_half ha hb hq θ)
      (by linarith)
  have hbasepow0 :
      0 ≤
        universalBalancedQBase a b q θ
          ^ (-universalP a b - 1) :=
    Real.rpow_nonneg
      (universalBalancedQBase_pos ha hb hq θ).le _
  unfold universalBalancedQDerivIntegrand
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
    abs_neg, abs_of_pos hp, abs_of_nonneg hv0,
    abs_of_nonneg hbasepow0]
  calc
    |(θ : ℝ) - universalUnequalPivot a b|
          * universalP a b
          * ((θ : ℝ) * (1 - (θ : ℝ))
              / (2 * universalUnequalC a b))
          * universalBalancedQBase a b q θ
              ^ (-universalP a b - 1)
        ≤
      1 * universalP a b
          * (1 / (2 * universalUnequalC a b))
          * universalBalancedQBase a b q θ
              ^ (-universalP a b - 1) := by
        gcongr
    _ ≤
      1 * universalP a b
          * (1 / (2 * universalUnequalC a b))
          * (1 / 2 : ℝ) ^ (-universalP a b - 1) := by
        gcongr
    _ =
      universalP a b * (1 / (2 * universalUnequalC a b))
        * (1 / 2 : ℝ) ^ (-universalP a b - 1) := by
      ring

/-- Differentiation under the arbitrary finite measure in the `q` chart. -/
theorem hasDerivAt_universalBalancedQResidual
    (ν : Measure UniversalTheta) [IsFiniteMeasure ν]
    {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hq : q ∈ universalBalancedQLocalSet a b) :
    HasDerivAt
      (universalBalancedQResidual ν a b)
      (universalBalancedQResidualDeriv ν a b q) q := by
  have hs : universalBalancedQLocalSet a b ∈ 𝓝 q :=
    isOpen_Ioo.mem_nhds hq
  have hFmeas :
      ∀ᶠ y in 𝓝 q,
        AEStronglyMeasurable
          (fun θ : UniversalTheta =>
            universalBalancedQIntegrand a b y θ) ν := by
    filter_upwards [hs] with y hy
    exact
      (continuous_universalBalancedQIntegrand_theta
        ha hb hy).aestronglyMeasurable
  have hFint :
      Integrable
        (fun θ : UniversalTheta =>
          universalBalancedQIntegrand a b q θ) ν := by
    let f : UniversalTheta →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact
        ⟨fun θ : UniversalTheta =>
            universalBalancedQIntegrand a b q θ,
          continuous_universalBalancedQIntegrand_theta ha hb hq⟩
    change Integrable (f : UniversalTheta → ℝ) ν
    exact BoundedContinuousFunction.integrable ν f
  have hF'meas :
      AEStronglyMeasurable
        (fun θ : UniversalTheta =>
          universalBalancedQDerivIntegrand a b q θ) ν :=
    (continuous_universalBalancedQDerivIntegrand_theta
      ha hb hq).aestronglyMeasurable
  have hbound :
      ∀ᵐ θ ∂ν, ∀ y ∈ universalBalancedQLocalSet a b,
        ‖universalBalancedQDerivIntegrand a b y θ‖
          ≤
        universalP a b * (1 / (2 * universalUnequalC a b))
          * (1 / 2 : ℝ) ^ (-universalP a b - 1) := by
    exact ae_of_all ν fun θ y hy =>
      norm_universalBalancedQDerivIntegrand_le ha hb hy θ
  have hboundint :
      Integrable
        (fun _ : UniversalTheta =>
          universalP a b * (1 / (2 * universalUnequalC a b))
            * (1 / 2 : ℝ) ^ (-universalP a b - 1)) ν :=
    integrable_const _
  have hdiff :
      ∀ᵐ θ ∂ν, ∀ y ∈ universalBalancedQLocalSet a b,
        HasDerivAt
          (fun z => universalBalancedQIntegrand a b z θ)
          (universalBalancedQDerivIntegrand a b y θ) y := by
    exact ae_of_all ν fun θ y hy =>
      hasDerivAt_universalBalancedQIntegrand ha hb hy θ
  exact
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun y θ => universalBalancedQIntegrand a b y θ)
      (F' := fun y θ =>
        universalBalancedQDerivIntegrand a b y θ)
      (bound := fun _ : UniversalTheta =>
        universalP a b * (1 / (2 * universalUnequalC a b))
          * (1 / 2 : ℝ) ^ (-universalP a b - 1))
      hs hFmeas hFint hF'meas hbound hboundint hdiff).2

/-- Evaluation of the differentiated normalized residual at `q = 0`. -/
theorem universalBalancedQResidualDeriv_zero
    (ν : Measure UniversalTheta) (a b : ℝ) :
    universalBalancedQResidualDeriv ν a b 0
      =
    universalQDerivativeFromMoment a b
      (universalPivotCubicMoment ν a b) := by
  unfold universalBalancedQResidualDeriv
    universalBalancedQDerivIntegrand
    universalBalancedQBase universalQDerivativeFromMoment
    universalPivotCubicMoment
  simp only [zero_mul, add_zero, Real.one_rpow]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with θ
  ring

/-- The derivative of the normalized residual at the balanced point. -/
theorem hasDerivAt_universalBalancedQResidual_zero
    (ν : Measure UniversalTheta) [IsFiniteMeasure ν]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt
      (universalBalancedQResidual ν a b)
      (universalQDerivativeFromMoment a b
        (universalPivotCubicMoment ν a b)) 0 := by
  rw [← universalBalancedQResidualDeriv_zero]
  exact hasDerivAt_universalBalancedQResidual ν ha hb
    (zero_mem_universalBalancedQLocalSet ha hb)

/--
The cubic pivot moment is exactly the centered polynomial moment consumed
by the algebraic obstruction theorem.
-/
theorem universalPivotCubicMoment_eq_centeredIntegrandMoment
    (ν : Measure UniversalTheta) [IsProbabilityMeasure ν]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    universalPivotCubicMoment ν a b
      =
    universalCenteredIntegrandMoment a b
      (universalCenteredMoment ν a b 1)
      (universalCenteredMoment ν a b 2)
      (universalCenteredMoment ν a b 3) := by
  have hh : universalH a b ≠ 0 :=
    (universalH_pos ha hb).ne'
  let z : UniversalTheta → ℝ :=
    fun θ => universalCenteredVariable a b θ
  have hz0 : Integrable (fun θ => z θ ^ 0) ν :=
    integrable_universalCenteredVariable_pow ν a b 0
  have hz1 : Integrable (fun θ => z θ ^ 1) ν :=
    integrable_universalCenteredVariable_pow ν a b 1
  have hz1' : Integrable z ν := by
    simpa only [pow_one] using hz1
  have hz2 : Integrable (fun θ => z θ ^ 2) ν :=
    integrable_universalCenteredVariable_pow ν a b 2
  have hz3 : Integrable (fun θ => z θ ^ 3) ν :=
    integrable_universalCenteredVariable_pow ν a b 3
  have h0 :
      Integrable
        (fun _ : UniversalTheta =>
          a * b * universalUnequalD a b) ν :=
    integrable_const _
  have h1 :
      Integrable
        (fun θ : UniversalTheta =>
          (universalUnequalD a b ^ 2 - a * b) * z θ) ν :=
    hz1'.const_mul _
  have h2 :
      Integrable
        (fun θ : UniversalTheta =>
          2 * universalUnequalD a b * z θ ^ 2) ν :=
    hz2.const_mul _
  have hiadd3 :=
    integral_add ((h0.add h1).sub h2) hz3
  change
    (∫ θ : UniversalTheta,
        (a * b * universalUnequalD a b
            + (universalUnequalD a b ^ 2 - a * b) * z θ
            - 2 * universalUnequalD a b * z θ ^ 2)
          + z θ ^ 3 ∂ν)
      =
    (∫ θ : UniversalTheta,
        a * b * universalUnequalD a b
          + (universalUnequalD a b ^ 2 - a * b) * z θ
          - 2 * universalUnequalD a b * z θ ^ 2 ∂ν)
      + ∫ θ : UniversalTheta, z θ ^ 3 ∂ν at hiadd3
  have hisub2 :=
    integral_sub (h0.add h1) h2
  change
    (∫ θ : UniversalTheta,
        (a * b * universalUnequalD a b
            + (universalUnequalD a b ^ 2 - a * b) * z θ)
          - 2 * universalUnequalD a b * z θ ^ 2 ∂ν)
      =
    (∫ θ : UniversalTheta,
        a * b * universalUnequalD a b
          + (universalUnequalD a b ^ 2 - a * b) * z θ ∂ν)
      - ∫ θ : UniversalTheta,
          2 * universalUnequalD a b * z θ ^ 2 ∂ν at hisub2
  have hiadd1 :=
    integral_add h0 h1
  change
    (∫ θ : UniversalTheta,
        a * b * universalUnequalD a b
          + (universalUnequalD a b ^ 2 - a * b) * z θ ∂ν)
      =
    (∫ _ : UniversalTheta,
        a * b * universalUnequalD a b ∂ν)
      + ∫ θ : UniversalTheta,
          (universalUnequalD a b ^ 2 - a * b) * z θ ∂ν at hiadd1
  have hpoint :
      ∀ θ : UniversalTheta,
        ((θ : ℝ) - universalUnequalPivot a b)
            * (θ : ℝ) * (1 - (θ : ℝ))
          =
        (a * b * universalUnequalD a b
            + (universalUnequalD a b ^ 2 - a * b) * z θ
            - 2 * universalUnequalD a b * z θ ^ 2
            + z θ ^ 3)
          / universalH a b ^ 3 := by
    intro θ
    calc
      ((θ : ℝ) - universalUnequalPivot a b)
            * (θ : ℝ) * (1 - (θ : ℝ))
          =
        ((universalUnequalD a b - z θ)
              * (a - z θ) * (b + z θ))
            / universalH a b ^ 3 := by
              exact universalUnequal_integrand_centered hh
      _ =
        (a * b * universalUnequalD a b
            + (universalUnequalD a b ^ 2 - a * b) * z θ
            - 2 * universalUnequalD a b * z θ ^ 2
            + z θ ^ 3)
          / universalH a b ^ 3 := by
            rw [universalUnequal_centered_cubic_expand]
  unfold universalPivotCubicMoment
  calc
    (∫ θ : UniversalTheta,
        ((θ : ℝ) - universalUnequalPivot a b)
          * (θ : ℝ) * (1 - (θ : ℝ)) ∂ν)
        =
      ∫ θ : UniversalTheta,
        (a * b * universalUnequalD a b
            + (universalUnequalD a b ^ 2 - a * b) * z θ
            - 2 * universalUnequalD a b * z θ ^ 2
            + z θ ^ 3)
          / universalH a b ^ 3 ∂ν := by
            apply integral_congr_ae
            exact ae_of_all ν hpoint
    _ =
      (a * b * universalUnequalD a b
          + (universalUnequalD a b ^ 2 - a * b)
              * universalCenteredMoment ν a b 1
          - 2 * universalUnequalD a b
              * universalCenteredMoment ν a b 2
          + universalCenteredMoment ν a b 3)
        / universalH a b ^ 3 := by
          rw [show
              (fun θ : UniversalTheta =>
                (a * b * universalUnequalD a b
                    + (universalUnequalD a b ^ 2 - a * b) * z θ
                    - 2 * universalUnequalD a b * z θ ^ 2
                    + z θ ^ 3)
                  / universalH a b ^ 3)
                =
              fun θ =>
                (1 / universalH a b ^ 3)
                  * (a * b * universalUnequalD a b
                      + (universalUnequalD a b ^ 2 - a * b) * z θ
                      - 2 * universalUnequalD a b * z θ ^ 2
                      + z θ ^ 3) by
                funext θ
                ring]
          rw [integral_const_mul]
          rw [hiadd3, hisub2, hiadd1]
          simp only [integral_const, probReal_univ,
            one_smul, integral_const_mul]
          unfold universalCenteredMoment
          dsimp only [z]
          ring
    _ =
      universalCenteredIntegrandMoment a b
        (universalCenteredMoment ν a b 1)
        (universalCenteredMoment ν a b 2)
        (universalCenteredMoment ν a b 3) := by
          rfl

/-- Exact factorization of the original denominator on the balanced line. -/
theorem universalB_at_unequalPivot
    {a b q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalTheta) :
    universalB a b (universalUnequalPivot a b) q θ
      =
    2 * universalUnequalC a b
      * universalBalancedQBase a b q θ := by
  have hh : a + b ≠ 0 := by linarith
  unfold universalB universalUnequalPivot universalBalancedQBase
    universalUnequalC universalH
  field_simp [hh, ha.ne', hb.ne']
  ring

/-- For nonnegative `q`, the normalized balanced denominator is positive. -/
theorem universalBalancedQBase_ge_one
    {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hq : 0 ≤ q) (θ : UniversalTheta) :
    1 ≤ universalBalancedQBase a b q θ := by
  have hc : 0 < universalUnequalC a b :=
    universalUnequalC_pos ha hb
  have hu0 := theta_mul_one_sub_nonneg θ
  unfold universalBalancedQBase
  have :
      0 ≤ q * ((θ : ℝ) * (1 - (θ : ℝ))
        / (2 * universalUnequalC a b)) := by
    positivity
  linarith

/-- The original kernel is a fixed positive scalar times the normalized one. -/
theorem universalKernel_at_unequalPivot
    {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hq : 0 ≤ q) (θ : UniversalTheta) :
    universalKernel a b (universalUnequalPivot a b) q θ
      =
    (2 * universalUnequalC a b) ^ (-universalP a b)
      * universalBalancedQBase a b q θ ^ (-universalP a b) := by
  have hc :
      0 ≤ 2 * universalUnequalC a b :=
    (mul_pos (by norm_num) (universalUnequalC_pos ha hb)).le
  have hbase :
      0 ≤ universalBalancedQBase a b q θ :=
    (universalBalancedQBase_ge_one ha hb hq θ).trans'
      (by norm_num)
  unfold universalKernel universalExponent
  rw [universalB_at_unequalPivot ha hb θ]
  exact Real.mul_rpow hc hbase

/--
The posterior identity makes the normalized balanced residual zero on the
entire right half-line `q ≥ 0`.
-/
theorem UniversalPosteriorIdentity.balancedQResidual_eq_zero
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b q : ℝ}
    (H : UniversalPosteriorIdentity ν a b)
    (ha : 0 < a) (hb : 0 < b) (hq : 0 ≤ q) :
    universalBalancedQResidual ν a b q = 0 := by
  have hr0 : 0 < universalUnequalPivot a b :=
    universalUnequalPivot_pos ha hb
  have hr1 : universalUnequalPivot a b < 1 :=
    universalUnequalPivot_lt_one ha hb
  have hraw :=
    H.integral_theta_sub_mul_kernel_eq_zero
      ha hb hr0 hr1 hq
  have hscale :
      (2 * universalUnequalC a b) ^ (-universalP a b) ≠ 0 :=
    ne_of_gt
      (Real.rpow_pos_of_pos
        (mul_pos (by norm_num) (universalUnequalC_pos ha hb)) _)
  have hrelation :
      (∫ θ : UniversalTheta,
          ((θ : ℝ) - universalUnequalPivot a b)
            * universalKernel a b
                (universalUnequalPivot a b) q θ ∂ν)
        =
      (2 * universalUnequalC a b) ^ (-universalP a b)
        * universalBalancedQResidual ν a b q := by
    unfold universalBalancedQResidual
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with θ
    rw [universalKernel_at_unequalPivot ha hb hq θ]
    unfold universalBalancedQIntegrand
    ring
  rw [hrelation] at hraw
  exact (mul_eq_zero.mp hraw).resolve_left hscale

/--
The right-half-line posterior identity forces the ordinary derivative of
the normalized residual at zero to vanish.

This is the quantifier-sensitive step: `action_eq` is assumed only for
`q ≥ 0`, so we restrict the already-proved ordinary derivative to
`[0,∞)` and use uniqueness of the derivative within that set.
-/
theorem UniversalPosteriorIdentity.balancedQDerivative_eq_zero
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b : ℝ}
    (H : UniversalPosteriorIdentity ν a b)
    (ha : 0 < a) (hb : 0 < b) :
    universalQDerivativeFromMoment a b
      (universalPivotCubicMoment ν a b) = 0 := by
  have hderiv :
      HasDerivAt
        (universalBalancedQResidual ν a b)
        (universalQDerivativeFromMoment a b
          (universalPivotCubicMoment ν a b)) 0 :=
    hasDerivAt_universalBalancedQResidual_zero ν ha hb
  have heq :
      universalBalancedQResidual ν a b
        =ᶠ[𝓝[Ici (0 : ℝ)] 0] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact H.balancedQResidual_eq_zero ha hb hq
  have hconst :
      HasDerivWithinAt
        (universalBalancedQResidual ν a b)
        0 (Ici (0 : ℝ)) 0 := by
    exact
      (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt
        |>.congr_of_eventuallyEq_of_mem heq self_mem_Ici
  have hmaps :=
    (uniqueDiffOn_Ici (0 : ℝ)).eq self_mem_Ici
      hderiv.hasDerivWithinAt hconst
  have hone :=
    congrArg (fun f : ℝ →L[ℝ] ℝ => f 1) hmaps
  simpa using hone

/--
No posterior identity of the universal form exists at unequal positive
shape parameters.

This is the closed unequal analytic theorem: unlike
`no_zero_qDerivative`, it has no derivative-identification premises.
-/
theorem UniversalPosteriorIdentity.unequal_false
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b : ℝ}
    (H : UniversalPosteriorIdentity ν a b)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    False := by
  have hzero :=
    H.balancedQDerivative_eq_zero ha hb
  rw [universalPivotCubicMoment_eq_centeredIntegrandMoment
    ν ha hb] at hzero
  exact H.no_zero_qDerivative ha hb hab hzero rfl

end

end GraybillDeal
