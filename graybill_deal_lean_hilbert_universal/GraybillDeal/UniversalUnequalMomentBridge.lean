import GraybillDeal.UniversalPosteriorIdentity
import GraybillDeal.UniversalUnequalAlgebra
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-!
# The centered Taylor-moment bridge for unequal sample sizes

This file connects the universal posterior identity at `q = 0` to the
three centered moments consumed by `UniversalUnequalAlgebra`.

For positive beta shapes `a,b`, put

* `h = a+b`,
* `p = h+3/2`,
* `d = a-b`,
* `r₀ = b/h`,
* `c = ab/h`, and
* `Z = a-hθ`.

Along the line `r(t)=r₀+ct`, the denominator factors as

`B(a,b,r(t),0,θ) = 2c(1+tZ)`.

Consequently, the posterior identity is equivalent, near `t=0`, to

`H(t) = E[(d-Z-abt)(1+tZ)^(-p)] = 0`.

The value and the first two derivatives at zero give

`E Z = d`,

`E Z² = d² + ab/p`,

`E Z³ = d E Z² + 2abd/(p+1)`.

The last two expressions are then converted, by exact algebra, into the
ODE-moment formulas used by `universalUnequal_qDerivative_of_odeMoments`.

The analytic ingredient is differentiation under the integral sign.  It is
proved below for a term family closed under differentiation, using an
explicit constant majorant on
`|t| < 1/(2(a+b))`.  Thus the complete posterior-to-moment calculation is
machine checked without an additional premise.
-/

namespace GraybillDeal

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction Topology

noncomputable section

/-- The centered random variable `Z=a-(a+b)θ`. -/
def universalCenteredVariable (a b : ℝ) (θ : UniversalTheta) : ℝ :=
  universalCenteredZ a b (θ : ℝ)

/-- The `k`th centered moment of `Z`. -/
def universalCenteredMoment
    (ν : Measure UniversalTheta) (a b : ℝ) (k : ℕ) : ℝ :=
  ∫ θ, universalCenteredVariable a b θ ^ k ∂ν

/-- The balanced `q=0` line in the `r` coordinate. -/
def universalCenteredPath (a b t : ℝ) : ℝ :=
  universalUnequalPivot a b + universalUnequalC a b * t

/-- The normalized centered residual whose integral vanishes near zero. -/
def universalCenteredResidual
    (a b t : ℝ) (θ : UniversalTheta) : ℝ :=
  let z := universalCenteredVariable a b θ
  (universalUnequalD a b - z - a * b * t)
    * (1 + t * z) ^ (-universalP a b)

/-- Integral of the centered residual. -/
def universalCenteredResidualIntegral
    (ν : Measure UniversalTheta) (a b t : ℝ) : ℝ :=
  ∫ θ, universalCenteredResidual a b t θ ∂ν

/-- The normalized affine base `1+tZ`. -/
def universalCenteredBase
    (a b t : ℝ) (θ : UniversalTheta) : ℝ :=
  1 + t * universalCenteredVariable a b θ

/--
A common term family closed under differentiation in `t`.

`d/dt term(c,n,e) = term(ce,n+1,e-1)`.
-/
def universalUnequalTerm
    (a b c : ℝ) (n : ℕ) (e t : ℝ)
    (θ : UniversalTheta) : ℝ :=
  c * universalCenteredVariable a b θ ^ n
    * universalCenteredBase a b t θ ^ e

/-- Integral of a normalized centered term. -/
def universalUnequalTermIntegral
    (ν : Measure UniversalTheta)
    (a b c : ℝ) (n : ℕ) (e t : ℝ) : ℝ :=
  ∫ θ, universalUnequalTerm a b c n e t θ ∂ν

/-- The fixed local set used in the unequal centered Taylor argument. -/
def universalUnequalLocalSet (a b : ℝ) : Set ℝ :=
  Ioo (-(1 / (2 * universalH a b)))
    (1 / (2 * universalH a b))

/-- The residual integral written as a combination of centered terms. -/
def universalCenteredTaylor0
    (ν : Measure UniversalTheta) (a b t : ℝ) : ℝ :=
  (universalUnequalD a b - a * b * t)
      * universalUnequalTermIntegral ν a b 1 0
          (-universalP a b) t
    - universalUnequalTermIntegral ν a b 1 1
        (-universalP a b) t

/-- The first derivative of `universalCenteredTaylor0`. -/
def universalCenteredTaylor1
    (ν : Measure UniversalTheta) (a b t : ℝ) : ℝ :=
  (-(a * b))
      * universalUnequalTermIntegral ν a b 1 0
          (-universalP a b) t
    + (universalUnequalD a b - a * b * t)
        * universalUnequalTermIntegral ν a b
            (-universalP a b) 1
            (-universalP a b - 1) t
    - universalUnequalTermIntegral ν a b
        (-universalP a b) 2
        (-universalP a b - 1) t

/-- The second derivative of `universalCenteredTaylor0`. -/
def universalCenteredTaylor2
    (ν : Measure UniversalTheta) (a b t : ℝ) : ℝ :=
  (-(a * b))
      * universalUnequalTermIntegral ν a b
          (-universalP a b) 1
          (-universalP a b - 1) t
    + (-(a * b))
        * universalUnequalTermIntegral ν a b
            (-universalP a b) 1
            (-universalP a b - 1) t
    + (universalUnequalD a b - a * b * t)
        * universalUnequalTermIntegral ν a b
            (universalP a b * (universalP a b + 1)) 2
            (-universalP a b - 2) t
    - universalUnequalTermIntegral ν a b
        (universalP a b * (universalP a b + 1)) 3
        (-universalP a b - 2) t

theorem continuous_universalCenteredVariable_pow
    (a b : ℝ) (k : ℕ) :
    Continuous
      (fun θ : UniversalTheta =>
        universalCenteredVariable a b θ ^ k) := by
  unfold universalCenteredVariable universalCenteredZ universalH
  fun_prop

theorem integrable_universalCenteredVariable_pow
    (ν : Measure UniversalTheta) [IsFiniteMeasure ν]
    (a b : ℝ) (k : ℕ) :
    Integrable
      (fun θ : UniversalTheta =>
        universalCenteredVariable a b θ ^ k) ν := by
  let f : UniversalTheta →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun θ : UniversalTheta =>
          universalCenteredVariable a b θ ^ k,
        continuous_universalCenteredVariable_pow a b k⟩
  change Integrable (f : UniversalTheta → ℝ) ν
  exact BoundedContinuousFunction.integrable ν f

theorem universalCenteredMoment_zero
    (ν : Measure UniversalTheta) [IsProbabilityMeasure ν]
    (a b : ℝ) :
    universalCenteredMoment ν a b 0 = 1 := by
  simp [universalCenteredMoment]

theorem universalCenteredVariable_bounds
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalTheta) :
    -b ≤ universalCenteredVariable a b θ
      ∧ universalCenteredVariable a b θ ≤ a := by
  have hθ0 : 0 ≤ (θ : ℝ) := θ.property.1
  have hθ1 : (θ : ℝ) ≤ 1 := θ.property.2
  unfold universalCenteredVariable universalCenteredZ universalH
  constructor <;> nlinarith

theorem abs_universalCenteredVariable_le_h
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalTheta) :
    |universalCenteredVariable a b θ| ≤ universalH a b := by
  rcases universalCenteredVariable_bounds ha hb θ with ⟨hzlo, hzhi⟩
  rw [abs_le]
  unfold universalH
  constructor <;> linarith

theorem abs_lt_local_radius_of_mem_universalUnequalLocalSet
    {a b t : ℝ}
    (ht : t ∈ universalUnequalLocalSet a b) :
    |t| < 1 / (2 * universalH a b) := by
  unfold universalUnequalLocalSet at ht
  rw [abs_lt]
  exact ht

theorem zero_mem_universalUnequalLocalSet
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (0 : ℝ) ∈ universalUnequalLocalSet a b := by
  have hh : 0 < universalH a b := universalH_pos ha hb
  unfold universalUnequalLocalSet
  constructor
  · have hr : 0 < 1 / (2 * universalH a b) := by positivity
    linarith
  · positivity

/-- Uniform positivity of `1+tZ` on the local set. -/
theorem universalCenteredBase_ge_half
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ universalUnequalLocalSet a b)
    (θ : UniversalTheta) :
    1 / 2 ≤ universalCenteredBase a b t θ := by
  have hh : 0 < universalH a b := universalH_pos ha hb
  have htabs :=
    abs_lt_local_radius_of_mem_universalUnequalLocalSet ht
  have hzabs :=
    abs_universalCenteredVariable_le_h ha hb θ
  have hprod :
      |t * universalCenteredVariable a b θ| < 1 / 2 := by
    calc
      |t * universalCenteredVariable a b θ|
          =
        |t| * |universalCenteredVariable a b θ| := abs_mul _ _
      _ ≤ |t| * universalH a b :=
        mul_le_mul_of_nonneg_left hzabs (abs_nonneg t)
      _ <
        (1 / (2 * universalH a b)) * universalH a b := by
          exact mul_lt_mul_of_pos_right htabs hh
      _ = 1 / 2 := by
        field_simp [hh.ne']
  unfold universalCenteredBase
  nlinarith [neg_abs_le (t * universalCenteredVariable a b θ)]

theorem universalCenteredBase_pos
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ universalUnequalLocalSet a b)
    (θ : UniversalTheta) :
    0 < universalCenteredBase a b t θ :=
  lt_of_lt_of_le (by norm_num)
    (universalCenteredBase_ge_half ha hb ht θ)

theorem continuous_universalCenteredVariable (a b : ℝ) :
    Continuous (universalCenteredVariable a b) := by
  unfold universalCenteredVariable universalCenteredZ universalH
  fun_prop

theorem continuous_universalCenteredBase_theta
    (a b t : ℝ) :
    Continuous
      (fun θ : UniversalTheta =>
        universalCenteredBase a b t θ) := by
  unfold universalCenteredBase
  exact continuous_const.add
    (continuous_const.mul
      (continuous_universalCenteredVariable a b))

theorem continuous_universalUnequalTerm_theta
    {a b c e t : ℝ} {n : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ universalUnequalLocalSet a b) :
    Continuous
      (fun θ : UniversalTheta =>
        universalUnequalTerm a b c n e t θ) := by
  unfold universalUnequalTerm
  apply Continuous.mul
  · exact continuous_const.mul
      ((continuous_universalCenteredVariable a b).pow n)
  · exact (continuous_universalCenteredBase_theta a b t).rpow_const
      (fun θ => Or.inl
        (ne_of_gt (universalCenteredBase_pos ha hb ht θ)))

/-- Pointwise derivative recurrence for the unequal centered term family. -/
theorem hasDerivAt_universalUnequalTerm
    {a b c e t : ℝ} {n : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ universalUnequalLocalSet a b)
    (θ : UniversalTheta) :
    HasDerivAt
      (fun y => universalUnequalTerm a b c n e y θ)
      (universalUnequalTerm a b (c * e) (n + 1) (e - 1) t θ)
      t := by
  have hbase :
      HasDerivAt
        (fun y : ℝ => universalCenteredBase a b y θ)
        (universalCenteredVariable a b θ) t := by
    unfold universalCenteredBase
    change HasDerivAt
      ((fun _ : ℝ => (1 : ℝ))
        + fun y : ℝ =>
          y * universalCenteredVariable a b θ)
      (universalCenteredVariable a b θ) t
    exact
      ((hasDerivAt_const t (1 : ℝ)).add
        ((hasDerivAt_id t).mul_const
          (universalCenteredVariable a b θ))).congr_deriv (by ring)
  have hpow :
      HasDerivAt
        (fun y : ℝ => universalCenteredBase a b y θ ^ e)
        (universalCenteredVariable a b θ * e
          * universalCenteredBase a b t θ ^ (e - 1)) t :=
    hbase.rpow_const
      (Or.inl
        (ne_of_gt (universalCenteredBase_pos ha hb ht θ)))
  have h :=
    hpow.const_mul
      (c * universalCenteredVariable a b θ ^ n)
  simpa only [universalUnequalTerm] using
    h.congr_deriv (by rw [pow_succ]; ring)

/-- An explicit constant majorant for the derivative term. -/
theorem norm_universalUnequalTerm_derivative_le
    {a b c e t : ℝ} {n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (he : e ≤ 0)
    (ht : t ∈ universalUnequalLocalSet a b)
    (θ : UniversalTheta) :
    ‖universalUnequalTerm a b (c * e) (n + 1) (e - 1) t θ‖
      ≤
    |c * e| * universalH a b ^ (n + 1)
      * (1 / 2 : ℝ) ^ (e - 1) := by
  have hh : 0 < universalH a b := universalH_pos ha hb
  have hzpow :
      |universalCenteredVariable a b θ| ^ (n + 1)
        ≤ universalH a b ^ (n + 1) := by
    gcongr
    exact abs_universalCenteredVariable_le_h ha hb θ
  have hbasepow :
      universalCenteredBase a b t θ ^ (e - 1)
        ≤ (1 / 2 : ℝ) ^ (e - 1) := by
    exact Real.rpow_le_rpow_of_nonpos
      (by norm_num)
      (universalCenteredBase_ge_half ha hb ht θ)
      (by linarith)
  have hbasepow0 :
      0 ≤ universalCenteredBase a b t θ ^ (e - 1) :=
    Real.rpow_nonneg
      (universalCenteredBase_pos ha hb ht θ).le _
  unfold universalUnequalTerm
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
    abs_of_nonneg hbasepow0]
  calc
    |c * e| * |universalCenteredVariable a b θ| ^ (n + 1)
          * universalCenteredBase a b t θ ^ (e - 1)
        ≤
      |c * e| * universalH a b ^ (n + 1)
          * universalCenteredBase a b t θ ^ (e - 1) := by
            gcongr
    _ ≤
      |c * e| * universalH a b ^ (n + 1)
          * (1 / 2 : ℝ) ^ (e - 1) := by
            gcongr

/--
Differentiation under an arbitrary finite measure for the unequal centered
term family.
-/
theorem hasDerivAt_universalUnequalTermIntegral
    (ν : Measure UniversalTheta) [IsFiniteMeasure ν]
    {a b c e t : ℝ} {n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (he : e ≤ 0)
    (ht : t ∈ universalUnequalLocalSet a b) :
    HasDerivAt
      (universalUnequalTermIntegral ν a b c n e)
      (universalUnequalTermIntegral ν a b
        (c * e) (n + 1) (e - 1) t)
      t := by
  have hs : universalUnequalLocalSet a b ∈ 𝓝 t :=
    isOpen_Ioo.mem_nhds ht
  have hFmeas :
      ∀ᶠ y in 𝓝 t,
        AEStronglyMeasurable
          (fun θ : UniversalTheta =>
            universalUnequalTerm a b c n e y θ) ν := by
    filter_upwards [hs] with y hy
    exact
      (continuous_universalUnequalTerm_theta ha hb hy).aestronglyMeasurable
  have hFint :
      Integrable
        (fun θ : UniversalTheta =>
          universalUnequalTerm a b c n e t θ) ν := by
    let f : UniversalTheta →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact
        ⟨fun θ : UniversalTheta =>
            universalUnequalTerm a b c n e t θ,
          continuous_universalUnequalTerm_theta ha hb ht⟩
    change Integrable (f : UniversalTheta → ℝ) ν
    exact BoundedContinuousFunction.integrable ν f
  have hF'meas :
      AEStronglyMeasurable
        (fun θ : UniversalTheta =>
          universalUnequalTerm a b (c * e)
            (n + 1) (e - 1) t θ) ν :=
    (continuous_universalUnequalTerm_theta ha hb ht).aestronglyMeasurable
  have hbound :
      ∀ᵐ θ ∂ν, ∀ y ∈ universalUnequalLocalSet a b,
        ‖universalUnequalTerm a b (c * e)
            (n + 1) (e - 1) y θ‖
          ≤
        |c * e| * universalH a b ^ (n + 1)
          * (1 / 2 : ℝ) ^ (e - 1) := by
    exact ae_of_all ν fun θ y hy =>
      norm_universalUnequalTerm_derivative_le ha hb he hy θ
  have hboundint :
      Integrable
        (fun _ : UniversalTheta =>
          |c * e| * universalH a b ^ (n + 1)
            * (1 / 2 : ℝ) ^ (e - 1)) ν :=
    integrable_const _
  have hdiff :
      ∀ᵐ θ ∂ν, ∀ y ∈ universalUnequalLocalSet a b,
        HasDerivAt
          (fun z => universalUnequalTerm a b c n e z θ)
          (universalUnequalTerm a b (c * e)
            (n + 1) (e - 1) y θ)
          y := by
    exact ae_of_all ν fun θ y hy =>
      hasDerivAt_universalUnequalTerm ha hb hy θ
  exact
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun y θ =>
        universalUnequalTerm a b c n e y θ)
      (F' := fun y θ =>
        universalUnequalTerm a b (c * e)
          (n + 1) (e - 1) y θ)
      (bound := fun _ : UniversalTheta =>
        |c * e| * universalH a b ^ (n + 1)
          * (1 / 2 : ℝ) ^ (e - 1))
      hs hFmeas hFint hF'meas hbound hboundint hdiff).2

theorem hasDerivAt_universalCenteredTaylor0
    (ν : Measure UniversalTheta) [IsFiniteMeasure ν]
    {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ universalUnequalLocalSet a b) :
    HasDerivAt
      (universalCenteredTaylor0 ν a b)
      (universalCenteredTaylor1 ν a b t) t := by
  have hp : 0 < universalP a b := universalP_pos ha hb
  have hlinear :
      HasDerivAt
        (fun y : ℝ => universalUnequalD a b - a * b * y)
        (-(a * b)) t := by
    change HasDerivAt
      ((fun _ : ℝ => universalUnequalD a b)
        - fun y : ℝ => (a * b) * y)
      (-(a * b)) t
    exact
      ((hasDerivAt_const t (universalUnequalD a b)).sub
        ((hasDerivAt_id t).const_mul (a * b))).congr_deriv (by ring)
  have h0 :=
    hasDerivAt_universalUnequalTermIntegral ν
      (a := a) (b := b) (c := 1) (n := 0)
      (e := -universalP a b) ha hb (by linarith) ht
  have h1 :=
    hasDerivAt_universalUnequalTermIntegral ν
      (a := a) (b := b) (c := 1) (n := 1)
      (e := -universalP a b) ha hb (by linarith) ht
  unfold universalCenteredTaylor0 universalCenteredTaylor1
  exact ((hlinear.mul h0).sub h1).congr_deriv (by simp)

theorem hasDerivAt_universalCenteredTaylor1
    (ν : Measure UniversalTheta) [IsFiniteMeasure ν]
    {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ universalUnequalLocalSet a b) :
    HasDerivAt
      (universalCenteredTaylor1 ν a b)
      (universalCenteredTaylor2 ν a b t) t := by
  have hp : 0 < universalP a b := universalP_pos ha hb
  have hlinear :
      HasDerivAt
        (fun y : ℝ => universalUnequalD a b - a * b * y)
        (-(a * b)) t := by
    change HasDerivAt
      ((fun _ : ℝ => universalUnequalD a b)
        - fun y : ℝ => (a * b) * y)
      (-(a * b)) t
    exact
      ((hasDerivAt_const t (universalUnequalD a b)).sub
        ((hasDerivAt_id t).const_mul (a * b))).congr_deriv (by ring)
  have h0 :=
    hasDerivAt_universalUnequalTermIntegral ν
      (a := a) (b := b) (c := 1) (n := 0)
      (e := -universalP a b) ha hb (by linarith) ht
  have h1 :=
    hasDerivAt_universalUnequalTermIntegral ν
      (a := a) (b := b) (c := -universalP a b) (n := 1)
      (e := -universalP a b - 1) ha hb (by linarith) ht
  have h2 :=
    hasDerivAt_universalUnequalTermIntegral ν
      (a := a) (b := b) (c := -universalP a b) (n := 2)
      (e := -universalP a b - 1) ha hb (by linarith) ht
  have hfirst := h0.const_mul (-(a * b))
  have hmiddle := hlinear.mul h1
  have hcoef :
      -universalP a b * (-universalP a b - 1)
        = universalP a b * (universalP a b + 1) := by
    ring
  have hexp :
      -universalP a b - 1 - 1
        = -universalP a b - 2 := by
    ring
  unfold universalCenteredTaylor1 universalCenteredTaylor2
  apply ((hfirst.add hmiddle).sub h2).congr_deriv
  rw [hcoef, hexp]
  ring

theorem integrable_universalUnequalTerm
    (ν : Measure UniversalTheta) [IsFiniteMeasure ν]
    {a b c e t : ℝ} {n : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ universalUnequalLocalSet a b) :
    Integrable
      (fun θ : UniversalTheta =>
        universalUnequalTerm a b c n e t θ) ν := by
  let f : UniversalTheta →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun θ : UniversalTheta =>
          universalUnequalTerm a b c n e t θ,
        continuous_universalUnequalTerm_theta ha hb ht⟩
  change Integrable (f : UniversalTheta → ℝ) ν
  exact BoundedContinuousFunction.integrable ν f

/-- The normalized residual integral is exactly the Taylor combination. -/
theorem universalCenteredResidualIntegral_eq_taylor0
    (ν : Measure UniversalTheta) [IsFiniteMeasure ν]
    {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ universalUnequalLocalSet a b) :
    universalCenteredResidualIntegral ν a b t
      = universalCenteredTaylor0 ν a b t := by
  have h0 :
      Integrable
        (fun θ : UniversalTheta =>
          universalUnequalTerm a b 1 0
            (-universalP a b) t θ) ν :=
    integrable_universalUnequalTerm ν ha hb ht
  have h1 :
      Integrable
        (fun θ : UniversalTheta =>
          universalUnequalTerm a b 1 1
            (-universalP a b) t θ) ν :=
    integrable_universalUnequalTerm ν ha hb ht
  unfold universalCenteredResidualIntegral
  calc
    (∫ θ : UniversalTheta,
        universalCenteredResidual a b t θ ∂ν)
        =
      ∫ θ : UniversalTheta,
        (universalUnequalD a b - a * b * t)
            * universalUnequalTerm a b 1 0
                (-universalP a b) t θ
          - universalUnequalTerm a b 1 1
              (-universalP a b) t θ ∂ν := by
        apply integral_congr_ae
        filter_upwards with θ
        simp only [universalCenteredResidual,
          universalUnequalTerm, universalCenteredBase,
          pow_zero, pow_one, one_mul]
        ring
    _ =
      (universalUnequalD a b - a * b * t)
          * universalUnequalTermIntegral ν a b 1 0
              (-universalP a b) t
        - universalUnequalTermIntegral ν a b 1 1
            (-universalP a b) t := by
      rw [integral_sub (h0.const_mul _) h1,
        integral_const_mul]
      rfl
    _ = universalCenteredTaylor0 ν a b t := rfl

theorem universalCenteredTaylor1_eq_zero_of_taylor0
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hzero :
      ∀ y ∈ universalUnequalLocalSet a b,
        universalCenteredTaylor0 ν a b y = 0)
    (ht : t ∈ universalUnequalLocalSet a b) :
    universalCenteredTaylor1 ν a b t = 0 := by
  have heq :
      universalCenteredTaylor0 ν a b
        =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy
    exact hzero y hy
  have hconst :
      HasDerivAt (universalCenteredTaylor0 ν a b) 0 t :=
    (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq
  exact
    (hasDerivAt_universalCenteredTaylor0 ν ha hb ht).unique hconst

theorem universalCenteredTaylor2_eq_zero_of_taylor0
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hzero :
      ∀ y ∈ universalUnequalLocalSet a b,
        universalCenteredTaylor0 ν a b y = 0) :
    universalCenteredTaylor2 ν a b 0 = 0 := by
  have hzeroMem : (0 : ℝ) ∈ universalUnequalLocalSet a b :=
    zero_mem_universalUnequalLocalSet ha hb
  have heq :
      universalCenteredTaylor1 ν a b
        =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hzeroMem] with y hy
    exact universalCenteredTaylor1_eq_zero_of_taylor0
      ha hb hzero hy
  have hconst :
      HasDerivAt (universalCenteredTaylor1 ν a b) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq heq
  exact
    (hasDerivAt_universalCenteredTaylor1 ν ha hb hzeroMem).unique hconst

theorem universalUnequalTermIntegral_zero
    (ν : Measure UniversalTheta)
    (a b c e : ℝ) (n : ℕ) :
    universalUnequalTermIntegral ν a b c n e 0
      = c * universalCenteredMoment ν a b n := by
  unfold universalUnequalTermIntegral universalUnequalTerm
    universalCenteredBase universalCenteredMoment
  simp only [zero_mul, add_zero, Real.one_rpow, mul_one]
  rw [← integral_const_mul]

theorem universalCenteredTaylor0_zero
    (ν : Measure UniversalTheta) [IsProbabilityMeasure ν]
    (a b : ℝ) :
    universalCenteredTaylor0 ν a b 0
      =
    universalUnequalD a b
      - universalCenteredMoment ν a b 1 := by
  unfold universalCenteredTaylor0
  simp_rw [universalUnequalTermIntegral_zero]
  rw [universalCenteredMoment_zero]
  ring

theorem universalCenteredTaylor1_zero
    (ν : Measure UniversalTheta) [IsProbabilityMeasure ν]
    (a b : ℝ) :
    universalCenteredTaylor1 ν a b 0
      =
    -(a * b)
      - universalP a b * universalUnequalD a b
          * universalCenteredMoment ν a b 1
      + universalP a b
          * universalCenteredMoment ν a b 2 := by
  unfold universalCenteredTaylor1
  simp_rw [universalUnequalTermIntegral_zero]
  rw [universalCenteredMoment_zero]
  ring

theorem universalCenteredTaylor2_zero
    (ν : Measure UniversalTheta) (a b : ℝ) :
    universalCenteredTaylor2 ν a b 0
      =
    2 * a * b * universalP a b
        * universalCenteredMoment ν a b 1
      + universalP a b * (universalP a b + 1)
        * (universalUnequalD a b
            * universalCenteredMoment ν a b 2
          - universalCenteredMoment ν a b 3) := by
  unfold universalCenteredTaylor2
  simp_rw [universalUnequalTermIntegral_zero]
  ring

/-- A locally zero centered residual fixes the first centered moment. -/
theorem universalCenteredMoment_one_of_taylor0
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hzero :
      ∀ y ∈ universalUnequalLocalSet a b,
        universalCenteredTaylor0 ν a b y = 0) :
    universalCenteredMoment ν a b 1
      = universalUnequalD a b := by
  have hzero0 :=
    hzero 0 (zero_mem_universalUnequalLocalSet ha hb)
  rw [universalCenteredTaylor0_zero] at hzero0
  linarith

/-- A locally zero centered residual fixes the second centered moment. -/
theorem universalCenteredMoment_two_raw_of_taylor0
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hzero :
      ∀ y ∈ universalUnequalLocalSet a b,
        universalCenteredTaylor0 ν a b y = 0) :
    universalCenteredMoment ν a b 2
      =
    universalUnequalD a b ^ 2
      + a * b / universalP a b := by
  have hp : 0 < universalP a b := universalP_pos ha hb
  have hzero1 :=
    universalCenteredTaylor1_eq_zero_of_taylor0
      ha hb hzero (zero_mem_universalUnequalLocalSet ha hb)
  rw [universalCenteredTaylor1_zero,
    universalCenteredMoment_one_of_taylor0 ha hb hzero] at hzero1
  field_simp [hp.ne'] at hzero1 ⊢
  nlinarith

theorem universalCenteredMoment_two_of_taylor0
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hzero :
      ∀ y ∈ universalUnequalLocalSet a b,
        universalCenteredTaylor0 ν a b y = 0) :
    universalCenteredMoment ν a b 2
      =
    (universalUnequalK a b
        + universalUnequalLambda a b
            * universalUnequalD a b ^ 2)
      / (universalUnequalLambda a b + 1) := by
  have hp : 0 < universalP a b := universalP_pos ha hb
  have hlambda :
      0 < universalUnequalLambda a b + 1 := by
    unfold universalUnequalLambda
    linarith [universalH_pos ha hb]
  rw [universalCenteredMoment_two_raw_of_taylor0 ha hb hzero]
  unfold universalP universalUnequalLambda universalUnequalK
    universalUnequalD universalH
  field_simp [hp.ne', hlambda.ne']
  ring

/-- A locally zero centered residual fixes the third centered moment. -/
theorem universalCenteredMoment_three_raw_of_taylor0
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hzero :
      ∀ y ∈ universalUnequalLocalSet a b,
        universalCenteredTaylor0 ν a b y = 0) :
    universalCenteredMoment ν a b 3
      =
    universalUnequalD a b
        * universalCenteredMoment ν a b 2
      + 2 * a * b * universalUnequalD a b
          / (universalP a b + 1) := by
  have hp : 0 < universalP a b := universalP_pos ha hb
  have hp1 : 0 < universalP a b + 1 := by linarith
  have hzero2 :=
    universalCenteredTaylor2_eq_zero_of_taylor0 ha hb hzero
  rw [universalCenteredTaylor2_zero,
    universalCenteredMoment_one_of_taylor0 ha hb hzero] at hzero2
  field_simp [hp.ne', hp1.ne'] at hzero2 ⊢
  nlinarith

theorem universalCenteredMoment_three_of_taylor0
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hzero :
      ∀ y ∈ universalUnequalLocalSet a b,
        universalCenteredTaylor0 ν a b y = 0) :
    universalCenteredMoment ν a b 3
      =
    universalUnequalD a b
      * (2 * universalUnequalS a b
          + 3 * universalUnequalLambda a b
              * universalUnequalK a b
          + universalUnequalLambda a b ^ 2
              * universalUnequalD a b ^ 2)
      / ((universalUnequalLambda a b + 1)
          * (universalUnequalLambda a b + 2)) := by
  have hp : 0 < universalP a b := universalP_pos ha hb
  have hp1 : 0 < universalP a b + 1 := by linarith
  have hl1 : 0 < universalUnequalLambda a b + 1 := by
    unfold universalUnequalLambda
    linarith [universalH_pos ha hb]
  have hl2 : 0 < universalUnequalLambda a b + 2 := by
    unfold universalUnequalLambda
    linarith [universalH_pos ha hb]
  rw [universalCenteredMoment_three_raw_of_taylor0 ha hb hzero,
    universalCenteredMoment_two_raw_of_taylor0 ha hb hzero]
  unfold universalP universalUnequalLambda universalUnequalK
    universalUnequalS universalUnequalD universalH
  field_simp [hp.ne', hp1.ne', hl1.ne', hl2.ne']
  ring

/--
The complete posterior-to-ODE-moment bridge.  Its three fields are exactly
the hypotheses expected by `universalUnequal_qDerivative_of_odeMoments`.
-/
structure UniversalUnequalOdeMoments
    (ν : Measure UniversalTheta) (a b : ℝ) : Prop where
  first :
    universalCenteredMoment ν a b 1
      = universalUnequalD a b
  second :
    universalCenteredMoment ν a b 2
      =
    (universalUnequalK a b
        + universalUnequalLambda a b
            * universalUnequalD a b ^ 2)
      / (universalUnequalLambda a b + 1)
  third :
    universalCenteredMoment ν a b 3
      =
    universalUnequalD a b
      * (2 * universalUnequalS a b
          + 3 * universalUnequalLambda a b
              * universalUnequalK a b
          + universalUnequalLambda a b ^ 2
              * universalUnequalD a b ^ 2)
      / ((universalUnequalLambda a b + 1)
          * (universalUnequalLambda a b + 2))

theorem universalUnequalOdeMoments_of_taylor0
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hzero :
      ∀ y ∈ universalUnequalLocalSet a b,
        universalCenteredTaylor0 ν a b y = 0) :
    UniversalUnequalOdeMoments ν a b where
  first := universalCenteredMoment_one_of_taylor0 ha hb hzero
  second := universalCenteredMoment_two_of_taylor0 ha hb hzero
  third := universalCenteredMoment_three_of_taylor0 ha hb hzero

theorem universalCenteredPath_eq
    {a b t : ℝ} (hh : universalH a b ≠ 0) :
    universalCenteredPath a b t
      = b * (1 + a * t) / universalH a b := by
  unfold universalCenteredPath universalUnequalPivot universalUnequalC
  field_simp [hh]

theorem one_sub_universalCenteredPath_eq
    {a b t : ℝ} (hh : universalH a b ≠ 0) :
    1 - universalCenteredPath a b t
      = a * (1 - b * t) / universalH a b := by
  unfold universalCenteredPath universalUnequalPivot universalUnequalC
    universalH
  unfold universalH at hh
  field_simp [hh]
  ring

theorem universalCenteredPath_pos
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : |t| < 1 / universalH a b) :
    0 < universalCenteredPath a b t := by
  have hh : 0 < universalH a b := universalH_pos ha hb
  have htlower : -(1 / universalH a b) < t := (abs_lt.mp ht).1
  have hat : 0 < 1 + a * t := by
    have hah : a < universalH a b := by
      unfold universalH
      linarith
    have haratio : a / universalH a b < 1 := by
      rw [div_lt_one hh]
      exact hah
    have hatlower :
        -(a / universalH a b) < a * t := by
      have hmul := mul_lt_mul_of_pos_left htlower ha
      calc
        -(a / universalH a b)
            = a * (-(1 / universalH a b)) := by ring
        _ < a * t := hmul
    linarith
  rw [universalCenteredPath_eq hh.ne']
  positivity

theorem universalCenteredPath_lt_one
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : |t| < 1 / universalH a b) :
    universalCenteredPath a b t < 1 := by
  have hh : 0 < universalH a b := universalH_pos ha hb
  have htupper : t < 1 / universalH a b := (abs_lt.mp ht).2
  have hbh : b < universalH a b := by
    unfold universalH
    linarith
  have hbratio : b / universalH a b < 1 := by
    rw [div_lt_one hh]
    exact hbh
  have hbtupper : b * t < b / universalH a b := by
    have hmul := mul_lt_mul_of_pos_left htupper hb
    calc
      b * t < b * (1 / universalH a b) := hmul
      _ = b / universalH a b := by ring
  have hbt : 0 < 1 - b * t := by
    linarith
  rw [← sub_pos]
  rw [one_sub_universalCenteredPath_eq hh.ne']
  positivity

theorem one_add_centered_pos
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : |t| < 1 / universalH a b)
    (θ : UniversalTheta) :
    0 < 1 + t * universalCenteredVariable a b θ := by
  have hh : 0 < universalH a b := universalH_pos ha hb
  have hz :=
    abs_universalCenteredVariable_le_h ha hb θ
  have hprod :
      |t * universalCenteredVariable a b θ| < 1 := by
    rw [abs_mul]
    have ht' : |t| * universalH a b < 1 := by
      calc
        |t| * universalH a b
            < (1 / universalH a b) * universalH a b :=
          mul_lt_mul_of_pos_right ht hh
        _ = 1 := by field_simp [hh.ne']
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hz (abs_nonneg t)) ht'
  linarith [neg_lt_of_abs_lt hprod]

theorem universalB_centeredPath_zero
    {a b t : ℝ} (hh : universalH a b ≠ 0)
    (θ : UniversalTheta) :
    universalB a b (universalCenteredPath a b t) 0 θ
      =
    2 * universalUnequalC a b
      * (1 + t * universalCenteredVariable a b θ) := by
  unfold universalB universalCenteredPath universalUnequalPivot
    universalUnequalC universalCenteredVariable universalCenteredZ
    universalH
  unfold universalH at hh
  field_simp [hh]
  ring

theorem theta_sub_centeredPath_eq
    {a b t : ℝ} (hh : universalH a b ≠ 0)
    (θ : UniversalTheta) :
    (θ : ℝ) - universalCenteredPath a b t
      =
    (universalUnequalD a b
        - universalCenteredVariable a b θ - a * b * t)
      / universalH a b := by
  unfold universalCenteredPath universalUnequalPivot universalUnequalC
    universalUnequalD universalCenteredVariable universalCenteredZ
    universalH
  unfold universalH at hh
  field_simp [hh]
  ring

theorem universalKernel_centeredPath_zero
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : |t| < 1 / universalH a b)
    (θ : UniversalTheta) :
    universalKernel a b (universalCenteredPath a b t) 0 θ
      =
    (2 * universalUnequalC a b) ^ (-universalP a b)
      * (1 + t * universalCenteredVariable a b θ)
          ^ (-universalP a b) := by
  have hh : universalH a b ≠ 0 :=
    (universalH_pos ha hb).ne'
  have hc : 0 ≤ 2 * universalUnequalC a b :=
    (mul_pos (by norm_num) (universalUnequalC_pos ha hb)).le
  have hbase :
      0 ≤ 1 + t * universalCenteredVariable a b θ :=
    (one_add_centered_pos ha hb ht θ).le
  unfold universalKernel universalExponent universalP
  rw [universalB_centeredPath_zero hh θ]
  exact Real.mul_rpow hc hbase

/--
The posterior identity says that the kernel-weighted centered residual
`θ-r` has integral zero.
-/
theorem UniversalPosteriorIdentity.integral_theta_sub_mul_kernel_eq_zero
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b r q : ℝ}
    (H : UniversalPosteriorIdentity ν a b)
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q) :
    (∫ θ : UniversalTheta,
        ((θ : ℝ) - r) * universalKernel a b r q θ ∂ν) = 0 := by
  have hnum :=
    H.numerator_eq_mul_denominator ha hb hr0 hr1 hq
  have hnumInt :
      Integrable
        (fun θ : UniversalTheta =>
          (θ : ℝ) * universalKernel a b r q θ) ν :=
    integrable_universalNumeratorKernel ν ha hb hr0 hr1 hq
  have hdenInt :
      Integrable
        (fun θ : UniversalTheta =>
          universalKernel a b r q θ) ν :=
    integrable_universalKernel ν ha hb hr0 hr1 hq
  calc
    (∫ θ : UniversalTheta,
        ((θ : ℝ) - r) * universalKernel a b r q θ ∂ν)
        =
      ∫ θ : UniversalTheta,
        (θ : ℝ) * universalKernel a b r q θ
          - r * universalKernel a b r q θ ∂ν := by
            apply integral_congr_ae
            filter_upwards with θ
            ring
    _ =
      (∫ θ : UniversalTheta,
          (θ : ℝ) * universalKernel a b r q θ ∂ν)
        - ∫ θ : UniversalTheta,
          r * universalKernel a b r q θ ∂ν := by
            rw [integral_sub hnumInt (hdenInt.const_mul r)]
    _ =
      universalPosteriorNumerator ν a b r q
        - r * universalPosteriorDenominator ν a b r q := by
          rw [integral_const_mul]
          rfl
    _ = 0 := by
      rw [hnum]
      ring

/--
Pointwise relation between the original posterior residual and the
normalized centered residual.
-/
theorem theta_sub_path_mul_kernel_eq_centeredResidual
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : |t| < 1 / universalH a b)
    (θ : UniversalTheta) :
    ((θ : ℝ) - universalCenteredPath a b t)
        * universalKernel a b (universalCenteredPath a b t) 0 θ
      =
    ((2 * universalUnequalC a b) ^ (-universalP a b)
        / universalH a b)
      * universalCenteredResidual a b t θ := by
  have hh : universalH a b ≠ 0 :=
    (universalH_pos ha hb).ne'
  rw [theta_sub_centeredPath_eq hh θ,
    universalKernel_centeredPath_zero ha hb ht θ]
  unfold universalCenteredResidual
  ring

/--
The posterior identity gives the normalized centered residual identity in
an explicit open neighborhood of zero.
-/
theorem UniversalPosteriorIdentity.centeredResidualIntegral_eq_zero
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b t : ℝ}
    (H : UniversalPosteriorIdentity ν a b)
    (ha : 0 < a) (hb : 0 < b)
    (ht : |t| < 1 / universalH a b) :
    universalCenteredResidualIntegral ν a b t = 0 := by
  have hr0 :
      0 < universalCenteredPath a b t :=
    universalCenteredPath_pos ha hb ht
  have hr1 :
      universalCenteredPath a b t < 1 :=
    universalCenteredPath_lt_one ha hb ht
  have hraw :=
    H.integral_theta_sub_mul_kernel_eq_zero
      ha hb hr0 hr1 (show 0 ≤ (0 : ℝ) from le_rfl)
  have hscale :
      (2 * universalUnequalC a b) ^ (-universalP a b)
          / universalH a b ≠ 0 := by
    apply div_ne_zero
    · exact ne_of_gt
        (Real.rpow_pos_of_pos
          (mul_pos (by norm_num)
            (universalUnequalC_pos ha hb)) _)
    · exact (universalH_pos ha hb).ne'
  have hrewrite :
      (∫ θ : UniversalTheta,
          ((θ : ℝ) - universalCenteredPath a b t)
            * universalKernel a b
                (universalCenteredPath a b t) 0 θ ∂ν)
        =
      ((2 * universalUnequalC a b) ^ (-universalP a b)
          / universalH a b)
        * universalCenteredResidualIntegral ν a b t := by
    calc
      (∫ θ : UniversalTheta,
          ((θ : ℝ) - universalCenteredPath a b t)
            * universalKernel a b
                (universalCenteredPath a b t) 0 θ ∂ν)
          =
        ∫ θ : UniversalTheta,
          ((2 * universalUnequalC a b) ^ (-universalP a b)
              / universalH a b)
            * universalCenteredResidual a b t θ ∂ν := by
          apply integral_congr_ae
          filter_upwards with θ
          exact theta_sub_path_mul_kernel_eq_centeredResidual
            ha hb ht θ
      _ =
        ((2 * universalUnequalC a b) ^ (-universalP a b)
            / universalH a b)
          * universalCenteredResidualIntegral ν a b t := by
            rw [integral_const_mul]
            rfl
  rw [hrewrite] at hraw
  exact (mul_eq_zero.mp hraw).resolve_left hscale

theorem UniversalPosteriorIdentity.centeredResidualIntegral_eventuallyEq_zero
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b : ℝ}
    (H : UniversalPosteriorIdentity ν a b)
    (ha : 0 < a) (hb : 0 < b) :
    universalCenteredResidualIntegral ν a b
      =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 := by
  have hh : 0 < 1 / universalH a b := by
    exact one_div_pos.mpr (universalH_pos ha hb)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hh] with t ht
  have habs : |t| < 1 / universalH a b := by
    simpa [Real.dist_eq] using ht
  exact H.centeredResidualIntegral_eq_zero ha hb habs

theorem UniversalPosteriorIdentity.centeredTaylor0_eq_zero
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b t : ℝ}
    (H : UniversalPosteriorIdentity ν a b)
    (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ universalUnequalLocalSet a b) :
    universalCenteredTaylor0 ν a b t = 0 := by
  have hh : 0 < universalH a b := universalH_pos ha hb
  have htabs :=
    abs_lt_local_radius_of_mem_universalUnequalLocalSet ht
  have hradius :
      1 / (2 * universalH a b) < 1 / universalH a b := by
    calc
      1 / (2 * universalH a b)
          = (1 / 2 : ℝ) / universalH a b := by
              field_simp [hh.ne']
      _ < 1 / universalH a b := by
        exact div_lt_div_of_pos_right (by norm_num) hh
  rw [← universalCenteredResidualIntegral_eq_taylor0
    ν ha hb ht]
  exact H.centeredResidualIntegral_eq_zero ha hb
    (htabs.trans hradius)

/--
The full posterior identity supplies all three ODE/Taylor moments required
by the unequal obstruction algebra.
-/
theorem UniversalPosteriorIdentity.odeMoments
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b : ℝ}
    (H : UniversalPosteriorIdentity ν a b)
    (ha : 0 < a) (hb : 0 < b) :
    UniversalUnequalOdeMoments ν a b :=
  universalUnequalOdeMoments_of_taylor0 ha hb
    (fun _ ht => H.centeredTaylor0_eq_zero ha hb ht)

/--
Direct connection to the algebraic obstruction theorem: once the
quotient-rule layer identifies the `q` derivative with the centered cubic
moment, the posterior identity forces the explicit unequal coefficient.
-/
theorem UniversalPosteriorIdentity.qDerivative_eq_obstruction
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b derivative : ℝ}
    (H : UniversalPosteriorIdentity ν a b)
    (ha : 0 < a) (hb : 0 < b)
    (hderivative :
      derivative =
        universalQDerivativeFromMoment a b
          (universalCenteredIntegrandMoment a b
            (universalCenteredMoment ν a b 1)
            (universalCenteredMoment ν a b 2)
            (universalCenteredMoment ν a b 3))) :
    derivative = universalUnequalObstruction a b := by
  let hm := H.odeMoments ha hb
  exact universalUnequal_qDerivative_of_odeMoments
    ha hb hm.first hm.second hm.third hderivative

/--
At unequal positive shapes, the posterior moment bridge is incompatible
with a zero `q` derivative.
-/
theorem UniversalPosteriorIdentity.no_zero_qDerivative
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a b derivative : ℝ}
    (H : UniversalPosteriorIdentity ν a b)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hzero : derivative = 0)
    (hderivative :
      derivative =
        universalQDerivativeFromMoment a b
          (universalCenteredIntegrandMoment a b
            (universalCenteredMoment ν a b 1)
            (universalCenteredMoment ν a b 2)
            (universalCenteredMoment ν a b 3))) :
    False :=
  universalUnequal_no_zero_qDerivative ha hb hab hzero
    (H.qDerivative_eq_obstruction ha hb hderivative)

end

end GraybillDeal
