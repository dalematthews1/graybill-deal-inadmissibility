import GraybillDeal.UniversalEqualMomentBridge
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-!
# The `q`-direction contradiction in the equal-size universal argument

This file closes the analytic contradiction for the equal-size branch.
Write

`x = r - 1/2`, `z = θ - 1/2`, `t = θ(1-θ) = 1/4-z²`,

and normalize the physical coordinate by `q = a s`.  Then

`B(a,a,1/2+x,as,θ) = a(1-4xz+st)`.

The posterior identity says that

`R(x,s) = ∫ (z-x)(1-4xz+st)⁻ᵖ dν = 0`

for `s ≥ 0`.  A right derivative at `s=0` gives

`Q(x) = ∫ (z-x)t(1-4xz)⁻ᵖ⁻¹ dν = 0`.

Differentiating this identity in `x` at zero gives

`-E[t] + 4(p+1)E[z²t] = 0`.

After multiplication by `-p/a`, this is exactly the assertion that the
mixed coefficient defined in `UniversalEqualAlgebra` vanishes.  The moment
bridge proves that the same coefficient is strictly positive.
-/

namespace GraybillDeal

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

noncomputable section

/-- The elementary factor `t = θ(1-θ)`. -/
def universalEqualT (θ : UniversalTheta) : ℝ :=
  (θ : ℝ) * (1 - (θ : ℝ))

/-- The normalized base after writing the physical coordinate as `q = a s`. -/
def universalEqualQBase
    (x s : ℝ) (θ : UniversalTheta) : ℝ :=
  universalEqualBase x θ + s * universalEqualT θ

/-- The fixed neighborhood used to differentiate in the normalized
`q` coordinate. -/
def universalEqualQLocalSet : Set ℝ :=
  Ioo (-1) 1

/-- The normalized posterior residual. -/
def universalEqualResidualQTerm
    (p x s : ℝ) (θ : UniversalTheta) : ℝ :=
  (universalEqualZ θ - x)
    * universalEqualQBase x s θ ^ (-p)

/-- Its pointwise derivative with respect to `s`. -/
def universalEqualResidualQDerivativeTerm
    (p x s : ℝ) (θ : UniversalTheta) : ℝ :=
  (-p) * (universalEqualZ θ - x) * universalEqualT θ
    * universalEqualQBase x s θ ^ (-p - 1)

/-- Integral of the normalized posterior residual. -/
def universalEqualResidualQIntegral
    (ν : Measure UniversalTheta) (p x s : ℝ) : ℝ :=
  ∫ θ, universalEqualResidualQTerm p x s θ ∂ν

/-- The first `q`-variation after the harmless factor `-p` is removed. -/
def universalEqualQBalance
    (ν : Measure UniversalTheta) (p x : ℝ) : ℝ :=
  ∫ θ,
    (universalEqualZ θ - x) * universalEqualT θ
      * universalEqualBase x θ ^ (-p - 1) ∂ν

theorem universalEqualT_nonneg (θ : UniversalTheta) :
    0 ≤ universalEqualT θ := by
  unfold universalEqualT
  exact mul_nonneg θ.property.1 (sub_nonneg.mpr θ.property.2)

theorem universalEqualT_le_quarter (θ : UniversalTheta) :
    universalEqualT θ ≤ 1 / 4 := by
  unfold universalEqualT
  nlinarith [sq_nonneg ((θ : ℝ) - 1 / 2)]

theorem universalEqualT_le_one (θ : UniversalTheta) :
    universalEqualT θ ≤ 1 := by
  exact (universalEqualT_le_quarter θ).trans (by norm_num)

theorem continuous_universalEqualT :
    Continuous universalEqualT := by
  unfold universalEqualT
  fun_prop

theorem zero_mem_universalEqualQLocalSet :
    (0 : ℝ) ∈ universalEqualQLocalSet := by
  unfold universalEqualQLocalSet
  norm_num

theorem abs_lt_one_of_mem_universalEqualQLocalSet
    {s : ℝ} (hs : s ∈ universalEqualQLocalSet) :
    |s| < 1 := by
  unfold universalEqualQLocalSet at hs
  rw [abs_lt]
  exact hs

theorem abs_universalEqualZ_sub_x_le_one
    {x : ℝ} (hx : x ∈ universalEqualLocalSet)
    (θ : UniversalTheta) :
    |universalEqualZ θ - x| ≤ 1 := by
  have hz := abs_universalEqualZ_le_half θ
  have hx' := abs_lt_eighth_of_mem_universalEqualLocalSet hx
  apply le_of_lt
  calc
    |universalEqualZ θ - x|
        ≤ |universalEqualZ θ| + |x| := abs_sub _ _
    _ < 1 / 2 + 1 / 8 := add_lt_add_of_le_of_lt hz hx'
    _ < 1 := by norm_num

/-- Uniform positivity of the normalized two-variable base. -/
theorem universalEqualQBase_ge_quarter
    {x s : ℝ}
    (hx : x ∈ universalEqualLocalSet)
    (hs : s ∈ universalEqualQLocalSet)
    (θ : UniversalTheta) :
    1 / 4 ≤ universalEqualQBase x s θ := by
  have hsabs : |s| ≤ 1 :=
    le_of_lt (abs_lt_one_of_mem_universalEqualQLocalSet hs)
  have ht0 := universalEqualT_nonneg θ
  have ht4 := universalEqualT_le_quarter θ
  have hst :
      |s * universalEqualT θ| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_nonneg ht0]
    calc
      |s| * universalEqualT θ
          ≤ 1 * universalEqualT θ :=
        mul_le_mul_of_nonneg_right hsabs ht0
      _ ≤ 1 / 4 := by simpa using ht4
  have hbase := universalEqualBase_ge_half hx θ
  unfold universalEqualQBase
  nlinarith [neg_abs_le (s * universalEqualT θ)]

theorem universalEqualQBase_pos
    {x s : ℝ}
    (hx : x ∈ universalEqualLocalSet)
    (hs : s ∈ universalEqualQLocalSet)
    (θ : UniversalTheta) :
    0 < universalEqualQBase x s θ :=
  lt_of_lt_of_le (by norm_num)
    (universalEqualQBase_ge_quarter hx hs θ)

theorem continuous_universalEqualQBase_theta (x s : ℝ) :
    Continuous (fun θ : UniversalTheta =>
      universalEqualQBase x s θ) := by
  unfold universalEqualQBase
  exact (continuous_universalEqualBase_theta x).add
    (continuous_const.mul continuous_universalEqualT)

theorem continuous_universalEqualResidualQTerm_theta
    {p x s : ℝ}
    (hx : x ∈ universalEqualLocalSet)
    (hs : s ∈ universalEqualQLocalSet) :
    Continuous (fun θ : UniversalTheta =>
      universalEqualResidualQTerm p x s θ) := by
  unfold universalEqualResidualQTerm
  exact
    (continuous_universalEqualZ.sub continuous_const).mul
      ((continuous_universalEqualQBase_theta x s).rpow_const
        (fun θ => Or.inl
          (ne_of_gt (universalEqualQBase_pos hx hs θ))))

theorem continuous_universalEqualResidualQDerivativeTerm_theta
    {p x s : ℝ}
    (hx : x ∈ universalEqualLocalSet)
    (hs : s ∈ universalEqualQLocalSet) :
    Continuous (fun θ : UniversalTheta =>
      universalEqualResidualQDerivativeTerm p x s θ) := by
  unfold universalEqualResidualQDerivativeTerm
  exact
    (((continuous_const.mul
      (continuous_universalEqualZ.sub continuous_const)).mul
        continuous_universalEqualT).mul
      ((continuous_universalEqualQBase_theta x s).rpow_const
        (fun θ => Or.inl
          (ne_of_gt (universalEqualQBase_pos hx hs θ)))))

/-- Pointwise derivative with respect to the normalized `q` coordinate. -/
theorem hasDerivAt_universalEqualResidualQTerm
    {p x s : ℝ}
    (hx : x ∈ universalEqualLocalSet)
    (hs : s ∈ universalEqualQLocalSet)
    (θ : UniversalTheta) :
    HasDerivAt
      (fun y => universalEqualResidualQTerm p x y θ)
      (universalEqualResidualQDerivativeTerm p x s θ) s := by
  have hbase :
      HasDerivAt
        (fun y : ℝ => universalEqualQBase x y θ)
        (universalEqualT θ) s := by
    simpa [universalEqualQBase] using!
      ((hasDerivAt_id s).mul_const
        (universalEqualT θ)).const_add
          (universalEqualBase x θ)
  have hpow :
      HasDerivAt
        (fun y : ℝ => universalEqualQBase x y θ ^ (-p))
        (universalEqualT θ * (-p)
          * universalEqualQBase x s θ ^ (-p - 1)) s :=
    hbase.rpow_const
      (Or.inl (ne_of_gt
        (universalEqualQBase_pos hx hs θ)))
  have h :=
    hpow.const_mul (universalEqualZ θ - x)
  simpa only [universalEqualResidualQTerm,
    universalEqualResidualQDerivativeTerm] using!
    h.congr_deriv (by ring)

/-- A constant local majorant for the normalized `q` derivative. -/
theorem norm_universalEqualResidualQDerivativeTerm_le
    {p x s : ℝ}
    (hp : 0 < p)
    (hx : x ∈ universalEqualLocalSet)
    (hs : s ∈ universalEqualQLocalSet)
    (θ : UniversalTheta) :
    ‖universalEqualResidualQDerivativeTerm p x s θ‖
      ≤ p * (1 / 4 : ℝ) ^ (-p - 1) := by
  have hz := abs_universalEqualZ_sub_x_le_one hx θ
  have ht0 := universalEqualT_nonneg θ
  have ht1 := universalEqualT_le_one θ
  have hqpow :
      universalEqualQBase x s θ ^ (-p - 1)
        ≤ (1 / 4 : ℝ) ^ (-p - 1) := by
    exact Real.rpow_le_rpow_of_nonpos
      (by norm_num)
      (universalEqualQBase_ge_quarter hx hs θ)
      (by linarith)
  have hqpow0 :
      0 ≤ universalEqualQBase x s θ ^ (-p - 1) :=
    Real.rpow_nonneg
      (le_trans (by norm_num)
        (universalEqualQBase_ge_quarter hx hs θ)) _
  have hquarterpow0 :
      0 ≤ (1 / 4 : ℝ) ^ (-p - 1) :=
    Real.rpow_nonneg (by norm_num) _
  unfold universalEqualResidualQDerivativeTerm
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
    abs_neg, abs_of_pos hp, abs_of_nonneg ht0,
    abs_of_nonneg hqpow0]
  calc
    p * |universalEqualZ θ - x| * universalEqualT θ
          * universalEqualQBase x s θ ^ (-p - 1)
        ≤ p * 1 * 1
          * universalEqualQBase x s θ ^ (-p - 1) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul
                (mul_le_mul_of_nonneg_left hz hp.le)
                ht1
                (universalEqualT_nonneg θ)
                (mul_nonneg hp.le (by norm_num)))
              hqpow0
    _ ≤ p * 1 * 1 * (1 / 4 : ℝ) ^ (-p - 1) := by
      exact mul_le_mul_of_nonneg_left hqpow
        (mul_nonneg
          (mul_nonneg hp.le (by norm_num))
          (by norm_num))
    _ = p * (1 / 4 : ℝ) ^ (-p - 1) := by ring

/--
Differentiation under the probability integral in the normalized
`q` coordinate.
-/
theorem hasDerivAt_universalEqualResidualQIntegral
    (ν : Measure UniversalTheta) [IsFiniteMeasure ν]
    {p x s : ℝ}
    (hp : 0 < p)
    (hx : x ∈ universalEqualLocalSet)
    (hs : s ∈ universalEqualQLocalSet) :
    HasDerivAt
      (universalEqualResidualQIntegral ν p x)
      (∫ θ,
        universalEqualResidualQDerivativeTerm p x s θ ∂ν) s := by
  have hset : universalEqualQLocalSet ∈ 𝓝 s :=
    isOpen_Ioo.mem_nhds hs
  have hFmeas :
      ∀ᶠ y in 𝓝 s,
        AEStronglyMeasurable
          (fun θ : UniversalTheta =>
            universalEqualResidualQTerm p x y θ) ν := by
    filter_upwards [hset] with y hy
    exact
      (continuous_universalEqualResidualQTerm_theta
        hx hy).aestronglyMeasurable
  have hFint :
      Integrable
        (fun θ : UniversalTheta =>
          universalEqualResidualQTerm p x s θ) ν := by
    let f : UniversalTheta →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact
        ⟨fun θ : UniversalTheta =>
            universalEqualResidualQTerm p x s θ,
          continuous_universalEqualResidualQTerm_theta hx hs⟩
    change Integrable (f : UniversalTheta → ℝ) ν
    exact BoundedContinuousFunction.integrable ν f
  have hF'meas :
      AEStronglyMeasurable
        (fun θ : UniversalTheta =>
          universalEqualResidualQDerivativeTerm p x s θ) ν :=
    (continuous_universalEqualResidualQDerivativeTerm_theta
      hx hs).aestronglyMeasurable
  have hbound :
      ∀ᵐ θ ∂ν, ∀ y ∈ universalEqualQLocalSet,
        ‖universalEqualResidualQDerivativeTerm p x y θ‖
          ≤ p * (1 / 4 : ℝ) ^ (-p - 1) := by
    exact ae_of_all ν fun θ y hy =>
      norm_universalEqualResidualQDerivativeTerm_le
        hp hx hy θ
  have hboundint :
      Integrable
        (fun _ : UniversalTheta =>
          p * (1 / 4 : ℝ) ^ (-p - 1)) ν :=
    integrable_const _
  have hdiff :
      ∀ᵐ θ ∂ν, ∀ y ∈ universalEqualQLocalSet,
        HasDerivAt
          (fun z => universalEqualResidualQTerm p x z θ)
          (universalEqualResidualQDerivativeTerm p x y θ)
          y := by
    exact ae_of_all ν fun θ y hy =>
      hasDerivAt_universalEqualResidualQTerm hx hy θ
  exact
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun y θ =>
        universalEqualResidualQTerm p x y θ)
      (F' := fun y θ =>
        universalEqualResidualQDerivativeTerm p x y θ)
      (bound := fun _ : UniversalTheta =>
        p * (1 / 4 : ℝ) ^ (-p - 1))
      hset hFmeas hFint hF'meas hbound hboundint hdiff).2

/-- The exact factorization after the substitution `q = a s`. -/
theorem universalB_equal_qcentered
    (a x s : ℝ) (θ : UniversalTheta) :
    universalB a a (1 / 2 + x) (a * s) θ
      = a * universalEqualQBase x s θ := by
  unfold universalB universalEqualQBase universalEqualBase
    universalEqualZ universalEqualT
  ring

theorem universalKernel_equal_qcentered
    {a x s : ℝ}
    (ha : 0 < a)
    (hx : x ∈ universalEqualLocalSet)
    (hs : s ∈ universalEqualQLocalSet)
    (θ : UniversalTheta) :
    universalKernel a a (1 / 2 + x) (a * s) θ
      =
    a ^ (-universalEqualExponent a)
      * universalEqualQBase x s θ
          ^ (-universalEqualExponent a) := by
  unfold universalKernel universalExponent universalEqualExponent
  rw [universalB_equal_qcentered]
  rw [Real.mul_rpow ha.le
    (universalEqualQBase_pos hx hs θ).le]
  congr 2 <;> ring

/--
The posterior identity says that its kernel-weighted residual has integral
zero.  This division-free form is convenient at `q=0`.
-/
theorem UniversalPosteriorIdentity.equal_integral_residual_eq_zero
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a r q : ℝ}
    (H : UniversalPosteriorIdentity ν a a)
    (ha : 0 < a)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q) :
    (∫ θ : UniversalTheta,
      ((θ : ℝ) - r) * universalKernel a a r q θ ∂ν) = 0 := by
  have hnum :=
    H.numerator_eq_mul_denominator ha ha hr0 hr1 hq
  have hnumInt :
      Integrable
        (fun θ : UniversalTheta =>
          (θ : ℝ) * universalKernel a a r q θ) ν :=
    integrable_universalNumeratorKernel ν ha ha hr0 hr1 hq
  have hdenInt :
      Integrable
        (fun θ : UniversalTheta =>
          universalKernel a a r q θ) ν :=
    integrable_universalKernel ν ha ha hr0 hr1 hq
  calc
    (∫ θ : UniversalTheta,
      ((θ : ℝ) - r) * universalKernel a a r q θ ∂ν)
        =
      ∫ θ : UniversalTheta,
        (θ : ℝ) * universalKernel a a r q θ
          - r * universalKernel a a r q θ ∂ν := by
            apply integral_congr_ae
            filter_upwards with θ
            ring
    _ =
      (∫ θ : UniversalTheta,
        (θ : ℝ) * universalKernel a a r q θ ∂ν)
        -
      ∫ θ : UniversalTheta,
        r * universalKernel a a r q θ ∂ν := by
          rw [integral_sub hnumInt (hdenInt.const_mul r)]
    _ =
      universalPosteriorNumerator ν a a r q
        - r * universalPosteriorDenominator ν a a r q := by
          rw [integral_const_mul]
          rfl
    _ = 0 := by
      rw [hnum]
      ring

/--
After removing the positive constant `a⁻ᵖ`, the posterior residual is the
normalized residual `R(x,s)`.
-/
theorem UniversalPosteriorIdentity.equal_residualQIntegral_eq_zero
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a x s : ℝ}
    (H : UniversalPosteriorIdentity ν a a)
    (ha : 0 < a)
    (hx : x ∈ universalEqualLocalSet)
    (hsLocal : s ∈ universalEqualQLocalSet)
    (hs0 : 0 ≤ s) :
    universalEqualResidualQIntegral ν
      (universalEqualExponent a) x s = 0 := by
  have hxabs := abs_lt_eighth_of_mem_universalEqualLocalSet hx
  rcases abs_lt.mp hxabs with ⟨hxl, hxu⟩
  have hr0 : 0 < 1 / 2 + x := by linarith
  have hr1 : 1 / 2 + x < 1 := by linarith
  have hq0 : 0 ≤ a * s := mul_nonneg ha.le hs0
  have hraw :=
    H.equal_integral_residual_eq_zero
      ha hr0 hr1 hq0
  let p := universalEqualExponent a
  let c := a ^ (-p)
  have hc : c ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ha _)
  have hpoint (θ : UniversalTheta) :
      ((θ : ℝ) - (1 / 2 + x))
          * universalKernel a a (1 / 2 + x) (a * s) θ
        =
      c * universalEqualResidualQTerm p x s θ := by
    rw [universalKernel_equal_qcentered ha hx hsLocal θ]
    unfold universalEqualResidualQTerm universalEqualZ
    simp only [p, c]
    ring
  have hrewrite :
      (∫ θ : UniversalTheta,
        ((θ : ℝ) - (1 / 2 + x))
          * universalKernel a a (1 / 2 + x) (a * s) θ ∂ν)
        =
      c * universalEqualResidualQIntegral ν p x s := by
    calc
      (∫ θ : UniversalTheta,
        ((θ : ℝ) - (1 / 2 + x))
          * universalKernel a a (1 / 2 + x) (a * s) θ ∂ν)
          =
        ∫ θ : UniversalTheta,
          c * universalEqualResidualQTerm p x s θ ∂ν := by
            apply integral_congr_ae
            filter_upwards with θ
            exact hpoint θ
      _ =
        c * universalEqualResidualQIntegral ν p x s := by
          rw [integral_const_mul]
          rfl
  rw [hrewrite] at hraw
  exact (mul_eq_zero.mp hraw).resolve_left hc

theorem universalEqualResidualQDerivativeIntegral_zero
    (ν : Measure UniversalTheta) (p x : ℝ) :
    (∫ θ,
      universalEqualResidualQDerivativeTerm p x 0 θ ∂ν)
      =
    (-p) * universalEqualQBalance ν p x := by
  have hpoint :
      (fun θ : UniversalTheta =>
        universalEqualResidualQDerivativeTerm p x 0 θ)
        =
      (fun θ : UniversalTheta =>
        (-p) *
          ((universalEqualZ θ - x) * universalEqualT θ
            * universalEqualBase x θ ^ (-p - 1))) := by
    funext θ
    unfold universalEqualResidualQDerivativeTerm
      universalEqualQBase
    simp only [zero_mul, add_zero]
    ring
  rw [hpoint, integral_const_mul]
  rfl

/--
The one-sided `s ≥ 0` posterior identity, together with the ordinary
two-sided derivative of its analytic extension, forces the first
`q`-variation to vanish.
-/
theorem UniversalPosteriorIdentity.equal_qBalance_eq_zero
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a x : ℝ}
    (H : UniversalPosteriorIdentity ν a a)
    (ha : 0 < a)
    (hx : x ∈ universalEqualLocalSet) :
    universalEqualQBalance ν (universalEqualExponent a) x = 0 := by
  let p := universalEqualExponent a
  have hp : 0 < p := by
    dsimp only [p]
    exact universalEqualExponent_pos ha
  have hlocal :
      universalEqualQLocalSet
        ∈ 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds
      (isOpen_Ioo.mem_nhds zero_mem_universalEqualQLocalSet)
  have heq :
      universalEqualResidualQIntegral ν p x
        =ᶠ[𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)]
      fun _ => 0 := by
    filter_upwards [hlocal, self_mem_nhdsWithin] with s hsLocal hs0
    exact H.equal_residualQIntegral_eq_zero
      ha hx hsLocal hs0
  have hderiv :
      HasDerivAt
        (universalEqualResidualQIntegral ν p x)
        (∫ θ,
          universalEqualResidualQDerivativeTerm p x 0 θ ∂ν) 0 :=
    hasDerivAt_universalEqualResidualQIntegral ν
      hp hx zero_mem_universalEqualQLocalSet
  have hconstWithDerivative :
      HasDerivWithinAt
        (fun _ : ℝ => 0)
        (∫ θ,
          universalEqualResidualQDerivativeTerm p x 0 θ ∂ν)
        (Set.Ici 0) 0 :=
    hderiv.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
      heq.symm self_mem_Ici
  have hderivativeZero :
      (∫ θ,
        universalEqualResidualQDerivativeTerm p x 0 θ ∂ν) = 0 :=
    UniqueDiffWithinAt.eq_deriv (Set.Ici 0)
      (uniqueDiffWithinAt_Ici 0)
      hconstWithDerivative
      (hasDerivWithinAt_const
        (x := (0 : ℝ)) (s := Set.Ici 0) (c := (0 : ℝ)))
  rw [universalEqualResidualQDerivativeIntegral_zero] at hderivativeZero
  exact (mul_eq_zero.mp hderivativeZero).resolve_left
    (neg_ne_zero.mpr hp.ne')

/-- A finite algebraic decomposition of `Q(x)` into the centered term
family already differentiated in `UniversalEqualMomentBridge`. -/
def universalEqualQBalanceExpression
    (ν : Measure UniversalTheta) (p x : ℝ) : ℝ :=
  (1 / 4) * universalEqualTermIntegral ν 1 1 (-p - 1) x
    - universalEqualTermIntegral ν 1 3 (-p - 1) x
    - x * ((1 / 4)
        * universalEqualTermIntegral ν 1 0 (-p - 1) x
      - universalEqualTermIntegral ν 1 2 (-p - 1) x)

theorem integrable_universalEqualTerm
    (ν : Measure UniversalTheta) [IsFiniteMeasure ν]
    {c e x : ℝ} {n : ℕ}
    (hx : x ∈ universalEqualLocalSet) :
    Integrable
      (fun θ : UniversalTheta =>
        universalEqualTerm c n e x θ) ν := by
  let f : UniversalTheta →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun θ : UniversalTheta =>
          universalEqualTerm c n e x θ,
        continuous_universalEqualTerm_theta hx⟩
  change Integrable (f : UniversalTheta → ℝ) ν
  exact BoundedContinuousFunction.integrable ν f

theorem universalEqualQBalance_eq_expression
    (ν : Measure UniversalTheta) [IsFiniteMeasure ν]
    {p x : ℝ}
    (hx : x ∈ universalEqualLocalSet) :
    universalEqualQBalance ν p x
      = universalEqualQBalanceExpression ν p x := by
  let f0 := fun θ : UniversalTheta =>
    universalEqualTerm 1 0 (-p - 1) x θ
  let f1 := fun θ : UniversalTheta =>
    universalEqualTerm 1 1 (-p - 1) x θ
  let f2 := fun θ : UniversalTheta =>
    universalEqualTerm 1 2 (-p - 1) x θ
  let f3 := fun θ : UniversalTheta =>
    universalEqualTerm 1 3 (-p - 1) x θ
  have h0 : Integrable f0 ν := by
    dsimp only [f0]
    exact integrable_universalEqualTerm ν hx
  have h1 : Integrable f1 ν := by
    dsimp only [f1]
    exact integrable_universalEqualTerm ν hx
  have h2 : Integrable f2 ν := by
    dsimp only [f2]
    exact integrable_universalEqualTerm ν hx
  have h3 : Integrable f3 ν := by
    dsimp only [f3]
    exact integrable_universalEqualTerm ν hx
  have hpoint :
      (fun θ : UniversalTheta =>
        (universalEqualZ θ - x) * universalEqualT θ
          * universalEqualBase x θ ^ (-p - 1))
        =
      (fun θ : UniversalTheta =>
        (1 / 4) * f1 θ - f3 θ
          - x * ((1 / 4) * f0 θ - f2 θ)) := by
    funext θ
    dsimp only [f0, f1, f2, f3]
    unfold universalEqualT universalEqualTerm universalEqualZ
    ring
  have hAint :
      (∫ θ : UniversalTheta,
        (1 / 4) * f1 θ - f3 θ ∂ν)
        =
      (1 / 4) * (∫ θ : UniversalTheta, f1 θ ∂ν)
        - ∫ θ : UniversalTheta, f3 θ ∂ν := by
    rw [integral_sub (h1.const_mul (1 / 4)) h3,
      integral_const_mul]
  have hGint :
      (∫ θ : UniversalTheta,
        x * ((1 / 4) * f0 θ - f2 θ) ∂ν)
        =
      x * ((1 / 4) * (∫ θ : UniversalTheta, f0 θ ∂ν)
        - ∫ θ : UniversalTheta, f2 θ ∂ν) := by
    rw [integral_const_mul,
      integral_sub (h0.const_mul (1 / 4)) h2,
      integral_const_mul]
  unfold universalEqualQBalance
  rw [hpoint]
  unfold universalEqualQBalanceExpression
    universalEqualTermIntegral
  calc
    (∫ θ : UniversalTheta,
      (1 / 4) * f1 θ - f3 θ
        - x * ((1 / 4) * f0 θ - f2 θ) ∂ν)
        =
      (∫ θ : UniversalTheta,
        (1 / 4) * f1 θ - f3 θ ∂ν)
        -
      ∫ θ : UniversalTheta,
        x * ((1 / 4) * f0 θ - f2 θ) ∂ν := by
          exact integral_sub
            ((h1.const_mul (1 / 4)).sub h3)
            ((h0.const_mul (1 / 4)).sub h2 |>.const_mul x)
    _ =
      ((1 / 4) * ∫ θ : UniversalTheta, f1 θ ∂ν)
        - (∫ θ : UniversalTheta, f3 θ ∂ν)
        - x * (((1 / 4) * ∫ θ : UniversalTheta, f0 θ ∂ν)
          - ∫ θ : UniversalTheta, f2 θ ∂ν) := by
            rw [hAint, hGint]
    _ =
      (1 / 4) *
          (∫ θ, universalEqualTerm 1 1 (-p - 1) x θ ∂ν)
        - (∫ θ, universalEqualTerm 1 3 (-p - 1) x θ ∂ν)
        - x * ((1 / 4)
            * (∫ θ, universalEqualTerm 1 0 (-p - 1) x θ ∂ν)
          - (∫ θ,
              universalEqualTerm 1 2 (-p - 1) x θ ∂ν)) := by
            rfl

theorem universalEqualTermIntegral_zero
    (ν : Measure UniversalTheta)
    (c e : ℝ) (n : ℕ) :
    universalEqualTermIntegral ν c n e 0
      =
    c * universalEqualCenteredMoment ν n := by
  unfold universalEqualTermIntegral universalEqualTerm
    universalEqualCenteredMoment universalEqualBase
  simp only [mul_zero, zero_mul, sub_zero, Real.one_rpow, mul_one]
  rw [integral_const_mul]

/-- The derivative of `Q` at the center, written in terms of the second
and fourth centered moments. -/
def universalEqualQCenterDerivative
    (p m₂ m₄ : ℝ) : ℝ :=
  -1 / 4 + (p + 2) * m₂ - 4 * (p + 1) * m₄

theorem universalEqualCenteredMoment_zero
    (ν : Measure UniversalTheta) [IsProbabilityMeasure ν] :
    universalEqualCenteredMoment ν 0 = 1 := by
  simp [universalEqualCenteredMoment]

/-- The finite decomposition of `Q` is differentiable at zero, and its
derivative is the advertised moment expression. -/
theorem hasDerivAt_universalEqualQBalanceExpression
    (ν : Measure UniversalTheta) [IsProbabilityMeasure ν]
    {p : ℝ} (hp : 0 < p) :
    HasDerivAt
      (universalEqualQBalanceExpression ν p)
      (universalEqualQCenterDerivative p
        (universalEqualCenteredMoment ν 2)
        (universalEqualCenteredMoment ν 4))
      0 := by
  have hterm (n : ℕ) :
      HasDerivAt
        (universalEqualTermIntegral ν 1 n (-p - 1))
        (universalEqualTermIntegral ν
          (4 * (p + 1)) (n + 1) (-p - 2) 0) 0 := by
    have hcoef :
        -4 * (1 : ℝ) * (-p - 1) = 4 * (p + 1) := by
      ring
    have he : -p - 1 - 1 = -p - 2 := by ring
    simpa only [hcoef, he] using
      (hasDerivAt_universalEqualTermIntegral ν
        (c := 1) (n := n) (e := -p - 1)
        (by norm_num) (by linarith) zero_mem_universalEqualLocalSet)
  have hA :=
    ((hterm 1).const_mul (1 / 4)).sub (hterm 3)
  have hG :=
    ((hterm 0).const_mul (1 / 4)).sub (hterm 2)
  have hproduct :=
    (hasDerivAt_id (0 : ℝ)).mul hG
  have h := hA.sub hproduct
  have hraw :=
    h.congr_of_eventuallyEq
      (show universalEqualQBalanceExpression ν p
          =ᶠ[𝓝 (0 : ℝ)] _ from
        Filter.Eventually.of_forall (fun y => by
          unfold universalEqualQBalanceExpression
          rfl))
  apply hraw.congr_deriv
  simp only [Nat.reduceAdd, id_eq, one_mul, zero_mul, add_zero,
    Pi.sub_apply]
  rw [universalEqualTermIntegral_zero,
    universalEqualTermIntegral_zero,
    universalEqualTermIntegral_zero,
    universalEqualTermIntegral_zero,
    universalEqualCenteredMoment_zero]
  unfold universalEqualQCenterDerivative
  ring

theorem hasDerivAt_universalEqualQBalance
    (ν : Measure UniversalTheta) [IsProbabilityMeasure ν]
    {p : ℝ} (hp : 0 < p) :
    HasDerivAt
      (universalEqualQBalance ν p)
      (universalEqualQCenterDerivative p
        (universalEqualCenteredMoment ν 2)
        (universalEqualCenteredMoment ν 4))
      0 := by
  have heq :
      universalEqualQBalance ν p
        =ᶠ[𝓝 (0 : ℝ)]
      universalEqualQBalanceExpression ν p := by
    filter_upwards
      [isOpen_Ioo.mem_nhds zero_mem_universalEqualLocalSet]
      with x hx
    exact universalEqualQBalance_eq_expression ν hx
  exact
    (hasDerivAt_universalEqualQBalanceExpression ν hp)
      |>.congr_of_eventuallyEq heq

/-- Since `Q` vanishes on an open neighborhood, its center derivative is
zero. -/
theorem UniversalPosteriorIdentity.equal_qCenterDerivative_eq_zero
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a : ℝ}
    (H : UniversalPosteriorIdentity ν a a)
    (ha : 0 < a) :
    universalEqualQCenterDerivative
      (universalEqualExponent a)
      (universalEqualCenteredMoment ν 2)
      (universalEqualCenteredMoment ν 4) = 0 := by
  have heq :
      universalEqualQBalance ν (universalEqualExponent a)
        =ᶠ[𝓝 (0 : ℝ)]
      fun _ => 0 := by
    filter_upwards
      [isOpen_Ioo.mem_nhds zero_mem_universalEqualLocalSet]
      with x hx
    exact H.equal_qBalance_eq_zero ha hx
  have hderiv :=
    hasDerivAt_universalEqualQBalance ν
      (universalEqualExponent_pos ha)
  have hconstWithDerivative :
      HasDerivAt (fun _ : ℝ => 0)
        (universalEqualQCenterDerivative
          (universalEqualExponent a)
          (universalEqualCenteredMoment ν 2)
          (universalEqualCenteredMoment ν 4)) 0 :=
    hderiv.congr_of_eventuallyEq heq.symm
  exact hconstWithDerivative.unique
    (hasDerivAt_const (0 : ℝ) (0 : ℝ))

/-- The derivative identity is exactly the assertion that the mixed
coefficient from `UniversalEqualAlgebra` is zero. -/
theorem UniversalPosteriorIdentity.equal_mixedCoefficient_eq_zero
    {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
    {a : ℝ}
    (H : UniversalPosteriorIdentity ν a a)
    (ha : 0 < a) :
    universalEqualMixedCoefficient
      a (universalEqualExponent a)
      (universalEqualCenteredMoment ν 2)
      (universalEqualCenteredMoment ν 4) = 0 := by
  have hderivative :=
    H.equal_qCenterDerivative_eq_zero ha
  calc
    universalEqualMixedCoefficient
        a (universalEqualExponent a)
        (universalEqualCenteredMoment ν 2)
        (universalEqualCenteredMoment ν 4)
        =
      (-(universalEqualExponent a / a))
        * universalEqualQCenterDerivative
          (universalEqualExponent a)
          (universalEqualCenteredMoment ν 2)
          (universalEqualCenteredMoment ν 4) := by
            unfold universalEqualMixedCoefficient
              universalEqualTFirstMoment
              universalEqualZ2TFirstMoment
              universalEqualQCenterDerivative
            ring
    _ = 0 := by rw [hderivative, mul_zero]

/--
The complete equal-size analytic contradiction: no probability measure can
satisfy the universal posterior identity when the common shape is positive.
-/
theorem UniversalPosteriorIdentity.equal_impossible
    (ν : Measure UniversalTheta) [IsProbabilityMeasure ν]
    {a : ℝ}
    (H : UniversalPosteriorIdentity ν a a)
    (ha : 0 < a) :
    False := by
  exact universalEqual_no_zero_mixedCoefficient
    ha
    (H.equal_quotientIdentities ν ha)
    (H.equal_mixedCoefficient_eq_zero ha)

/-- Negated-existence form of the equal-size contradiction. -/
theorem no_universalPosteriorIdentity_equal
    (ν : Measure UniversalTheta) [IsProbabilityMeasure ν]
    {a : ℝ} (ha : 0 < a) :
    ¬ UniversalPosteriorIdentity ν a a := by
  intro H
  exact H.equal_impossible ν ha

end

end GraybillDeal
