import GraybillDeal.UniversalPosteriorIdentity
import GraybillDeal.UniversalEqualAlgebra
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-!
# Moment bridge for the equal-size universal argument

For equal beta shapes `a = b`, put

`x = r - 1/2`, `z = θ - 1/2`, and `p = 2a + 3/2`.

At `q = 0` the reduced kernel factors as

`a⁻ᵖ (1 - 4xz)⁻ᵖ`.

Consequently the limiting posterior identity is equivalent, locally at
`x = 0`, to

`U(x) = x D(x)`,

where

`D(x) = ∫ (1 - 4xz)⁻ᵖ dν`,

`U(x) = ∫ z (1 - 4xz)⁻ᵖ dν`.

This file differentiates these integrals under the integral sign on the
fixed neighborhood `|x| < 1/8`.  Since `|z| ≤ 1/2`, the base is uniformly
bounded below there.  The derivatives through third order therefore have
an explicit constant integrable majorant.

Differentiating `U = xD` once and three times at zero yields exactly the
two quotient identities consumed by `UniversalEqualAlgebra`.
-/

namespace GraybillDeal

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

noncomputable section

/-- The centered compact parameter coordinate `z = θ - 1/2`. -/
def universalEqualZ (θ : UniversalTheta) : ℝ :=
  (θ : ℝ) - 1 / 2

/-- The normalized equal-size `q = 0` kernel base. -/
def universalEqualBase (x : ℝ) (θ : UniversalTheta) : ℝ :=
  1 - 4 * x * universalEqualZ θ

/--
A common family containing the centered kernel and all derivatives needed
below.  Its derivative with respect to `x` is another member of the family:

`d/dx term(c,n,e) = term(-4ce,n+1,e-1)`.
-/
def universalEqualTerm
    (c : ℝ) (n : ℕ) (e x : ℝ) (θ : UniversalTheta) : ℝ :=
  c * universalEqualZ θ ^ n * universalEqualBase x θ ^ e

/-- Integral of a centered kernel term. -/
def universalEqualTermIntegral
    (ν : Measure UniversalTheta)
    (c : ℝ) (n : ℕ) (e x : ℝ) : ℝ :=
  ∫ θ, universalEqualTerm c n e x θ ∂ν

/-- Centered denominator `D`. -/
def universalEqualD
    (ν : Measure UniversalTheta) (p x : ℝ) : ℝ :=
  universalEqualTermIntegral ν 1 0 (-p) x

/-- First derivative of `D`. -/
def universalEqualD1
    (ν : Measure UniversalTheta) (p x : ℝ) : ℝ :=
  universalEqualTermIntegral ν (4 * p) 1 (-p - 1) x

/-- Second derivative of `D`. -/
def universalEqualD2
    (ν : Measure UniversalTheta) (p x : ℝ) : ℝ :=
  universalEqualTermIntegral ν
    (16 * p * (p + 1)) 2 (-p - 2) x

/-- Third derivative of `D`; only its existence is used. -/
def universalEqualD3
    (ν : Measure UniversalTheta) (p x : ℝ) : ℝ :=
  universalEqualTermIntegral ν
    (64 * p * (p + 1) * (p + 2)) 3 (-p - 3) x

/-- Centered numerator `U`. -/
def universalEqualU
    (ν : Measure UniversalTheta) (p x : ℝ) : ℝ :=
  universalEqualTermIntegral ν 1 1 (-p) x

/-- First derivative of `U`. -/
def universalEqualU1
    (ν : Measure UniversalTheta) (p x : ℝ) : ℝ :=
  universalEqualTermIntegral ν (4 * p) 2 (-p - 1) x

/-- Second derivative of `U`. -/
def universalEqualU2
    (ν : Measure UniversalTheta) (p x : ℝ) : ℝ :=
  universalEqualTermIntegral ν
    (16 * p * (p + 1)) 3 (-p - 2) x

/-- Third derivative of `U`. -/
def universalEqualU3
    (ν : Measure UniversalTheta) (p x : ℝ) : ℝ :=
  universalEqualTermIntegral ν
    (64 * p * (p + 1) * (p + 2)) 4 (-p - 3) x

/-- Centered moment of order `n`. -/
def universalEqualCenteredMoment
    (ν : Measure UniversalTheta) (n : ℕ) : ℝ :=
  ∫ θ, universalEqualZ θ ^ n ∂ν

/-- The fixed open neighborhood used for every differentiation step. -/
def universalEqualLocalSet : Set ℝ :=
  Ioo (-1 / 8) (1 / 8)

theorem universalEqualZ_mem_Icc (θ : UniversalTheta) :
    universalEqualZ θ ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
  unfold universalEqualZ
  constructor <;> linarith [θ.property.1, θ.property.2]

theorem abs_universalEqualZ_le_half (θ : UniversalTheta) :
    |universalEqualZ θ| ≤ 1 / 2 := by
  rw [abs_le]
  have hz := universalEqualZ_mem_Icc θ
  constructor <;> linarith [hz.1, hz.2]

theorem abs_universalEqualZ_le_one (θ : UniversalTheta) :
    |universalEqualZ θ| ≤ 1 := by
  exact (abs_universalEqualZ_le_half θ).trans (by norm_num)

theorem abs_lt_eighth_of_mem_universalEqualLocalSet
    {x : ℝ} (hx : x ∈ universalEqualLocalSet) :
    |x| < 1 / 8 := by
  unfold universalEqualLocalSet at hx
  rw [abs_lt]
  constructor <;> linarith [hx.1, hx.2]

/-- Uniform positivity of the normalized base on the local set. -/
theorem universalEqualBase_ge_half
    {x : ℝ} (hx : x ∈ universalEqualLocalSet)
    (θ : UniversalTheta) :
    1 / 2 ≤ universalEqualBase x θ := by
  have hxabs := abs_lt_eighth_of_mem_universalEqualLocalSet hx
  have hzabs := abs_universalEqualZ_le_half θ
  have h4x : |4 * x| < 1 / 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    nlinarith
  have hprod :
      |4 * x * universalEqualZ θ| < 1 / 4 := by
    calc
      |4 * x * universalEqualZ θ|
          = |4 * x| * |universalEqualZ θ| := abs_mul _ _
      _ ≤ |4 * x| * (1 / 2) :=
        mul_le_mul_of_nonneg_left hzabs (abs_nonneg _)
      _ < (1 / 2) * (1 / 2) := by
        exact mul_lt_mul_of_pos_right h4x (by norm_num)
      _ = 1 / 4 := by norm_num
  unfold universalEqualBase
  nlinarith [le_abs_self (4 * x * universalEqualZ θ)]

theorem universalEqualBase_pos
    {x : ℝ} (hx : x ∈ universalEqualLocalSet)
    (θ : UniversalTheta) :
    0 < universalEqualBase x θ :=
  lt_of_lt_of_le (by norm_num)
    (universalEqualBase_ge_half hx θ)

theorem continuous_universalEqualZ :
    Continuous universalEqualZ := by
  unfold universalEqualZ
  fun_prop

theorem continuous_universalEqualBase_theta (x : ℝ) :
    Continuous (fun θ : UniversalTheta =>
      universalEqualBase x θ) := by
  have hc :
      Continuous (fun _ : UniversalTheta => (4 : ℝ) * x) :=
    continuous_const
  exact continuous_const.sub (hc.mul continuous_universalEqualZ)

theorem continuous_universalEqualTerm_theta
    {c e x : ℝ} {n : ℕ}
    (hx : x ∈ universalEqualLocalSet) :
    Continuous (fun θ : UniversalTheta =>
      universalEqualTerm c n e x θ) := by
  unfold universalEqualTerm
  exact
    ((continuous_const.mul (continuous_universalEqualZ.pow n)).mul
      ((continuous_universalEqualBase_theta x).rpow_const
        (fun θ => Or.inl
          (ne_of_gt (universalEqualBase_pos hx θ)))))

/-- Pointwise derivative recurrence for the centered term family. -/
theorem hasDerivAt_universalEqualTerm
    {c e x : ℝ} {n : ℕ}
    (hx : x ∈ universalEqualLocalSet)
    (θ : UniversalTheta) :
    HasDerivAt
      (fun y => universalEqualTerm c n e y θ)
      (universalEqualTerm (-4 * c * e) (n + 1) (e - 1) x θ)
      x := by
  have hbase :
      HasDerivAt
        (fun y : ℝ => universalEqualBase y θ)
        (-4 * universalEqualZ θ) x := by
    simpa [universalEqualBase, mul_comm, mul_left_comm, mul_assoc] using!
      (hasDerivAt_const x (1 : ℝ)).sub
        ((hasDerivAt_id x).mul_const
          (4 * universalEqualZ θ))
  have hpow :
      HasDerivAt
        (fun y : ℝ => universalEqualBase y θ ^ e)
        ((-4 * universalEqualZ θ) * e
          * universalEqualBase x θ ^ (e - 1)) x :=
    hbase.rpow_const
      (Or.inl (ne_of_gt (universalEqualBase_pos hx θ)))
  unfold universalEqualTerm
  apply
    (hpow.const_mul
      (c * universalEqualZ θ ^ n)).congr_deriv
  rw [pow_succ]
  ring

/-- Explicit local majorant for the derivative term. -/
theorem norm_universalEqualTerm_derivative_le
    {c e x : ℝ} {n : ℕ}
    (hc : 0 ≤ c) (he : e ≤ 0)
    (hx : x ∈ universalEqualLocalSet)
    (θ : UniversalTheta) :
    ‖universalEqualTerm (-4 * c * e) (n + 1) (e - 1) x θ‖
      ≤
    (-4 * c * e) * (1 / 2 : ℝ) ^ (e - 1) := by
  have hce : c * e ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc he
  have hcoef : 0 ≤ -4 * c * e := by linarith
  have hzpow :
      |universalEqualZ θ| ^ (n + 1) ≤ 1 :=
    pow_le_one₀ (abs_nonneg _) (abs_universalEqualZ_le_one θ)
  have hbasepow :
      universalEqualBase x θ ^ (e - 1)
        ≤ (1 / 2 : ℝ) ^ (e - 1) := by
    exact Real.rpow_le_rpow_of_nonpos
      (by norm_num)
      (universalEqualBase_ge_half hx θ)
      (by linarith)
  have hbasepow0 :
      0 ≤ universalEqualBase x θ ^ (e - 1) :=
    Real.rpow_nonneg
      (le_trans (by norm_num)
        (universalEqualBase_ge_half hx θ)) _
  have hhalfpow0 : 0 ≤ (1 / 2 : ℝ) ^ (e - 1) :=
    Real.rpow_nonneg (by norm_num) _
  unfold universalEqualTerm
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hcoef,
    abs_pow, abs_of_nonneg hbasepow0]
  calc
    (-4 * c * e) * |universalEqualZ θ| ^ (n + 1)
          * universalEqualBase x θ ^ (e - 1)
        ≤
      (-4 * c * e) * 1
          * universalEqualBase x θ ^ (e - 1) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hzpow hcoef)
              hbasepow0
    _ ≤ (-4 * c * e) * 1 * (1 / 2 : ℝ) ^ (e - 1) := by
      exact mul_le_mul_of_nonneg_left hbasepow
        (mul_nonneg hcoef (by norm_num))
    _ = (-4 * c * e) * (1 / 2 : ℝ) ^ (e - 1) := by
      ring

/--
Differentiation under an arbitrary finite measure for the whole centered
term family.  This is the only dominated-convergence argument needed by the
equal-size moment bridge.
-/
theorem hasDerivAt_universalEqualTermIntegral
    (ν : Measure UniversalTheta) [IsFiniteMeasure ν]
    {c e x : ℝ} {n : ℕ}
    (hc : 0 ≤ c) (he : e ≤ 0)
    (hx : x ∈ universalEqualLocalSet) :
    HasDerivAt
      (universalEqualTermIntegral ν c n e)
      (universalEqualTermIntegral ν
        (-4 * c * e) (n + 1) (e - 1) x)
      x := by
  have hs : universalEqualLocalSet ∈ 𝓝 x :=
    isOpen_Ioo.mem_nhds hx
  have hFmeas :
      ∀ᶠ y in 𝓝 x,
        AEStronglyMeasurable
          (fun θ : UniversalTheta =>
            universalEqualTerm c n e y θ) ν := by
    filter_upwards [hs] with y hy
    exact (continuous_universalEqualTerm_theta hy).aestronglyMeasurable
  have hFint :
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
  have hce : c * e ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc he
  have hc' : 0 ≤ -4 * c * e := by linarith
  have he' : e - 1 ≤ 0 := by linarith
  have hF'meas :
      AEStronglyMeasurable
        (fun θ : UniversalTheta =>
          universalEqualTerm (-4 * c * e)
            (n + 1) (e - 1) x θ) ν :=
    (continuous_universalEqualTerm_theta hx).aestronglyMeasurable
  have hbound :
      ∀ᵐ θ ∂ν, ∀ y ∈ universalEqualLocalSet,
        ‖universalEqualTerm (-4 * c * e)
            (n + 1) (e - 1) y θ‖
          ≤
        (-4 * c * e) * (1 / 2 : ℝ) ^ (e - 1) := by
    exact ae_of_all ν fun θ y hy =>
      norm_universalEqualTerm_derivative_le hc he hy θ
  have hboundint :
      Integrable
        (fun _ : UniversalTheta =>
          (-4 * c * e) * (1 / 2 : ℝ) ^ (e - 1)) ν :=
    integrable_const _
  have hdiff :
      ∀ᵐ θ ∂ν, ∀ y ∈ universalEqualLocalSet,
        HasDerivAt
          (fun z => universalEqualTerm c n e z θ)
          (universalEqualTerm (-4 * c * e)
            (n + 1) (e - 1) y θ)
          y := by
    exact ae_of_all ν fun θ y hy =>
      hasDerivAt_universalEqualTerm hy θ
  exact
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun y θ =>
        universalEqualTerm c n e y θ)
      (F' := fun y θ =>
        universalEqualTerm (-4 * c * e)
          (n + 1) (e - 1) y θ)
      (bound := fun _ : UniversalTheta =>
        (-4 * c * e) * (1 / 2 : ℝ) ^ (e - 1))
      hs hFmeas hFint hF'meas hbound hboundint hdiff).2

section DerivativeChain

variable (ν : Measure UniversalTheta) [IsFiniteMeasure ν]
variable {p x : ℝ}

theorem hasDerivAt_universalEqualD
    (hp : 0 < p) (hx : x ∈ universalEqualLocalSet) :
    HasDerivAt (universalEqualD ν p) (universalEqualD1 ν p x) x := by
  change
    HasDerivAt
      (universalEqualTermIntegral ν 1 0 (-p))
      (universalEqualTermIntegral ν (4 * p) 1 (-p - 1) x) x
  have hcoef : -4 * (1 : ℝ) * (-p) = 4 * p := by ring
  have hn : (0 : ℕ) + 1 = 1 := by norm_num
  have he : -p - 1 = -p - 1 := rfl
  simpa only [hcoef, hn, he] using
    (hasDerivAt_universalEqualTermIntegral ν
      (c := 1) (n := 0) (e := -p)
      (by norm_num) (by linarith) hx)

theorem hasDerivAt_universalEqualD1
    (hp : 0 < p) (hx : x ∈ universalEqualLocalSet) :
    HasDerivAt (universalEqualD1 ν p) (universalEqualD2 ν p x) x := by
  change
    HasDerivAt
      (universalEqualTermIntegral ν (4 * p) 1 (-p - 1))
      (universalEqualTermIntegral ν
        (16 * p * (p + 1)) 2 (-p - 2) x) x
  have hcoef :
      -4 * (4 * p) * (-p - 1)
        = 16 * p * (p + 1) := by ring
  have hn : (1 : ℕ) + 1 = 2 := by norm_num
  have he : -p - 1 - 1 = -p - 2 := by ring
  simpa only [hcoef, hn, he] using
    (hasDerivAt_universalEqualTermIntegral ν
      (c := 4 * p) (n := 1) (e := -p - 1)
      (by positivity) (by linarith) hx)

theorem hasDerivAt_universalEqualD2
    (hp : 0 < p) (hx : x ∈ universalEqualLocalSet) :
    HasDerivAt (universalEqualD2 ν p) (universalEqualD3 ν p x) x := by
  change
    HasDerivAt
      (universalEqualTermIntegral ν
        (16 * p * (p + 1)) 2 (-p - 2))
      (universalEqualTermIntegral ν
        (64 * p * (p + 1) * (p + 2)) 3 (-p - 3) x) x
  have hcoef :
      -4 * (16 * p * (p + 1)) * (-p - 2)
        = 64 * p * (p + 1) * (p + 2) := by ring
  have hn : (2 : ℕ) + 1 = 3 := by norm_num
  have he : -p - 2 - 1 = -p - 3 := by ring
  simpa only [hcoef, hn, he] using
    (hasDerivAt_universalEqualTermIntegral ν
      (c := 16 * p * (p + 1)) (n := 2) (e := -p - 2)
      (by positivity) (by linarith) hx)

theorem hasDerivAt_universalEqualU
    (hp : 0 < p) (hx : x ∈ universalEqualLocalSet) :
    HasDerivAt (universalEqualU ν p) (universalEqualU1 ν p x) x := by
  change
    HasDerivAt
      (universalEqualTermIntegral ν 1 1 (-p))
      (universalEqualTermIntegral ν (4 * p) 2 (-p - 1) x) x
  have hcoef : -4 * (1 : ℝ) * (-p) = 4 * p := by ring
  have hn : (1 : ℕ) + 1 = 2 := by norm_num
  have he : -p - 1 = -p - 1 := rfl
  simpa only [hcoef, hn, he] using
    (hasDerivAt_universalEqualTermIntegral ν
      (c := 1) (n := 1) (e := -p)
      (by norm_num) (by linarith) hx)

theorem hasDerivAt_universalEqualU1
    (hp : 0 < p) (hx : x ∈ universalEqualLocalSet) :
    HasDerivAt (universalEqualU1 ν p) (universalEqualU2 ν p x) x := by
  change
    HasDerivAt
      (universalEqualTermIntegral ν (4 * p) 2 (-p - 1))
      (universalEqualTermIntegral ν
        (16 * p * (p + 1)) 3 (-p - 2) x) x
  have hcoef :
      -4 * (4 * p) * (-p - 1)
        = 16 * p * (p + 1) := by ring
  have hn : (2 : ℕ) + 1 = 3 := by norm_num
  have he : -p - 1 - 1 = -p - 2 := by ring
  simpa only [hcoef, hn, he] using
    (hasDerivAt_universalEqualTermIntegral ν
      (c := 4 * p) (n := 2) (e := -p - 1)
      (by positivity) (by linarith) hx)

theorem hasDerivAt_universalEqualU2
    (hp : 0 < p) (hx : x ∈ universalEqualLocalSet) :
    HasDerivAt (universalEqualU2 ν p) (universalEqualU3 ν p x) x := by
  change
    HasDerivAt
      (universalEqualTermIntegral ν
        (16 * p * (p + 1)) 3 (-p - 2))
      (universalEqualTermIntegral ν
        (64 * p * (p + 1) * (p + 2)) 4 (-p - 3) x) x
  have hcoef :
      -4 * (16 * p * (p + 1)) * (-p - 2)
        = 64 * p * (p + 1) * (p + 2) := by ring
  have hn : (3 : ℕ) + 1 = 4 := by norm_num
  have he : -p - 2 - 1 = -p - 3 := by ring
  simpa only [hcoef, hn, he] using
    (hasDerivAt_universalEqualTermIntegral ν
      (c := 16 * p * (p + 1)) (n := 3) (e := -p - 2)
      (by positivity) (by linarith) hx)

end DerivativeChain

/-- The equal-size reduced denominator factors into a constant and `D`. -/
theorem universalB_equal_centered
    (a x : ℝ) (θ : UniversalTheta) :
    universalB a a (1 / 2 + x) 0 θ
      = a * universalEqualBase x θ := by
  unfold universalB universalEqualBase universalEqualZ
  ring

theorem universalKernel_equal_centered
    {a x : ℝ} (ha : 0 < a)
    (hx : x ∈ universalEqualLocalSet)
    (θ : UniversalTheta) :
    universalKernel a a (1 / 2 + x) 0 θ
      =
    a ^ (-universalEqualExponent a)
      * universalEqualBase x θ ^ (-universalEqualExponent a) := by
  unfold universalKernel universalExponent universalEqualExponent
  rw [universalB_equal_centered]
  rw [Real.mul_rpow ha.le
    (universalEqualBase_pos hx θ).le]
  congr 2 <;> ring

/--
The posterior identity gives the exact centered identity `U(x)=xD(x)` on
the fixed neighborhood.
-/
theorem UniversalPosteriorIdentity.equal_centered_identity
    (ν : Measure UniversalTheta) [IsProbabilityMeasure ν]
    {a x : ℝ}
    (H : UniversalPosteriorIdentity ν a a)
    (ha : 0 < a)
    (hx : x ∈ universalEqualLocalSet) :
    universalEqualU ν (universalEqualExponent a) x
      =
    x * universalEqualD ν (universalEqualExponent a) x := by
  have hxabs := abs_lt_eighth_of_mem_universalEqualLocalSet hx
  rcases abs_lt.mp hxabs with ⟨hxl, hxu⟩
  have hr0 : 0 < 1 / 2 + x := by linarith
  have hr1 : 1 / 2 + x < 1 := by linarith
  have hraw :=
    H.numerator_eq_mul_denominator ha ha hr0 hr1
      (q := 0) le_rfl
  let p := universalEqualExponent a
  let c := a ^ (-p)
  have hc : c ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha _)
  have hkernel (θ : UniversalTheta) :
      universalKernel a a (1 / 2 + x) 0 θ
        =
      c * universalEqualBase x θ ^ (-p) := by
    simpa only [p, c] using
      universalKernel_equal_centered ha hx θ
  have hDint :
      Integrable
        (fun θ : UniversalTheta =>
          universalEqualBase x θ ^ (-p)) ν := by
    have hp : 0 < p := by
      dsimp only [p, universalEqualExponent]
      linarith
    let f : UniversalTheta →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact
        ⟨fun θ : UniversalTheta =>
            universalEqualBase x θ ^ (-p),
          (continuous_universalEqualBase_theta x).rpow_const
            (fun θ => Or.inl
              (ne_of_gt (universalEqualBase_pos hx θ)))⟩
    change Integrable (f : UniversalTheta → ℝ) ν
    exact BoundedContinuousFunction.integrable ν f
  have hUint :
      Integrable
        (fun θ : UniversalTheta =>
          universalEqualZ θ
            * universalEqualBase x θ ^ (-p)) ν := by
    have hcont :
        Continuous
          (fun θ : UniversalTheta =>
            universalEqualZ θ
              * universalEqualBase x θ ^ (-p)) := by
      simpa [universalEqualTerm] using
        (continuous_universalEqualTerm_theta
          (c := 1) (n := 1) (e := -p) hx)
    let f : UniversalTheta →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact
        ⟨fun θ : UniversalTheta =>
            universalEqualZ θ
              * universalEqualBase x θ ^ (-p),
          hcont⟩
    change Integrable (f : UniversalTheta → ℝ) ν
    exact BoundedContinuousFunction.integrable ν f
  have hden :
      universalPosteriorDenominator ν a a (1 / 2 + x) 0
        =
      c * universalEqualD ν p x := by
    unfold universalPosteriorDenominator
    simp_rw [hkernel]
    rw [integral_const_mul]
    simp [universalEqualD, universalEqualTermIntegral,
      universalEqualTerm]
  have hnum :
      universalPosteriorNumerator ν a a (1 / 2 + x) 0
        =
      c * (1 / 2 * universalEqualD ν p x
        + universalEqualU ν p x) := by
    unfold universalPosteriorNumerator
    simp_rw [hkernel]
    have hpull :
        (fun θ : UniversalTheta =>
          (θ : ℝ) *
            (c * universalEqualBase x θ ^ (-p)))
          =
        (fun θ : UniversalTheta =>
          c * ((θ : ℝ)
            * universalEqualBase x θ ^ (-p))) := by
      funext θ
      ring
    rw [hpull, integral_const_mul]
    have hpoint :
        (fun θ : UniversalTheta =>
          (θ : ℝ) * universalEqualBase x θ ^ (-p))
          =
        (fun θ =>
          (1 / 2) * universalEqualBase x θ ^ (-p)
            + universalEqualZ θ
              * universalEqualBase x θ ^ (-p)) := by
      funext θ
      unfold universalEqualZ
      ring
    rw [hpoint, integral_add (hDint.const_mul _) hUint,
      integral_const_mul]
    simp [universalEqualD, universalEqualU,
      universalEqualTermIntegral, universalEqualTerm]
  rw [hnum, hden] at hraw
  apply (mul_left_cancel₀ hc)
  linear_combination hraw

theorem zero_mem_universalEqualLocalSet :
    (0 : ℝ) ∈ universalEqualLocalSet := by
  unfold universalEqualLocalSet
  norm_num

section CenterValues

variable (ν : Measure UniversalTheta) [IsProbabilityMeasure ν]
variable (p : ℝ)

theorem universalEqualD_zero :
    universalEqualD ν p 0 = 1 := by
  simp [universalEqualD, universalEqualTermIntegral,
    universalEqualTerm, universalEqualBase]

theorem universalEqualU1_zero :
    universalEqualU1 ν p 0
      =
    4 * p * universalEqualCenteredMoment ν 2 := by
  unfold universalEqualU1 universalEqualTermIntegral
    universalEqualTerm universalEqualCenteredMoment
    universalEqualBase
  simp only [mul_zero, zero_mul, sub_zero, Real.one_rpow, mul_one]
  rw [← integral_const_mul]

theorem universalEqualD2_zero :
    universalEqualD2 ν p 0
      =
    16 * p * (p + 1)
      * universalEqualCenteredMoment ν 2 := by
  unfold universalEqualD2 universalEqualTermIntegral
    universalEqualTerm universalEqualCenteredMoment
    universalEqualBase
  simp only [mul_zero, zero_mul, sub_zero, Real.one_rpow, mul_one]
  rw [← integral_const_mul]

theorem universalEqualU3_zero :
    universalEqualU3 ν p 0
      =
    64 * p * (p + 1) * (p + 2)
      * universalEqualCenteredMoment ν 4 := by
  unfold universalEqualU3 universalEqualTermIntegral
    universalEqualTerm universalEqualCenteredMoment
    universalEqualBase
  simp only [mul_zero, zero_mul, sub_zero, Real.one_rpow, mul_one]
  rw [← integral_const_mul]

end CenterValues

/--
An exact local identity `U=xD` implies the two quotient identities.  This
theorem is useful independently of the decision-theoretic source of that
identity.
-/
theorem universalEqualQuotientIdentities_of_centered_identity
    (ν : Measure UniversalTheta) [IsProbabilityMeasure ν]
    {p : ℝ} (hp : 0 < p)
    (hcenter :
      ∀ x ∈ universalEqualLocalSet,
        universalEqualU ν p x = x * universalEqualD ν p x) :
    UniversalEqualQuotientIdentities p
      (universalEqualCenteredMoment ν 2)
      (universalEqualCenteredMoment ν 4) := by
  have hfirst :
      ∀ x ∈ universalEqualLocalSet,
        universalEqualU1 ν p x
          =
        universalEqualD ν p x
          + x * universalEqualD1 ν p x := by
    intro x hx
    have heq :
        universalEqualU ν p
          =ᶠ[𝓝 x]
        fun y => y * universalEqualD ν p y := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hcenter y hy
    have hu := hasDerivAt_universalEqualU ν hp hx
    have hid :
        HasDerivAt (fun y : ℝ => y) 1 x :=
      hasDerivAt_id x
    have hrhs :
        HasDerivAt
          (fun y : ℝ => y * universalEqualD ν p y)
          (universalEqualD ν p x
            + x * universalEqualD1 ν p x) x := by
      simpa only [one_mul] using!
        hid.mul (hasDerivAt_universalEqualD ν hp hx)
    exact (hu.congr_of_eventuallyEq heq.symm).unique
      hrhs
  have hsecond :
      ∀ x ∈ universalEqualLocalSet,
        universalEqualU2 ν p x
          =
        2 * universalEqualD1 ν p x
          + x * universalEqualD2 ν p x := by
    intro x hx
    have heq :
        universalEqualU1 ν p
          =ᶠ[𝓝 x]
        fun y =>
          universalEqualD ν p y
            + y * universalEqualD1 ν p y := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hfirst y hy
    have hu := hasDerivAt_universalEqualU1 ν hp hx
    have hid :
        HasDerivAt (fun y : ℝ => y) 1 x :=
      hasDerivAt_id x
    have hrhs :
        HasDerivAt
          (fun y : ℝ =>
            universalEqualD ν p y
              + y * universalEqualD1 ν p y)
          (2 * universalEqualD1 ν p x
            + x * universalEqualD2 ν p x) x := by
      have h :=
        (hasDerivAt_universalEqualD ν hp hx).add
          (hid.mul
            (hasDerivAt_universalEqualD1 ν hp hx))
      simpa only [one_mul] using!
        h.congr_deriv (by ring)
    exact (hu.congr_of_eventuallyEq heq.symm).unique
      hrhs
  have hlinearDerivative :
      universalEqualU1 ν p 0 = universalEqualD ν p 0 := by
    simpa using hfirst 0 zero_mem_universalEqualLocalSet
  have hcubicDerivative :
      universalEqualU3 ν p 0
        = 3 * universalEqualD2 ν p 0 := by
    have heq :
        universalEqualU2 ν p
          =ᶠ[𝓝 (0 : ℝ)]
        fun y =>
          2 * universalEqualD1 ν p y
            + y * universalEqualD2 ν p y := by
      filter_upwards
        [isOpen_Ioo.mem_nhds zero_mem_universalEqualLocalSet]
          with y hy
      exact hsecond y hy
    have hu :=
      hasDerivAt_universalEqualU2 ν hp
        zero_mem_universalEqualLocalSet
    have hid :
        HasDerivAt (fun y : ℝ => y) 1 0 :=
      hasDerivAt_id 0
    have hrhs :
        HasDerivAt
          (fun y : ℝ =>
            2 * universalEqualD1 ν p y
              + y * universalEqualD2 ν p y)
          (3 * universalEqualD2 ν p 0) 0 := by
      have h :=
        ((hasDerivAt_universalEqualD1 ν hp
            zero_mem_universalEqualLocalSet).const_mul 2).add
          (hid.mul
            (hasDerivAt_universalEqualD2 ν hp
              zero_mem_universalEqualLocalSet))
      simpa only [one_mul, zero_mul, add_zero] using!
        h.congr_deriv (by ring)
    exact (hu.congr_of_eventuallyEq heq.symm).unique
      hrhs
  have hlinear :
      4 * p * universalEqualCenteredMoment ν 2 = 1 := by
    rw [← universalEqualU1_zero ν p,
      hlinearDerivative, universalEqualD_zero]
  refine
    { linear := ?_
      cubic := ?_ }
  · simpa [universalEqualNumeratorLinearCoefficient] using hlinear
  · rw [universalEqualNumeratorCubicCoefficient,
      universalEqualNumeratorLinearCoefficient,
      universalEqualDenominatorQuadraticCoefficient]
    rw [universalEqualU3_zero ν p,
      universalEqualD2_zero ν p] at hcubicDerivative
    calc
      (32 / 3) * p * (p + 1) * (p + 2)
          * universalEqualCenteredMoment ν 4
          =
        (1 / 6)
          * (64 * p * (p + 1) * (p + 2)
            * universalEqualCenteredMoment ν 4) := by ring
      _ =
        (1 / 6)
          * (3 * (16 * p * (p + 1)
            * universalEqualCenteredMoment ν 2)) := by
              rw [hcubicDerivative]
      _ =
        (4 * p * universalEqualCenteredMoment ν 2)
          * (8 * p * (p + 1)
            * universalEqualCenteredMoment ν 2) := by
              rw [hlinear]
              ring

/--
The actual limiting posterior identity supplies the two equal-size quotient
identities for every `a > 0`.
-/
theorem UniversalPosteriorIdentity.equal_quotientIdentities
    (ν : Measure UniversalTheta) [IsProbabilityMeasure ν]
    {a : ℝ}
    (H : UniversalPosteriorIdentity ν a a)
    (ha : 0 < a) :
    UniversalEqualQuotientIdentities
      (universalEqualExponent a)
      (universalEqualCenteredMoment ν 2)
      (universalEqualCenteredMoment ν 4) := by
  apply universalEqualQuotientIdentities_of_centered_identity ν
    (universalEqualExponent_pos ha)
  intro x hx
  exact H.equal_centered_identity ν ha hx

end

end GraybillDeal
