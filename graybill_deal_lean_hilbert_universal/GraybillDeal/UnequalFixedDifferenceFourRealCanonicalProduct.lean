import GraybillDeal.UnequalFixedDifferenceFourRealCanonicalReduced
import GraybillDeal.UnequalDampedRisk
import GraybillDeal.GeneralCanonicalProduct
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.FieldSimp

/-!
# Product-moment reduction for the fixed-difference-four family

This file integrates the gamma coordinates `L,V` out of the direct
canonical construction for

`(n₁,n₂) = (2m-1,2m+3)`, `m ≥ 7`.

The canonical residual sum has law `Gamma(2m,1/2)`, while
`V = D² / λ` has law `Gamma(1/2,1/2)`.  Consequently

* `E[V²/L] = 3 / (2(2m-1))`;
* `E[V³/L²] = 15 / (4(2m-1)(2m-2))`.

The factor `4m` in the canonical quadratic statistic converts these
moments exactly into the family constants

* `K_m = 6m/(2m-1)`;
* `Ell_m = 30m²/((m-1)(2m-1))`.

The final theorem packages the two resulting moments as an
`UnequalDampedMomentBridge`.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Scalar moment identifications -/

/--
The coefficient `4m` in the canonical quadratic statistic, multiplied by
`E[V²/L]`, is exactly the reduced linear constant `K_m`.
-/
theorem unequalFixedDifferenceFourRealK_eq_gammaMoment
    {m : ℝ} (hm : 7 ≤ m) :
    4 * m
        * (3 / (2 * (2 * m - 1)))
      =
    unequalFixedDifferenceFourRealK m := by
  have hden : 2 * m - 1 ≠ 0 := by linarith
  unfold unequalFixedDifferenceFourRealK
  field_simp [hden]
  ring

/--
The mixed term in the square of the canonical perturbation produces
`2 K_m c_m`.
-/
theorem unequalFixedDifferenceFourRealTwoKCMoment
    {m : ℝ} (hm : 7 ≤ m) :
    (8 * m * unequalFixedDifferenceFourRealC m)
        * (3 / (2 * (2 * m - 1)))
      =
    2 * unequalFixedDifferenceFourRealK m
        * unequalFixedDifferenceFourRealC m := by
  rw [show
    (8 * m * unequalFixedDifferenceFourRealC m)
          * (3 / (2 * (2 * m - 1)))
      =
    2 * unequalFixedDifferenceFourRealC m
      * (4 * m
        * (3 / (2 * (2 * m - 1)))) by ring,
    unequalFixedDifferenceFourRealK_eq_gammaMoment hm]
  ring

/--
The squared `4m` coefficient, multiplied by `E[V³/L²]`, is exactly
the reduced quadratic constant `Ell_m`.
-/
theorem unequalFixedDifferenceFourRealEll_eq_gammaMoment
    {m : ℝ} (hm : 7 ≤ m) :
    (4 * m) ^ 2
        * (15 /
          (4 * (2 * m - 1)
            * (2 * m - 2)))
      =
    unequalFixedDifferenceFourRealEll m := by
  have hm1 : m - 1 ≠ 0 := by linarith
  have h2m1 : 2 * m - 1 ≠ 0 := by linarith
  have h2m2 : 2 * m - 2 ≠ 0 := by linarith
  unfold unequalFixedDifferenceFourRealEll
  field_simp [hm1, h2m1, h2m2]
  ring

/-! ## Canonical coefficient factors -/

/-- Coefficient of `V` in the family linear mixed-moment expansion. -/
def unequalFixedDifferenceFourRealCanonicalLinearFactor0
    (m : ℝ) (θ p : ℝ) : ℝ :=
  (unequalFixedDifferenceFourRealCanonicalR m θ p - θ)
    * unequalDampedPhi
        (unequalFixedDifferenceFourRealT m)
        (unequalFixedDifferenceFourRealKappa m)
        (unequalFixedDifferenceFourRealCanonicalR m θ p)

/-- Coefficient of `V²/L` in the family linear mixed-moment expansion. -/
def unequalFixedDifferenceFourRealCanonicalLinearFactor1
    (m : ℝ) (θ p : ℝ) : ℝ :=
  unequalFixedDifferenceFourRealCanonicalLinearFactor0 m θ p
    / unequalFixedDifferenceFourRealCanonicalDenom m θ p

/-- Coefficient of `V` in the family quadratic mixed-moment expansion. -/
def unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
    (m : ℝ) (θ p : ℝ) : ℝ :=
  unequalDampedPhi
      (unequalFixedDifferenceFourRealT m)
      (unequalFixedDifferenceFourRealKappa m)
      (unequalFixedDifferenceFourRealCanonicalR m θ p) ^ 2

/-- Coefficient of `V²/L` in the family quadratic mixed-moment expansion. -/
def unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
    (m : ℝ) (θ p : ℝ) : ℝ :=
  unequalFixedDifferenceFourRealCanonicalQuadraticFactor0 m θ p
    / unequalFixedDifferenceFourRealCanonicalDenom m θ p

/-- Coefficient of `V³/L²` in the family quadratic mixed-moment expansion. -/
def unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
    (m : ℝ) (θ p : ℝ) : ℝ :=
  unequalFixedDifferenceFourRealCanonicalQuadraticFactor0 m θ p
    / unequalFixedDifferenceFourRealCanonicalDenom m θ p ^ 2

/-- Reduced linear `P`-integrand after taking the `L,V` moments. -/
def unequalFixedDifferenceFourRealCanonicalLinearPIntegrand
    (m : ℝ) (θ p : ℝ) : ℝ :=
  unequalFixedDifferenceFourRealCanonicalLinearFactor0 m θ p
      * unequalFixedDifferenceFourRealC m
    - unequalFixedDifferenceFourRealK m
      * unequalFixedDifferenceFourRealCanonicalLinearFactor1 m θ p

/-- Reduced quadratic `P`-integrand after taking the `L,V` moments. -/
def unequalFixedDifferenceFourRealCanonicalQuadraticPIntegrand
    (m : ℝ) (θ p : ℝ) : ℝ :=
  unequalFixedDifferenceFourRealCanonicalQuadraticFactor0 m θ p
      * unequalFixedDifferenceFourRealC m ^ 2
    - (2 * unequalFixedDifferenceFourRealK m
        * unequalFixedDifferenceFourRealC m)
      * unequalFixedDifferenceFourRealCanonicalQuadraticFactor1 m θ p
    + unequalFixedDifferenceFourRealEll m
      * unequalFixedDifferenceFourRealCanonicalQuadraticFactor2 m θ p

theorem measurable_unequalFixedDifferenceFourRealCanonicalLinearFactor0
    (m : ℝ) (θ : ℝ) :
    Measurable
      (unequalFixedDifferenceFourRealCanonicalLinearFactor0 m θ) := by
  unfold unequalFixedDifferenceFourRealCanonicalLinearFactor0
    unequalFixedDifferenceFourRealCanonicalR
    unequalFixedDifferenceFourRealCanonicalDenom
    unequalDampedPhi unequalDampedInner
  fun_prop

theorem measurable_unequalFixedDifferenceFourRealCanonicalLinearFactor1
    (m : ℝ) (θ : ℝ) :
    Measurable
      (unequalFixedDifferenceFourRealCanonicalLinearFactor1 m θ) := by
  unfold unequalFixedDifferenceFourRealCanonicalLinearFactor1
  exact
    (measurable_unequalFixedDifferenceFourRealCanonicalLinearFactor0 m θ).div
      (by
        unfold unequalFixedDifferenceFourRealCanonicalDenom
        fun_prop)

theorem measurable_unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
    (m : ℝ) (θ : ℝ) :
    Measurable
      (unequalFixedDifferenceFourRealCanonicalQuadraticFactor0 m θ) := by
  unfold unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
    unequalFixedDifferenceFourRealCanonicalR
    unequalFixedDifferenceFourRealCanonicalDenom
    unequalDampedPhi unequalDampedInner
  fun_prop

theorem measurable_unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
    (m : ℝ) (θ : ℝ) :
    Measurable
      (unequalFixedDifferenceFourRealCanonicalQuadraticFactor1 m θ) := by
  unfold unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
  exact
    (measurable_unequalFixedDifferenceFourRealCanonicalQuadraticFactor0 m θ).div
      (by
        unfold unequalFixedDifferenceFourRealCanonicalDenom
        fun_prop)

theorem measurable_unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
    (m : ℝ) (θ : ℝ) :
    Measurable
      (unequalFixedDifferenceFourRealCanonicalQuadraticFactor2 m θ) := by
  unfold unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
  exact
    (measurable_unequalFixedDifferenceFourRealCanonicalQuadraticFactor0 m θ).div
      (by
        unfold unequalFixedDifferenceFourRealCanonicalDenom
        fun_prop)

/-- Integrability of the five family-indexed `P` coefficient functions. -/
structure UnequalFixedDifferenceFourRealCanonicalPFactorIntegrability
    (m : ℝ) (θ : ℝ) (P : Ω → ℝ) (ℙ : Measure Ω) : Prop where
  linear0 :
    Integrable
      (fun ω =>
        unequalFixedDifferenceFourRealCanonicalLinearFactor0
          m θ (P ω)) ℙ
  linear1 :
    Integrable
      (fun ω =>
        unequalFixedDifferenceFourRealCanonicalLinearFactor1
          m θ (P ω)) ℙ
  quadratic0 :
    Integrable
      (fun ω =>
        unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
          m θ (P ω)) ℙ
  quadratic1 :
    Integrable
      (fun ω =>
        unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
          m θ (P ω)) ℙ
  quadratic2 :
    Integrable
      (fun ω =>
        unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
          m θ (P ω)) ℙ

/-! ## Pointwise mixed-moment expansions -/

/--
Pointwise expansion of `V (R-θ) H` into the two products that independence
will factor.
-/
theorem unequalFixedDifferenceFourRealCanonicalLinearH_expand
    (m : ℝ) (θ p l v : ℝ) :
    v * (unequalFixedDifferenceFourRealCanonicalR m θ p - θ)
        * unequalFixedDifferenceFourRealCanonicalH m θ p l v
      =
    unequalFixedDifferenceFourRealC m
      * (unequalFixedDifferenceFourRealCanonicalLinearFactor0
          m θ p * v)
    - (4 * m)
      * (unequalFixedDifferenceFourRealCanonicalLinearFactor1
          m θ p * (v ^ 2 / l)) := by
  unfold unequalFixedDifferenceFourRealCanonicalH
    unequalFixedDifferenceFourRealCanonicalQ
    unequalFixedDifferenceFourRealCanonicalLinearFactor1
    unequalFixedDifferenceFourRealCanonicalLinearFactor0
  simp only [div_eq_mul_inv, mul_inv]
  ring

/--
Pointwise expansion of `V H²` into the three products that independence
will factor.
-/
theorem unequalFixedDifferenceFourRealCanonicalQuadraticH_expand
    (m : ℝ) (θ p l v : ℝ) :
    v * unequalFixedDifferenceFourRealCanonicalH m θ p l v ^ 2
      =
    unequalFixedDifferenceFourRealC m ^ 2
      * (unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
          m θ p * v)
    - (8 * m * unequalFixedDifferenceFourRealC m)
      * (unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
          m θ p * (v ^ 2 / l))
    + (4 * m) ^ 2
      * (unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
          m θ p * (v ^ 3 / l ^ 2)) := by
  unfold unequalFixedDifferenceFourRealCanonicalH
    unequalFixedDifferenceFourRealCanonicalQ
    unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
    unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
    unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-! ## Identification of the reduced `P` integrands -/

theorem unequalFixedDifferenceFourRealCanonicalLinearPIntegrand_eq_BIntegrand
    (m : ℝ) (θ p : ℝ) :
    unequalFixedDifferenceFourRealCanonicalLinearPIntegrand m θ p
      =
    unequalFixedDifferenceFourRealCanonicalBIntegrand m θ p := by
  unfold unequalFixedDifferenceFourRealCanonicalLinearPIntegrand
    unequalFixedDifferenceFourRealCanonicalLinearFactor1
    unequalFixedDifferenceFourRealCanonicalLinearFactor0
    unequalFixedDifferenceFourRealCanonicalBIntegrand
  ring

theorem unequalFixedDifferenceFourRealCanonicalQuadraticPIntegrand_eq_CIntegrand
    (m : ℝ) (θ p : ℝ) :
    unequalFixedDifferenceFourRealCanonicalQuadraticPIntegrand m θ p
      =
    unequalFixedDifferenceFourRealCanonicalCIntegrand m θ p := by
  unfold unequalFixedDifferenceFourRealCanonicalQuadraticPIntegrand
    unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
    unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
    unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
    unequalFixedDifferenceFourRealCanonicalCIntegrand
    unequalFixedDifferenceFourRealCKernel
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-! ## Linear product reduction -/

/--
Integrating out `L,V` reduces the full linear canonical moment to the
one-dimensional `P` integrand.
-/
theorem unequalFixedDifferenceFourRealCanonicalLinearH_product_reduction
    {m : ℝ} (hm : 7 ≤ m)
    (θ : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV :
      ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom :
      GeneralCanonicalFiveMoments (2 * m) L V ℙ)
    (hPint :
      UnequalFixedDifferenceFourRealCanonicalPFactorIntegrability
        m θ P ℙ) :
    (∫ ω,
      V ω * (unequalFixedDifferenceFourRealCanonicalR m θ (P ω) - θ)
        * unequalFixedDifferenceFourRealCanonicalH
            m θ (P ω) (L ω) (V ω) ∂ℙ)
      =
    ∫ ω,
      unequalFixedDifferenceFourRealCanonicalLinearPIntegrand
        m θ (P ω) ∂ℙ := by
  obtain ⟨hV2L_int, hV2L_mean⟩ :=
    general_integral_v_sq_div_l
      (2 * m) L V ℙ hVL hmom
  have hP0V :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalLinearFactor0
            m θ (P ω))
        V ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourRealCanonicalLinearFactor0
          m θ)
        (by fun_prop : Measurable fun z : ℝ × ℝ => z.2)
  have hP1V2L :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalLinearFactor1
            m θ (P ω))
        (fun ω => V ω ^ 2 / L ω) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourRealCanonicalLinearFactor1
          m θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 2 / z.1)
  have hterm0 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalLinearFactor0
              m θ (P ω)
            * V ω) ℙ :=
    hP0V.integrable_mul hPint.linear0 hmom.v_integrable
  have hterm1 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalLinearFactor1
              m θ (P ω)
            * (V ω ^ 2 / L ω)) ℙ :=
    hP1V2L.integrable_mul hPint.linear1 hV2L_int
  have hfactor0 :
      (∫ ω,
        unequalFixedDifferenceFourRealCanonicalLinearFactor0
            m θ (P ω)
          * V ω ∂ℙ)
        =
      ∫ ω,
        unequalFixedDifferenceFourRealCanonicalLinearFactor0
          m θ (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω,
            unequalFixedDifferenceFourRealCanonicalLinearFactor0
              m θ (P ω) ∂ℙ)
            * ∫ ω, V ω ∂ℙ :=
        hP0V.integral_fun_mul_eq_mul_integral
          hPint.linear0.aestronglyMeasurable
          hmom.v_integrable.aestronglyMeasurable
      _ = _ := by rw [hmom.v_mean, mul_one]
  have hfactor1 :
      (∫ ω,
        unequalFixedDifferenceFourRealCanonicalLinearFactor1
            m θ (P ω)
          * (V ω ^ 2 / L ω) ∂ℙ)
        =
      (3 / (2 * (2 * m - 1)))
        * ∫ ω,
          unequalFixedDifferenceFourRealCanonicalLinearFactor1
            m θ (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω,
            unequalFixedDifferenceFourRealCanonicalLinearFactor1
              m θ (P ω) ∂ℙ)
            * ∫ ω, V ω ^ 2 / L ω ∂ℙ :=
        hP1V2L.integral_fun_mul_eq_mul_integral
          hPint.linear1.aestronglyMeasurable
          hV2L_int.aestronglyMeasurable
      _ = _ := by
        rw [hV2L_mean]
        ring
  have hreduced :
      (∫ ω,
        unequalFixedDifferenceFourRealCanonicalLinearPIntegrand
          m θ (P ω) ∂ℙ)
        =
      unequalFixedDifferenceFourRealC m
          * (∫ ω,
            unequalFixedDifferenceFourRealCanonicalLinearFactor0
              m θ (P ω) ∂ℙ)
        - unequalFixedDifferenceFourRealK m
          * (∫ ω,
            unequalFixedDifferenceFourRealCanonicalLinearFactor1
              m θ (P ω) ∂ℙ) := by
    calc
      _ =
          ∫ ω,
            unequalFixedDifferenceFourRealCanonicalLinearFactor0
                m θ (P ω)
                * unequalFixedDifferenceFourRealC m
              - unequalFixedDifferenceFourRealK m
                * unequalFixedDifferenceFourRealCanonicalLinearFactor1
                  m θ (P ω) ∂ℙ := by
            rfl
      _ =
          (∫ ω,
            unequalFixedDifferenceFourRealCanonicalLinearFactor0
                m θ (P ω)
              * unequalFixedDifferenceFourRealC m ∂ℙ)
            -
          ∫ ω,
            unequalFixedDifferenceFourRealK m
              * unequalFixedDifferenceFourRealCanonicalLinearFactor1
                m θ (P ω) ∂ℙ := by
            rw [integral_sub
              (hPint.linear0.mul_const
                (unequalFixedDifferenceFourRealC m))
              (hPint.linear1.const_mul
                (unequalFixedDifferenceFourRealK m))]
      _ = _ := by
        rw [integral_mul_const, integral_const_mul]
        ring
  calc
    (∫ ω,
      V ω * (unequalFixedDifferenceFourRealCanonicalR m θ (P ω) - θ)
        * unequalFixedDifferenceFourRealCanonicalH
            m θ (P ω) (L ω) (V ω) ∂ℙ)
        =
      ∫ ω,
        unequalFixedDifferenceFourRealC m
          * (unequalFixedDifferenceFourRealCanonicalLinearFactor0
              m θ (P ω) * V ω)
        - (4 * m)
          * (unequalFixedDifferenceFourRealCanonicalLinearFactor1
              m θ (P ω) * (V ω ^ 2 / L ω)) ∂ℙ := by
            apply integral_congr_ae
            filter_upwards [] with ω
            exact unequalFixedDifferenceFourRealCanonicalLinearH_expand
              m θ (P ω) (L ω) (V ω)
    _ =
      unequalFixedDifferenceFourRealC m
        * (∫ ω,
          unequalFixedDifferenceFourRealCanonicalLinearFactor0
            m θ (P ω) * V ω ∂ℙ)
      - (4 * m)
        * (∫ ω,
          unequalFixedDifferenceFourRealCanonicalLinearFactor1
              m θ (P ω)
            * (V ω ^ 2 / L ω) ∂ℙ) := by
          rw [integral_sub
            (hterm0.const_mul (unequalFixedDifferenceFourRealC m))
            (hterm1.const_mul (4 * m)),
            integral_const_mul, integral_const_mul]
    _ =
      unequalFixedDifferenceFourRealC m
        * (∫ ω,
          unequalFixedDifferenceFourRealCanonicalLinearFactor0
            m θ (P ω) ∂ℙ)
      - (4 * m)
        * ((3 / (2 * (2 * m - 1)))
          * ∫ ω,
            unequalFixedDifferenceFourRealCanonicalLinearFactor1
              m θ (P ω) ∂ℙ) := by
          rw [hfactor0, hfactor1]
    _ =
      unequalFixedDifferenceFourRealC m
        * (∫ ω,
          unequalFixedDifferenceFourRealCanonicalLinearFactor0
            m θ (P ω) ∂ℙ)
      - unequalFixedDifferenceFourRealK m
        * (∫ ω,
          unequalFixedDifferenceFourRealCanonicalLinearFactor1
            m θ (P ω) ∂ℙ) := by
          rw [← unequalFixedDifferenceFourRealK_eq_gammaMoment hm]
          ring
    _ =
      ∫ ω,
        unequalFixedDifferenceFourRealCanonicalLinearPIntegrand
          m θ (P ω) ∂ℙ := hreduced.symm

/-! ## Quadratic product reduction -/

/--
Integrating out `L,V` reduces the full quadratic canonical moment to the
one-dimensional `P` integrand.
-/
theorem unequalFixedDifferenceFourRealCanonicalQuadraticH_product_reduction
    {m : ℝ} (hm : 7 ≤ m)
    (θ : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV :
      ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom :
      GeneralCanonicalFiveMoments (2 * m) L V ℙ)
    (hPint :
      UnequalFixedDifferenceFourRealCanonicalPFactorIntegrability
        m θ P ℙ) :
    (∫ ω,
      V ω * unequalFixedDifferenceFourRealCanonicalH
          m θ (P ω) (L ω) (V ω) ^ 2 ∂ℙ)
      =
    ∫ ω,
      unequalFixedDifferenceFourRealCanonicalQuadraticPIntegrand
        m θ (P ω) ∂ℙ := by
  obtain ⟨hV2L_int, hV2L_mean⟩ :=
    general_integral_v_sq_div_l
      (2 * m) L V ℙ hVL hmom
  obtain ⟨hV3L2_int, hV3L2_mean⟩ :=
    general_integral_v_cube_div_l_sq
      (2 * m) L V ℙ hVL hmom
  have hP0V :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
            m θ (P ω))
        V ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
          m θ)
        (by fun_prop : Measurable fun z : ℝ × ℝ => z.2)
  have hP1V2L :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
            m θ (P ω))
        (fun ω => V ω ^ 2 / L ω) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
          m θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 2 / z.1)
  have hP2V3L2 :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
            m θ (P ω))
        (fun ω => V ω ^ 3 / L ω ^ 2) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
          m θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 3 / z.1 ^ 2)
  have hterm0 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
              m θ (P ω)
            * V ω) ℙ :=
    hP0V.integrable_mul hPint.quadratic0 hmom.v_integrable
  have hterm1 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
              m θ (P ω)
            * (V ω ^ 2 / L ω)) ℙ :=
    hP1V2L.integrable_mul hPint.quadratic1 hV2L_int
  have hterm2 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
              m θ (P ω)
            * (V ω ^ 3 / L ω ^ 2)) ℙ :=
    hP2V3L2.integrable_mul hPint.quadratic2 hV3L2_int
  have hfactor0 :
      (∫ ω,
        unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
            m θ (P ω)
          * V ω ∂ℙ)
        =
      ∫ ω,
        unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
          m θ (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω,
            unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
              m θ (P ω) ∂ℙ)
            * ∫ ω, V ω ∂ℙ :=
        hP0V.integral_fun_mul_eq_mul_integral
          hPint.quadratic0.aestronglyMeasurable
          hmom.v_integrable.aestronglyMeasurable
      _ = _ := by rw [hmom.v_mean, mul_one]
  have hfactor1 :
      (∫ ω,
        unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
            m θ (P ω)
          * (V ω ^ 2 / L ω) ∂ℙ)
        =
      (3 / (2 * (2 * m - 1)))
        * ∫ ω,
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
            m θ (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω,
            unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
              m θ (P ω) ∂ℙ)
            * ∫ ω, V ω ^ 2 / L ω ∂ℙ :=
        hP1V2L.integral_fun_mul_eq_mul_integral
          hPint.quadratic1.aestronglyMeasurable
          hV2L_int.aestronglyMeasurable
      _ = _ := by
        rw [hV2L_mean]
        ring
  have hfactor2 :
      (∫ ω,
        unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
            m θ (P ω)
          * (V ω ^ 3 / L ω ^ 2) ∂ℙ)
        =
      (15 /
        (4 * (2 * m - 1)
          * (2 * m - 2)))
        * ∫ ω,
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
            m θ (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω,
            unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
              m θ (P ω) ∂ℙ)
            * ∫ ω, V ω ^ 3 / L ω ^ 2 ∂ℙ :=
        hP2V3L2.integral_fun_mul_eq_mul_integral
          hPint.quadratic2.aestronglyMeasurable
          hV3L2_int.aestronglyMeasurable
      _ = _ := by
        rw [hV3L2_mean]
        ring
  have hreduced :
      (∫ ω,
        unequalFixedDifferenceFourRealCanonicalQuadraticPIntegrand
          m θ (P ω) ∂ℙ)
        =
      unequalFixedDifferenceFourRealC m ^ 2
        * (∫ ω,
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
            m θ (P ω) ∂ℙ)
      - (2 * unequalFixedDifferenceFourRealK m
          * unequalFixedDifferenceFourRealC m)
        * (∫ ω,
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
            m θ (P ω) ∂ℙ)
      + unequalFixedDifferenceFourRealEll m
        * (∫ ω,
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
            m θ (P ω) ∂ℙ) := by
    calc
      _ =
          ∫ ω,
            unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
                m θ (P ω)
                * unequalFixedDifferenceFourRealC m ^ 2
              - (2 * unequalFixedDifferenceFourRealK m
                  * unequalFixedDifferenceFourRealC m)
                * unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
                  m θ (P ω)
              + unequalFixedDifferenceFourRealEll m
                * unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
                  m θ (P ω) ∂ℙ := by
            rfl
      _ =
          (∫ ω,
            unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
                m θ (P ω)
                * unequalFixedDifferenceFourRealC m ^ 2
              - (2 * unequalFixedDifferenceFourRealK m
                  * unequalFixedDifferenceFourRealC m)
                * unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
                  m θ (P ω) ∂ℙ)
            +
          ∫ ω,
            unequalFixedDifferenceFourRealEll m
              * unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
                m θ (P ω) ∂ℙ := by
            simpa only [Pi.add_apply, Pi.sub_apply] using
              integral_add
                ((hPint.quadratic0.mul_const
                    (unequalFixedDifferenceFourRealC m ^ 2)).sub
                  (hPint.quadratic1.const_mul
                    (2 * unequalFixedDifferenceFourRealK m
                      * unequalFixedDifferenceFourRealC m)))
                (hPint.quadratic2.const_mul
                  (unequalFixedDifferenceFourRealEll m))
      _ =
          ((∫ ω,
            unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
                m θ (P ω)
              * unequalFixedDifferenceFourRealC m ^ 2 ∂ℙ)
            -
          ∫ ω,
            (2 * unequalFixedDifferenceFourRealK m
                * unequalFixedDifferenceFourRealC m)
              * unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
                m θ (P ω) ∂ℙ)
            +
          ∫ ω,
            unequalFixedDifferenceFourRealEll m
              * unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
                m θ (P ω) ∂ℙ := by
            rw [integral_sub
              (hPint.quadratic0.mul_const
                (unequalFixedDifferenceFourRealC m ^ 2))
              (hPint.quadratic1.const_mul
                (2 * unequalFixedDifferenceFourRealK m
                  * unequalFixedDifferenceFourRealC m))]
      _ = _ := by
        rw [integral_mul_const, integral_const_mul, integral_const_mul]
        ring
  calc
    (∫ ω,
      V ω * unequalFixedDifferenceFourRealCanonicalH
          m θ (P ω) (L ω) (V ω) ^ 2 ∂ℙ)
        =
      ∫ ω,
        unequalFixedDifferenceFourRealC m ^ 2
          * (unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
              m θ (P ω) * V ω)
        - (8 * m * unequalFixedDifferenceFourRealC m)
          * (unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
              m θ (P ω) * (V ω ^ 2 / L ω))
        + (4 * m) ^ 2
          * (unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
              m θ (P ω) * (V ω ^ 3 / L ω ^ 2)) ∂ℙ := by
            apply integral_congr_ae
            filter_upwards [] with ω
            exact unequalFixedDifferenceFourRealCanonicalQuadraticH_expand
              m θ (P ω) (L ω) (V ω)
    _ =
      unequalFixedDifferenceFourRealC m ^ 2
        * (∫ ω,
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
            m θ (P ω) * V ω ∂ℙ)
      - (8 * m * unequalFixedDifferenceFourRealC m)
        * (∫ ω,
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
              m θ (P ω)
            * (V ω ^ 2 / L ω) ∂ℙ)
      + (4 * m) ^ 2
        * (∫ ω,
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
              m θ (P ω)
            * (V ω ^ 3 / L ω ^ 2) ∂ℙ) := by
          calc
            _ =
                (∫ ω,
                  unequalFixedDifferenceFourRealC m ^ 2
                    * (unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
                        m θ (P ω) * V ω)
                  - (8 * m * unequalFixedDifferenceFourRealC m)
                    * (unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
                        m θ (P ω) * (V ω ^ 2 / L ω)) ∂ℙ)
                +
                ∫ ω,
                  (4 * m) ^ 2
                    * (unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
                        m θ (P ω)
                      * (V ω ^ 3 / L ω ^ 2)) ∂ℙ := by
                      simpa only [Pi.add_apply, Pi.sub_apply] using
                        integral_add
                          ((hterm0.const_mul
                              (unequalFixedDifferenceFourRealC m ^ 2)).sub
                            (hterm1.const_mul
                              (8 * m
                                * unequalFixedDifferenceFourRealC m)))
                          (hterm2.const_mul ((4 * m) ^ 2))
            _ =
                ((∫ ω,
                  unequalFixedDifferenceFourRealC m ^ 2
                    * (unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
                        m θ (P ω) * V ω) ∂ℙ)
                -
                ∫ ω,
                  (8 * m * unequalFixedDifferenceFourRealC m)
                    * (unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
                        m θ (P ω) * (V ω ^ 2 / L ω)) ∂ℙ)
                +
                ∫ ω,
                  (4 * m) ^ 2
                    * (unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
                        m θ (P ω)
                      * (V ω ^ 3 / L ω ^ 2)) ∂ℙ := by
                      rw [integral_sub
                        (hterm0.const_mul
                          (unequalFixedDifferenceFourRealC m ^ 2))
                        (hterm1.const_mul
                          (8 * m
                            * unequalFixedDifferenceFourRealC m))]
            _ = _ := by
              rw [integral_const_mul, integral_const_mul,
                integral_const_mul]
    _ =
      unequalFixedDifferenceFourRealC m ^ 2
        * (∫ ω,
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
            m θ (P ω) ∂ℙ)
      - (8 * m * unequalFixedDifferenceFourRealC m)
        * ((3 / (2 * (2 * m - 1)))
          * ∫ ω,
            unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
              m θ (P ω) ∂ℙ)
      + (4 * m) ^ 2
        * ((15 /
          (4 * (2 * m - 1)
            * (2 * m - 2)))
          * ∫ ω,
            unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
              m θ (P ω) ∂ℙ) := by
          rw [hfactor0, hfactor1, hfactor2]
    _ =
      unequalFixedDifferenceFourRealC m ^ 2
        * (∫ ω,
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
            m θ (P ω) ∂ℙ)
      - (2 * unequalFixedDifferenceFourRealK m
          * unequalFixedDifferenceFourRealC m)
        * (∫ ω,
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
            m θ (P ω) ∂ℙ)
      + unequalFixedDifferenceFourRealEll m
        * (∫ ω,
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
            m θ (P ω) ∂ℙ) := by
          rw [← unequalFixedDifferenceFourRealTwoKCMoment hm,
            ← unequalFixedDifferenceFourRealEll_eq_gammaMoment hm]
          ring
    _ =
      ∫ ω,
        unequalFixedDifferenceFourRealCanonicalQuadraticPIntegrand
          m θ (P ω) ∂ℙ := hreduced.symm

/-! ## Integrability of the full canonical moments -/

theorem unequalFixedDifferenceFourRealCanonicalLinearH_integrable_of_product
    (m : ℝ) (θ : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV :
      ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom :
      GeneralCanonicalFiveMoments (2 * m) L V ℙ)
    (hPint :
      UnequalFixedDifferenceFourRealCanonicalPFactorIntegrability
        m θ P ℙ) :
    Integrable
      (fun ω =>
        V ω * (unequalFixedDifferenceFourRealCanonicalR m θ (P ω) - θ)
          * unequalFixedDifferenceFourRealCanonicalH
              m θ (P ω) (L ω) (V ω)) ℙ := by
  obtain ⟨hV2L_int, _⟩ :=
    general_integral_v_sq_div_l
      (2 * m) L V ℙ hVL hmom
  have hP0V :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalLinearFactor0
            m θ (P ω))
        V ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourRealCanonicalLinearFactor0
          m θ)
        (by fun_prop : Measurable fun z : ℝ × ℝ => z.2)
  have hP1V2L :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalLinearFactor1
            m θ (P ω))
        (fun ω => V ω ^ 2 / L ω) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourRealCanonicalLinearFactor1
          m θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 2 / z.1)
  have hterm0 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalLinearFactor0
              m θ (P ω)
            * V ω) ℙ :=
    hP0V.integrable_mul hPint.linear0 hmom.v_integrable
  have hterm1 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalLinearFactor1
              m θ (P ω)
            * (V ω ^ 2 / L ω)) ℙ :=
    hP1V2L.integrable_mul hPint.linear1 hV2L_int
  apply
    ((hterm0.const_mul (unequalFixedDifferenceFourRealC m)).sub
      (hterm1.const_mul (4 * m))).congr
  filter_upwards [] with ω
  simpa only [Pi.sub_apply] using
    (unequalFixedDifferenceFourRealCanonicalLinearH_expand
      m θ (P ω) (L ω) (V ω)).symm

theorem unequalFixedDifferenceFourRealCanonicalQuadraticH_integrable_of_product
    (m : ℝ) (θ : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV :
      ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom :
      GeneralCanonicalFiveMoments (2 * m) L V ℙ)
    (hPint :
      UnequalFixedDifferenceFourRealCanonicalPFactorIntegrability
        m θ P ℙ) :
    Integrable
      (fun ω =>
        V ω * unequalFixedDifferenceFourRealCanonicalH
            m θ (P ω) (L ω) (V ω) ^ 2) ℙ := by
  obtain ⟨hV2L_int, _⟩ :=
    general_integral_v_sq_div_l
      (2 * m) L V ℙ hVL hmom
  obtain ⟨hV3L2_int, _⟩ :=
    general_integral_v_cube_div_l_sq
      (2 * m) L V ℙ hVL hmom
  have hP0V :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
            m θ (P ω))
        V ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
          m θ)
        (by fun_prop : Measurable fun z : ℝ × ℝ => z.2)
  have hP1V2L :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
            m θ (P ω))
        (fun ω => V ω ^ 2 / L ω) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
          m θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 2 / z.1)
  have hP2V3L2 :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
            m θ (P ω))
        (fun ω => V ω ^ 3 / L ω ^ 2) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
          m θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 3 / z.1 ^ 2)
  have hterm0 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
              m θ (P ω)
            * V ω) ℙ :=
    hP0V.integrable_mul hPint.quadratic0 hmom.v_integrable
  have hterm1 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
              m θ (P ω)
            * (V ω ^ 2 / L ω)) ℙ :=
    hP1V2L.integrable_mul hPint.quadratic1 hV2L_int
  have hterm2 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
              m θ (P ω)
            * (V ω ^ 3 / L ω ^ 2)) ℙ :=
    hP2V3L2.integrable_mul hPint.quadratic2 hV3L2_int
  apply
    (((hterm0.const_mul (unequalFixedDifferenceFourRealC m ^ 2)).sub
      (hterm1.const_mul
        (8 * m * unequalFixedDifferenceFourRealC m))).add
      (hterm2.const_mul ((4 * m) ^ 2))).congr
  filter_upwards [] with ω
  simpa only [Pi.add_apply, Pi.sub_apply] using
    (unequalFixedDifferenceFourRealCanonicalQuadraticH_expand
      m θ (P ω) (L ω) (V ω)).symm

/-! ## The two-moment risk bridge -/

theorem unequalFixedDifferenceFourRealCanonicalMomentBridge_of_product_reductions
    {m : ℝ} (hm : 7 ≤ m)
    (θ B C : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV :
      ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom :
      GeneralCanonicalFiveMoments (2 * m) L V ℙ)
    (hPint :
      UnequalFixedDifferenceFourRealCanonicalPFactorIntegrability
        m θ P ℙ)
    (hlinear :
      (∫ ω,
        unequalFixedDifferenceFourRealCanonicalLinearPIntegrand
          m θ (P ω) ∂ℙ) = B)
    (hquadratic :
      (∫ ω,
        unequalFixedDifferenceFourRealCanonicalQuadraticPIntegrand
          m θ (P ω) ∂ℙ) = C) :
    UnequalDampedMomentBridge θ B C
      (fun ω => unequalFixedDifferenceFourRealCanonicalR m θ (P ω))
      (fun ω =>
        unequalFixedDifferenceFourRealCanonicalH
          m θ (P ω) (L ω) (V ω))
      V ℙ := by
  refine
    { linear_integrable :=
        unequalFixedDifferenceFourRealCanonicalLinearH_integrable_of_product
          m θ P L V ℙ hP_LV hVL hmom hPint
      quadratic_integrable :=
        unequalFixedDifferenceFourRealCanonicalQuadraticH_integrable_of_product
          m θ P L V ℙ hP_LV hVL hmom hPint
      linear_moment := ?_
      quadratic_moment := ?_ }
  · rw [unequalFixedDifferenceFourRealCanonicalLinearH_product_reduction
      hm θ P L V ℙ hP_LV hVL hmom hPint, hlinear]
  · rw [unequalFixedDifferenceFourRealCanonicalQuadraticH_product_reduction
      hm θ P L V ℙ hP_LV hVL hmom hPint, hquadratic]

/--
Specialize the generic bridge to the direct canonical coefficients
`B_m(θ)` and `C_m(θ)`.
-/
theorem unequalFixedDifferenceFourRealCanonicalMomentBridge_of_canonical_expectations
    {m : ℝ} (hm : 7 ≤ m)
    (θ : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV :
      ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom :
      GeneralCanonicalFiveMoments (2 * m) L V ℙ)
    (hPint :
      UnequalFixedDifferenceFourRealCanonicalPFactorIntegrability
        m θ P ℙ)
    (hB :
      (∫ ω,
        unequalFixedDifferenceFourRealCanonicalBIntegrand
          m θ (P ω) ∂ℙ)
        = unequalFixedDifferenceFourRealCanonicalB m θ)
    (hC :
      (∫ ω,
        unequalFixedDifferenceFourRealCanonicalCIntegrand
          m θ (P ω) ∂ℙ)
        = unequalFixedDifferenceFourRealCanonicalC m θ) :
    UnequalDampedMomentBridge θ
      (unequalFixedDifferenceFourRealCanonicalB m θ)
      (unequalFixedDifferenceFourRealCanonicalC m θ)
      (fun ω => unequalFixedDifferenceFourRealCanonicalR m θ (P ω))
      (fun ω =>
        unequalFixedDifferenceFourRealCanonicalH
          m θ (P ω) (L ω) (V ω))
      V ℙ := by
  apply
    unequalFixedDifferenceFourRealCanonicalMomentBridge_of_product_reductions
      hm θ
      (unequalFixedDifferenceFourRealCanonicalB m θ)
      (unequalFixedDifferenceFourRealCanonicalC m θ)
      P L V ℙ hP_LV hVL hmom hPint
  · calc
      (∫ ω,
        unequalFixedDifferenceFourRealCanonicalLinearPIntegrand
          m θ (P ω) ∂ℙ)
          =
        ∫ ω,
          unequalFixedDifferenceFourRealCanonicalBIntegrand
            m θ (P ω) ∂ℙ := by
              apply integral_congr_ae
              filter_upwards [] with ω
              exact
                unequalFixedDifferenceFourRealCanonicalLinearPIntegrand_eq_BIntegrand
                  m θ (P ω)
      _ = unequalFixedDifferenceFourRealCanonicalB m θ := hB
  · calc
      (∫ ω,
        unequalFixedDifferenceFourRealCanonicalQuadraticPIntegrand
          m θ (P ω) ∂ℙ)
          =
        ∫ ω,
          unequalFixedDifferenceFourRealCanonicalCIntegrand
            m θ (P ω) ∂ℙ := by
              apply integral_congr_ae
              filter_upwards [] with ω
              exact
                unequalFixedDifferenceFourRealCanonicalQuadraticPIntegrand_eq_CIntegrand
                  m θ (P ω)
      _ = unequalFixedDifferenceFourRealCanonicalC m θ := hC

end

end GraybillDeal
