import GraybillDeal.UnequalFixedDifferenceFourCanonicalReduced
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

private theorem unequalFD4CanonicalProduct_cast_seven_le
    {m : ℕ} (hm : 7 ≤ m) :
    (7 : ℝ) ≤ (m : ℝ) := by
  exact_mod_cast hm

/--
The coefficient `4m` in the canonical quadratic statistic, multiplied by
`E[V²/L]`, is exactly the reduced linear constant `K_m`.
-/
theorem unequalFixedDifferenceFourK_eq_gammaMoment
    {m : ℕ} (hm : 7 ≤ m) :
    4 * (m : ℝ)
        * (3 / (2 * (2 * (m : ℝ) - 1)))
      =
    unequalFixedDifferenceFourK m := by
  have hmR := unequalFD4CanonicalProduct_cast_seven_le hm
  have hden : 2 * (m : ℝ) - 1 ≠ 0 := by linarith
  unfold unequalFixedDifferenceFourK
  field_simp [hden]
  ring

/--
The mixed term in the square of the canonical perturbation produces
`2 K_m c_m`.
-/
theorem unequalFixedDifferenceFourTwoKCMoment
    {m : ℕ} (hm : 7 ≤ m) :
    (8 * (m : ℝ) * unequalFixedDifferenceFourC m)
        * (3 / (2 * (2 * (m : ℝ) - 1)))
      =
    2 * unequalFixedDifferenceFourK m
        * unequalFixedDifferenceFourC m := by
  rw [show
    (8 * (m : ℝ) * unequalFixedDifferenceFourC m)
          * (3 / (2 * (2 * (m : ℝ) - 1)))
      =
    2 * unequalFixedDifferenceFourC m
      * (4 * (m : ℝ)
        * (3 / (2 * (2 * (m : ℝ) - 1)))) by ring,
    unequalFixedDifferenceFourK_eq_gammaMoment hm]
  ring

/--
The squared `4m` coefficient, multiplied by `E[V³/L²]`, is exactly
the reduced quadratic constant `Ell_m`.
-/
theorem unequalFixedDifferenceFourEll_eq_gammaMoment
    {m : ℕ} (hm : 7 ≤ m) :
    (4 * (m : ℝ)) ^ 2
        * (15 /
          (4 * (2 * (m : ℝ) - 1)
            * (2 * (m : ℝ) - 2)))
      =
    unequalFixedDifferenceFourEll m := by
  have hmR := unequalFD4CanonicalProduct_cast_seven_le hm
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have h2m1 : 2 * (m : ℝ) - 1 ≠ 0 := by linarith
  have h2m2 : 2 * (m : ℝ) - 2 ≠ 0 := by linarith
  unfold unequalFixedDifferenceFourEll
  field_simp [hm1, h2m1, h2m2]
  ring

/-! ## Canonical coefficient factors -/

/-- Coefficient of `V` in the family linear mixed-moment expansion. -/
def unequalFixedDifferenceFourCanonicalLinearFactor0
    (m : ℕ) (θ p : ℝ) : ℝ :=
  (unequalFixedDifferenceFourCanonicalR m θ p - θ)
    * unequalDampedPhi
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourKappa m)
        (unequalFixedDifferenceFourCanonicalR m θ p)

/-- Coefficient of `V²/L` in the family linear mixed-moment expansion. -/
def unequalFixedDifferenceFourCanonicalLinearFactor1
    (m : ℕ) (θ p : ℝ) : ℝ :=
  unequalFixedDifferenceFourCanonicalLinearFactor0 m θ p
    / unequalFixedDifferenceFourCanonicalDenom m θ p

/-- Coefficient of `V` in the family quadratic mixed-moment expansion. -/
def unequalFixedDifferenceFourCanonicalQuadraticFactor0
    (m : ℕ) (θ p : ℝ) : ℝ :=
  unequalDampedPhi
      (unequalFixedDifferenceFourT m)
      (unequalFixedDifferenceFourKappa m)
      (unequalFixedDifferenceFourCanonicalR m θ p) ^ 2

/-- Coefficient of `V²/L` in the family quadratic mixed-moment expansion. -/
def unequalFixedDifferenceFourCanonicalQuadraticFactor1
    (m : ℕ) (θ p : ℝ) : ℝ :=
  unequalFixedDifferenceFourCanonicalQuadraticFactor0 m θ p
    / unequalFixedDifferenceFourCanonicalDenom m θ p

/-- Coefficient of `V³/L²` in the family quadratic mixed-moment expansion. -/
def unequalFixedDifferenceFourCanonicalQuadraticFactor2
    (m : ℕ) (θ p : ℝ) : ℝ :=
  unequalFixedDifferenceFourCanonicalQuadraticFactor0 m θ p
    / unequalFixedDifferenceFourCanonicalDenom m θ p ^ 2

/-- Reduced linear `P`-integrand after taking the `L,V` moments. -/
def unequalFixedDifferenceFourCanonicalLinearPIntegrand
    (m : ℕ) (θ p : ℝ) : ℝ :=
  unequalFixedDifferenceFourCanonicalLinearFactor0 m θ p
      * unequalFixedDifferenceFourC m
    - unequalFixedDifferenceFourK m
      * unequalFixedDifferenceFourCanonicalLinearFactor1 m θ p

/-- Reduced quadratic `P`-integrand after taking the `L,V` moments. -/
def unequalFixedDifferenceFourCanonicalQuadraticPIntegrand
    (m : ℕ) (θ p : ℝ) : ℝ :=
  unequalFixedDifferenceFourCanonicalQuadraticFactor0 m θ p
      * unequalFixedDifferenceFourC m ^ 2
    - (2 * unequalFixedDifferenceFourK m
        * unequalFixedDifferenceFourC m)
      * unequalFixedDifferenceFourCanonicalQuadraticFactor1 m θ p
    + unequalFixedDifferenceFourEll m
      * unequalFixedDifferenceFourCanonicalQuadraticFactor2 m θ p

theorem measurable_unequalFixedDifferenceFourCanonicalLinearFactor0
    (m : ℕ) (θ : ℝ) :
    Measurable
      (unequalFixedDifferenceFourCanonicalLinearFactor0 m θ) := by
  unfold unequalFixedDifferenceFourCanonicalLinearFactor0
    unequalFixedDifferenceFourCanonicalR
    unequalFixedDifferenceFourCanonicalDenom
    unequalDampedPhi unequalDampedInner
  fun_prop

theorem measurable_unequalFixedDifferenceFourCanonicalLinearFactor1
    (m : ℕ) (θ : ℝ) :
    Measurable
      (unequalFixedDifferenceFourCanonicalLinearFactor1 m θ) := by
  unfold unequalFixedDifferenceFourCanonicalLinearFactor1
  exact
    (measurable_unequalFixedDifferenceFourCanonicalLinearFactor0 m θ).div
      (by
        unfold unequalFixedDifferenceFourCanonicalDenom
        fun_prop)

theorem measurable_unequalFixedDifferenceFourCanonicalQuadraticFactor0
    (m : ℕ) (θ : ℝ) :
    Measurable
      (unequalFixedDifferenceFourCanonicalQuadraticFactor0 m θ) := by
  unfold unequalFixedDifferenceFourCanonicalQuadraticFactor0
    unequalFixedDifferenceFourCanonicalR
    unequalFixedDifferenceFourCanonicalDenom
    unequalDampedPhi unequalDampedInner
  fun_prop

theorem measurable_unequalFixedDifferenceFourCanonicalQuadraticFactor1
    (m : ℕ) (θ : ℝ) :
    Measurable
      (unequalFixedDifferenceFourCanonicalQuadraticFactor1 m θ) := by
  unfold unequalFixedDifferenceFourCanonicalQuadraticFactor1
  exact
    (measurable_unequalFixedDifferenceFourCanonicalQuadraticFactor0 m θ).div
      (by
        unfold unequalFixedDifferenceFourCanonicalDenom
        fun_prop)

theorem measurable_unequalFixedDifferenceFourCanonicalQuadraticFactor2
    (m : ℕ) (θ : ℝ) :
    Measurable
      (unequalFixedDifferenceFourCanonicalQuadraticFactor2 m θ) := by
  unfold unequalFixedDifferenceFourCanonicalQuadraticFactor2
  exact
    (measurable_unequalFixedDifferenceFourCanonicalQuadraticFactor0 m θ).div
      (by
        unfold unequalFixedDifferenceFourCanonicalDenom
        fun_prop)

/-- Integrability of the five family-indexed `P` coefficient functions. -/
structure UnequalFixedDifferenceFourCanonicalPFactorIntegrability
    (m : ℕ) (θ : ℝ) (P : Ω → ℝ) (ℙ : Measure Ω) : Prop where
  linear0 :
    Integrable
      (fun ω =>
        unequalFixedDifferenceFourCanonicalLinearFactor0
          m θ (P ω)) ℙ
  linear1 :
    Integrable
      (fun ω =>
        unequalFixedDifferenceFourCanonicalLinearFactor1
          m θ (P ω)) ℙ
  quadratic0 :
    Integrable
      (fun ω =>
        unequalFixedDifferenceFourCanonicalQuadraticFactor0
          m θ (P ω)) ℙ
  quadratic1 :
    Integrable
      (fun ω =>
        unequalFixedDifferenceFourCanonicalQuadraticFactor1
          m θ (P ω)) ℙ
  quadratic2 :
    Integrable
      (fun ω =>
        unequalFixedDifferenceFourCanonicalQuadraticFactor2
          m θ (P ω)) ℙ

/-! ## Pointwise mixed-moment expansions -/

/--
Pointwise expansion of `V (R-θ) H` into the two products that independence
will factor.
-/
theorem unequalFixedDifferenceFourCanonicalLinearH_expand
    (m : ℕ) (θ p l v : ℝ) :
    v * (unequalFixedDifferenceFourCanonicalR m θ p - θ)
        * unequalFixedDifferenceFourCanonicalH m θ p l v
      =
    unequalFixedDifferenceFourC m
      * (unequalFixedDifferenceFourCanonicalLinearFactor0
          m θ p * v)
    - (4 * (m : ℝ))
      * (unequalFixedDifferenceFourCanonicalLinearFactor1
          m θ p * (v ^ 2 / l)) := by
  unfold unequalFixedDifferenceFourCanonicalH
    unequalFixedDifferenceFourCanonicalQ
    unequalFixedDifferenceFourCanonicalLinearFactor1
    unequalFixedDifferenceFourCanonicalLinearFactor0
  simp only [div_eq_mul_inv, mul_inv]
  ring

/--
Pointwise expansion of `V H²` into the three products that independence
will factor.
-/
theorem unequalFixedDifferenceFourCanonicalQuadraticH_expand
    (m : ℕ) (θ p l v : ℝ) :
    v * unequalFixedDifferenceFourCanonicalH m θ p l v ^ 2
      =
    unequalFixedDifferenceFourC m ^ 2
      * (unequalFixedDifferenceFourCanonicalQuadraticFactor0
          m θ p * v)
    - (8 * (m : ℝ) * unequalFixedDifferenceFourC m)
      * (unequalFixedDifferenceFourCanonicalQuadraticFactor1
          m θ p * (v ^ 2 / l))
    + (4 * (m : ℝ)) ^ 2
      * (unequalFixedDifferenceFourCanonicalQuadraticFactor2
          m θ p * (v ^ 3 / l ^ 2)) := by
  unfold unequalFixedDifferenceFourCanonicalH
    unequalFixedDifferenceFourCanonicalQ
    unequalFixedDifferenceFourCanonicalQuadraticFactor2
    unequalFixedDifferenceFourCanonicalQuadraticFactor1
    unequalFixedDifferenceFourCanonicalQuadraticFactor0
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-! ## Identification of the reduced `P` integrands -/

theorem unequalFixedDifferenceFourCanonicalLinearPIntegrand_eq_BIntegrand
    (m : ℕ) (θ p : ℝ) :
    unequalFixedDifferenceFourCanonicalLinearPIntegrand m θ p
      =
    unequalFixedDifferenceFourCanonicalBIntegrand m θ p := by
  unfold unequalFixedDifferenceFourCanonicalLinearPIntegrand
    unequalFixedDifferenceFourCanonicalLinearFactor1
    unequalFixedDifferenceFourCanonicalLinearFactor0
    unequalFixedDifferenceFourCanonicalBIntegrand
  ring

theorem unequalFixedDifferenceFourCanonicalQuadraticPIntegrand_eq_CIntegrand
    (m : ℕ) (θ p : ℝ) :
    unequalFixedDifferenceFourCanonicalQuadraticPIntegrand m θ p
      =
    unequalFixedDifferenceFourCanonicalCIntegrand m θ p := by
  unfold unequalFixedDifferenceFourCanonicalQuadraticPIntegrand
    unequalFixedDifferenceFourCanonicalQuadraticFactor2
    unequalFixedDifferenceFourCanonicalQuadraticFactor1
    unequalFixedDifferenceFourCanonicalQuadraticFactor0
    unequalFixedDifferenceFourCanonicalCIntegrand
    unequalFixedDifferenceFourCKernel
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-! ## Linear product reduction -/

/--
Integrating out `L,V` reduces the full linear canonical moment to the
one-dimensional `P` integrand.
-/
theorem unequalFixedDifferenceFourCanonicalLinearH_product_reduction
    {m : ℕ} (hm : 7 ≤ m)
    (θ : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV :
      ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom :
      GeneralCanonicalFiveMoments (2 * (m : ℝ)) L V ℙ)
    (hPint :
      UnequalFixedDifferenceFourCanonicalPFactorIntegrability
        m θ P ℙ) :
    (∫ ω,
      V ω * (unequalFixedDifferenceFourCanonicalR m θ (P ω) - θ)
        * unequalFixedDifferenceFourCanonicalH
            m θ (P ω) (L ω) (V ω) ∂ℙ)
      =
    ∫ ω,
      unequalFixedDifferenceFourCanonicalLinearPIntegrand
        m θ (P ω) ∂ℙ := by
  obtain ⟨hV2L_int, hV2L_mean⟩ :=
    general_integral_v_sq_div_l
      (2 * (m : ℝ)) L V ℙ hVL hmom
  have hP0V :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourCanonicalLinearFactor0
            m θ (P ω))
        V ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourCanonicalLinearFactor0
          m θ)
        (by fun_prop : Measurable fun z : ℝ × ℝ => z.2)
  have hP1V2L :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourCanonicalLinearFactor1
            m θ (P ω))
        (fun ω => V ω ^ 2 / L ω) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourCanonicalLinearFactor1
          m θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 2 / z.1)
  have hterm0 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourCanonicalLinearFactor0
              m θ (P ω)
            * V ω) ℙ :=
    hP0V.integrable_mul hPint.linear0 hmom.v_integrable
  have hterm1 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourCanonicalLinearFactor1
              m θ (P ω)
            * (V ω ^ 2 / L ω)) ℙ :=
    hP1V2L.integrable_mul hPint.linear1 hV2L_int
  have hfactor0 :
      (∫ ω,
        unequalFixedDifferenceFourCanonicalLinearFactor0
            m θ (P ω)
          * V ω ∂ℙ)
        =
      ∫ ω,
        unequalFixedDifferenceFourCanonicalLinearFactor0
          m θ (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω,
            unequalFixedDifferenceFourCanonicalLinearFactor0
              m θ (P ω) ∂ℙ)
            * ∫ ω, V ω ∂ℙ :=
        hP0V.integral_fun_mul_eq_mul_integral
          hPint.linear0.aestronglyMeasurable
          hmom.v_integrable.aestronglyMeasurable
      _ = _ := by rw [hmom.v_mean, mul_one]
  have hfactor1 :
      (∫ ω,
        unequalFixedDifferenceFourCanonicalLinearFactor1
            m θ (P ω)
          * (V ω ^ 2 / L ω) ∂ℙ)
        =
      (3 / (2 * (2 * (m : ℝ) - 1)))
        * ∫ ω,
          unequalFixedDifferenceFourCanonicalLinearFactor1
            m θ (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω,
            unequalFixedDifferenceFourCanonicalLinearFactor1
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
        unequalFixedDifferenceFourCanonicalLinearPIntegrand
          m θ (P ω) ∂ℙ)
        =
      unequalFixedDifferenceFourC m
          * (∫ ω,
            unequalFixedDifferenceFourCanonicalLinearFactor0
              m θ (P ω) ∂ℙ)
        - unequalFixedDifferenceFourK m
          * (∫ ω,
            unequalFixedDifferenceFourCanonicalLinearFactor1
              m θ (P ω) ∂ℙ) := by
    calc
      _ =
          ∫ ω,
            unequalFixedDifferenceFourCanonicalLinearFactor0
                m θ (P ω)
                * unequalFixedDifferenceFourC m
              - unequalFixedDifferenceFourK m
                * unequalFixedDifferenceFourCanonicalLinearFactor1
                  m θ (P ω) ∂ℙ := by
            rfl
      _ =
          (∫ ω,
            unequalFixedDifferenceFourCanonicalLinearFactor0
                m θ (P ω)
              * unequalFixedDifferenceFourC m ∂ℙ)
            -
          ∫ ω,
            unequalFixedDifferenceFourK m
              * unequalFixedDifferenceFourCanonicalLinearFactor1
                m θ (P ω) ∂ℙ := by
            rw [integral_sub
              (hPint.linear0.mul_const
                (unequalFixedDifferenceFourC m))
              (hPint.linear1.const_mul
                (unequalFixedDifferenceFourK m))]
      _ = _ := by
        rw [integral_mul_const, integral_const_mul]
        ring
  calc
    (∫ ω,
      V ω * (unequalFixedDifferenceFourCanonicalR m θ (P ω) - θ)
        * unequalFixedDifferenceFourCanonicalH
            m θ (P ω) (L ω) (V ω) ∂ℙ)
        =
      ∫ ω,
        unequalFixedDifferenceFourC m
          * (unequalFixedDifferenceFourCanonicalLinearFactor0
              m θ (P ω) * V ω)
        - (4 * (m : ℝ))
          * (unequalFixedDifferenceFourCanonicalLinearFactor1
              m θ (P ω) * (V ω ^ 2 / L ω)) ∂ℙ := by
            apply integral_congr_ae
            filter_upwards [] with ω
            exact unequalFixedDifferenceFourCanonicalLinearH_expand
              m θ (P ω) (L ω) (V ω)
    _ =
      unequalFixedDifferenceFourC m
        * (∫ ω,
          unequalFixedDifferenceFourCanonicalLinearFactor0
            m θ (P ω) * V ω ∂ℙ)
      - (4 * (m : ℝ))
        * (∫ ω,
          unequalFixedDifferenceFourCanonicalLinearFactor1
              m θ (P ω)
            * (V ω ^ 2 / L ω) ∂ℙ) := by
          rw [integral_sub
            (hterm0.const_mul (unequalFixedDifferenceFourC m))
            (hterm1.const_mul (4 * (m : ℝ))),
            integral_const_mul, integral_const_mul]
    _ =
      unequalFixedDifferenceFourC m
        * (∫ ω,
          unequalFixedDifferenceFourCanonicalLinearFactor0
            m θ (P ω) ∂ℙ)
      - (4 * (m : ℝ))
        * ((3 / (2 * (2 * (m : ℝ) - 1)))
          * ∫ ω,
            unequalFixedDifferenceFourCanonicalLinearFactor1
              m θ (P ω) ∂ℙ) := by
          rw [hfactor0, hfactor1]
    _ =
      unequalFixedDifferenceFourC m
        * (∫ ω,
          unequalFixedDifferenceFourCanonicalLinearFactor0
            m θ (P ω) ∂ℙ)
      - unequalFixedDifferenceFourK m
        * (∫ ω,
          unequalFixedDifferenceFourCanonicalLinearFactor1
            m θ (P ω) ∂ℙ) := by
          rw [← unequalFixedDifferenceFourK_eq_gammaMoment hm]
          ring
    _ =
      ∫ ω,
        unequalFixedDifferenceFourCanonicalLinearPIntegrand
          m θ (P ω) ∂ℙ := hreduced.symm

/-! ## Quadratic product reduction -/

/--
Integrating out `L,V` reduces the full quadratic canonical moment to the
one-dimensional `P` integrand.
-/
theorem unequalFixedDifferenceFourCanonicalQuadraticH_product_reduction
    {m : ℕ} (hm : 7 ≤ m)
    (θ : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV :
      ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom :
      GeneralCanonicalFiveMoments (2 * (m : ℝ)) L V ℙ)
    (hPint :
      UnequalFixedDifferenceFourCanonicalPFactorIntegrability
        m θ P ℙ) :
    (∫ ω,
      V ω * unequalFixedDifferenceFourCanonicalH
          m θ (P ω) (L ω) (V ω) ^ 2 ∂ℙ)
      =
    ∫ ω,
      unequalFixedDifferenceFourCanonicalQuadraticPIntegrand
        m θ (P ω) ∂ℙ := by
  obtain ⟨hV2L_int, hV2L_mean⟩ :=
    general_integral_v_sq_div_l
      (2 * (m : ℝ)) L V ℙ hVL hmom
  obtain ⟨hV3L2_int, hV3L2_mean⟩ :=
    general_integral_v_cube_div_l_sq
      (2 * (m : ℝ)) L V ℙ hVL hmom
  have hP0V :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourCanonicalQuadraticFactor0
            m θ (P ω))
        V ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourCanonicalQuadraticFactor0
          m θ)
        (by fun_prop : Measurable fun z : ℝ × ℝ => z.2)
  have hP1V2L :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourCanonicalQuadraticFactor1
            m θ (P ω))
        (fun ω => V ω ^ 2 / L ω) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourCanonicalQuadraticFactor1
          m θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 2 / z.1)
  have hP2V3L2 :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourCanonicalQuadraticFactor2
            m θ (P ω))
        (fun ω => V ω ^ 3 / L ω ^ 2) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourCanonicalQuadraticFactor2
          m θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 3 / z.1 ^ 2)
  have hterm0 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourCanonicalQuadraticFactor0
              m θ (P ω)
            * V ω) ℙ :=
    hP0V.integrable_mul hPint.quadratic0 hmom.v_integrable
  have hterm1 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourCanonicalQuadraticFactor1
              m θ (P ω)
            * (V ω ^ 2 / L ω)) ℙ :=
    hP1V2L.integrable_mul hPint.quadratic1 hV2L_int
  have hterm2 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourCanonicalQuadraticFactor2
              m θ (P ω)
            * (V ω ^ 3 / L ω ^ 2)) ℙ :=
    hP2V3L2.integrable_mul hPint.quadratic2 hV3L2_int
  have hfactor0 :
      (∫ ω,
        unequalFixedDifferenceFourCanonicalQuadraticFactor0
            m θ (P ω)
          * V ω ∂ℙ)
        =
      ∫ ω,
        unequalFixedDifferenceFourCanonicalQuadraticFactor0
          m θ (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω,
            unequalFixedDifferenceFourCanonicalQuadraticFactor0
              m θ (P ω) ∂ℙ)
            * ∫ ω, V ω ∂ℙ :=
        hP0V.integral_fun_mul_eq_mul_integral
          hPint.quadratic0.aestronglyMeasurable
          hmom.v_integrable.aestronglyMeasurable
      _ = _ := by rw [hmom.v_mean, mul_one]
  have hfactor1 :
      (∫ ω,
        unequalFixedDifferenceFourCanonicalQuadraticFactor1
            m θ (P ω)
          * (V ω ^ 2 / L ω) ∂ℙ)
        =
      (3 / (2 * (2 * (m : ℝ) - 1)))
        * ∫ ω,
          unequalFixedDifferenceFourCanonicalQuadraticFactor1
            m θ (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω,
            unequalFixedDifferenceFourCanonicalQuadraticFactor1
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
        unequalFixedDifferenceFourCanonicalQuadraticFactor2
            m θ (P ω)
          * (V ω ^ 3 / L ω ^ 2) ∂ℙ)
        =
      (15 /
        (4 * (2 * (m : ℝ) - 1)
          * (2 * (m : ℝ) - 2)))
        * ∫ ω,
          unequalFixedDifferenceFourCanonicalQuadraticFactor2
            m θ (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω,
            unequalFixedDifferenceFourCanonicalQuadraticFactor2
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
        unequalFixedDifferenceFourCanonicalQuadraticPIntegrand
          m θ (P ω) ∂ℙ)
        =
      unequalFixedDifferenceFourC m ^ 2
        * (∫ ω,
          unequalFixedDifferenceFourCanonicalQuadraticFactor0
            m θ (P ω) ∂ℙ)
      - (2 * unequalFixedDifferenceFourK m
          * unequalFixedDifferenceFourC m)
        * (∫ ω,
          unequalFixedDifferenceFourCanonicalQuadraticFactor1
            m θ (P ω) ∂ℙ)
      + unequalFixedDifferenceFourEll m
        * (∫ ω,
          unequalFixedDifferenceFourCanonicalQuadraticFactor2
            m θ (P ω) ∂ℙ) := by
    calc
      _ =
          ∫ ω,
            unequalFixedDifferenceFourCanonicalQuadraticFactor0
                m θ (P ω)
                * unequalFixedDifferenceFourC m ^ 2
              - (2 * unequalFixedDifferenceFourK m
                  * unequalFixedDifferenceFourC m)
                * unequalFixedDifferenceFourCanonicalQuadraticFactor1
                  m θ (P ω)
              + unequalFixedDifferenceFourEll m
                * unequalFixedDifferenceFourCanonicalQuadraticFactor2
                  m θ (P ω) ∂ℙ := by
            rfl
      _ =
          (∫ ω,
            unequalFixedDifferenceFourCanonicalQuadraticFactor0
                m θ (P ω)
                * unequalFixedDifferenceFourC m ^ 2
              - (2 * unequalFixedDifferenceFourK m
                  * unequalFixedDifferenceFourC m)
                * unequalFixedDifferenceFourCanonicalQuadraticFactor1
                  m θ (P ω) ∂ℙ)
            +
          ∫ ω,
            unequalFixedDifferenceFourEll m
              * unequalFixedDifferenceFourCanonicalQuadraticFactor2
                m θ (P ω) ∂ℙ := by
            simpa only [Pi.add_apply, Pi.sub_apply] using
              integral_add
                ((hPint.quadratic0.mul_const
                    (unequalFixedDifferenceFourC m ^ 2)).sub
                  (hPint.quadratic1.const_mul
                    (2 * unequalFixedDifferenceFourK m
                      * unequalFixedDifferenceFourC m)))
                (hPint.quadratic2.const_mul
                  (unequalFixedDifferenceFourEll m))
      _ =
          ((∫ ω,
            unequalFixedDifferenceFourCanonicalQuadraticFactor0
                m θ (P ω)
              * unequalFixedDifferenceFourC m ^ 2 ∂ℙ)
            -
          ∫ ω,
            (2 * unequalFixedDifferenceFourK m
                * unequalFixedDifferenceFourC m)
              * unequalFixedDifferenceFourCanonicalQuadraticFactor1
                m θ (P ω) ∂ℙ)
            +
          ∫ ω,
            unequalFixedDifferenceFourEll m
              * unequalFixedDifferenceFourCanonicalQuadraticFactor2
                m θ (P ω) ∂ℙ := by
            rw [integral_sub
              (hPint.quadratic0.mul_const
                (unequalFixedDifferenceFourC m ^ 2))
              (hPint.quadratic1.const_mul
                (2 * unequalFixedDifferenceFourK m
                  * unequalFixedDifferenceFourC m))]
      _ = _ := by
        rw [integral_mul_const, integral_const_mul, integral_const_mul]
        ring
  calc
    (∫ ω,
      V ω * unequalFixedDifferenceFourCanonicalH
          m θ (P ω) (L ω) (V ω) ^ 2 ∂ℙ)
        =
      ∫ ω,
        unequalFixedDifferenceFourC m ^ 2
          * (unequalFixedDifferenceFourCanonicalQuadraticFactor0
              m θ (P ω) * V ω)
        - (8 * (m : ℝ) * unequalFixedDifferenceFourC m)
          * (unequalFixedDifferenceFourCanonicalQuadraticFactor1
              m θ (P ω) * (V ω ^ 2 / L ω))
        + (4 * (m : ℝ)) ^ 2
          * (unequalFixedDifferenceFourCanonicalQuadraticFactor2
              m θ (P ω) * (V ω ^ 3 / L ω ^ 2)) ∂ℙ := by
            apply integral_congr_ae
            filter_upwards [] with ω
            exact unequalFixedDifferenceFourCanonicalQuadraticH_expand
              m θ (P ω) (L ω) (V ω)
    _ =
      unequalFixedDifferenceFourC m ^ 2
        * (∫ ω,
          unequalFixedDifferenceFourCanonicalQuadraticFactor0
            m θ (P ω) * V ω ∂ℙ)
      - (8 * (m : ℝ) * unequalFixedDifferenceFourC m)
        * (∫ ω,
          unequalFixedDifferenceFourCanonicalQuadraticFactor1
              m θ (P ω)
            * (V ω ^ 2 / L ω) ∂ℙ)
      + (4 * (m : ℝ)) ^ 2
        * (∫ ω,
          unequalFixedDifferenceFourCanonicalQuadraticFactor2
              m θ (P ω)
            * (V ω ^ 3 / L ω ^ 2) ∂ℙ) := by
          calc
            _ =
                (∫ ω,
                  unequalFixedDifferenceFourC m ^ 2
                    * (unequalFixedDifferenceFourCanonicalQuadraticFactor0
                        m θ (P ω) * V ω)
                  - (8 * (m : ℝ) * unequalFixedDifferenceFourC m)
                    * (unequalFixedDifferenceFourCanonicalQuadraticFactor1
                        m θ (P ω) * (V ω ^ 2 / L ω)) ∂ℙ)
                +
                ∫ ω,
                  (4 * (m : ℝ)) ^ 2
                    * (unequalFixedDifferenceFourCanonicalQuadraticFactor2
                        m θ (P ω)
                      * (V ω ^ 3 / L ω ^ 2)) ∂ℙ := by
                      simpa only [Pi.add_apply, Pi.sub_apply] using
                        integral_add
                          ((hterm0.const_mul
                              (unequalFixedDifferenceFourC m ^ 2)).sub
                            (hterm1.const_mul
                              (8 * (m : ℝ)
                                * unequalFixedDifferenceFourC m)))
                          (hterm2.const_mul ((4 * (m : ℝ)) ^ 2))
            _ =
                ((∫ ω,
                  unequalFixedDifferenceFourC m ^ 2
                    * (unequalFixedDifferenceFourCanonicalQuadraticFactor0
                        m θ (P ω) * V ω) ∂ℙ)
                -
                ∫ ω,
                  (8 * (m : ℝ) * unequalFixedDifferenceFourC m)
                    * (unequalFixedDifferenceFourCanonicalQuadraticFactor1
                        m θ (P ω) * (V ω ^ 2 / L ω)) ∂ℙ)
                +
                ∫ ω,
                  (4 * (m : ℝ)) ^ 2
                    * (unequalFixedDifferenceFourCanonicalQuadraticFactor2
                        m θ (P ω)
                      * (V ω ^ 3 / L ω ^ 2)) ∂ℙ := by
                      rw [integral_sub
                        (hterm0.const_mul
                          (unequalFixedDifferenceFourC m ^ 2))
                        (hterm1.const_mul
                          (8 * (m : ℝ)
                            * unequalFixedDifferenceFourC m))]
            _ = _ := by
              rw [integral_const_mul, integral_const_mul,
                integral_const_mul]
    _ =
      unequalFixedDifferenceFourC m ^ 2
        * (∫ ω,
          unequalFixedDifferenceFourCanonicalQuadraticFactor0
            m θ (P ω) ∂ℙ)
      - (8 * (m : ℝ) * unequalFixedDifferenceFourC m)
        * ((3 / (2 * (2 * (m : ℝ) - 1)))
          * ∫ ω,
            unequalFixedDifferenceFourCanonicalQuadraticFactor1
              m θ (P ω) ∂ℙ)
      + (4 * (m : ℝ)) ^ 2
        * ((15 /
          (4 * (2 * (m : ℝ) - 1)
            * (2 * (m : ℝ) - 2)))
          * ∫ ω,
            unequalFixedDifferenceFourCanonicalQuadraticFactor2
              m θ (P ω) ∂ℙ) := by
          rw [hfactor0, hfactor1, hfactor2]
    _ =
      unequalFixedDifferenceFourC m ^ 2
        * (∫ ω,
          unequalFixedDifferenceFourCanonicalQuadraticFactor0
            m θ (P ω) ∂ℙ)
      - (2 * unequalFixedDifferenceFourK m
          * unequalFixedDifferenceFourC m)
        * (∫ ω,
          unequalFixedDifferenceFourCanonicalQuadraticFactor1
            m θ (P ω) ∂ℙ)
      + unequalFixedDifferenceFourEll m
        * (∫ ω,
          unequalFixedDifferenceFourCanonicalQuadraticFactor2
            m θ (P ω) ∂ℙ) := by
          rw [← unequalFixedDifferenceFourTwoKCMoment hm,
            ← unequalFixedDifferenceFourEll_eq_gammaMoment hm]
          ring
    _ =
      ∫ ω,
        unequalFixedDifferenceFourCanonicalQuadraticPIntegrand
          m θ (P ω) ∂ℙ := hreduced.symm

/-! ## Integrability of the full canonical moments -/

theorem unequalFixedDifferenceFourCanonicalLinearH_integrable_of_product
    (m : ℕ) (θ : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV :
      ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom :
      GeneralCanonicalFiveMoments (2 * (m : ℝ)) L V ℙ)
    (hPint :
      UnequalFixedDifferenceFourCanonicalPFactorIntegrability
        m θ P ℙ) :
    Integrable
      (fun ω =>
        V ω * (unequalFixedDifferenceFourCanonicalR m θ (P ω) - θ)
          * unequalFixedDifferenceFourCanonicalH
              m θ (P ω) (L ω) (V ω)) ℙ := by
  obtain ⟨hV2L_int, _⟩ :=
    general_integral_v_sq_div_l
      (2 * (m : ℝ)) L V ℙ hVL hmom
  have hP0V :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourCanonicalLinearFactor0
            m θ (P ω))
        V ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourCanonicalLinearFactor0
          m θ)
        (by fun_prop : Measurable fun z : ℝ × ℝ => z.2)
  have hP1V2L :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourCanonicalLinearFactor1
            m θ (P ω))
        (fun ω => V ω ^ 2 / L ω) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourCanonicalLinearFactor1
          m θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 2 / z.1)
  have hterm0 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourCanonicalLinearFactor0
              m θ (P ω)
            * V ω) ℙ :=
    hP0V.integrable_mul hPint.linear0 hmom.v_integrable
  have hterm1 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourCanonicalLinearFactor1
              m θ (P ω)
            * (V ω ^ 2 / L ω)) ℙ :=
    hP1V2L.integrable_mul hPint.linear1 hV2L_int
  apply
    ((hterm0.const_mul (unequalFixedDifferenceFourC m)).sub
      (hterm1.const_mul (4 * (m : ℝ)))).congr
  filter_upwards [] with ω
  simpa only [Pi.sub_apply] using
    (unequalFixedDifferenceFourCanonicalLinearH_expand
      m θ (P ω) (L ω) (V ω)).symm

theorem unequalFixedDifferenceFourCanonicalQuadraticH_integrable_of_product
    (m : ℕ) (θ : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV :
      ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom :
      GeneralCanonicalFiveMoments (2 * (m : ℝ)) L V ℙ)
    (hPint :
      UnequalFixedDifferenceFourCanonicalPFactorIntegrability
        m θ P ℙ) :
    Integrable
      (fun ω =>
        V ω * unequalFixedDifferenceFourCanonicalH
            m θ (P ω) (L ω) (V ω) ^ 2) ℙ := by
  obtain ⟨hV2L_int, _⟩ :=
    general_integral_v_sq_div_l
      (2 * (m : ℝ)) L V ℙ hVL hmom
  obtain ⟨hV3L2_int, _⟩ :=
    general_integral_v_cube_div_l_sq
      (2 * (m : ℝ)) L V ℙ hVL hmom
  have hP0V :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourCanonicalQuadraticFactor0
            m θ (P ω))
        V ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourCanonicalQuadraticFactor0
          m θ)
        (by fun_prop : Measurable fun z : ℝ × ℝ => z.2)
  have hP1V2L :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourCanonicalQuadraticFactor1
            m θ (P ω))
        (fun ω => V ω ^ 2 / L ω) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourCanonicalQuadraticFactor1
          m θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 2 / z.1)
  have hP2V3L2 :
      ProbabilityTheory.IndepFun
        (fun ω =>
          unequalFixedDifferenceFourCanonicalQuadraticFactor2
            m θ (P ω))
        (fun ω => V ω ^ 3 / L ω ^ 2) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp
        (measurable_unequalFixedDifferenceFourCanonicalQuadraticFactor2
          m θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 3 / z.1 ^ 2)
  have hterm0 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourCanonicalQuadraticFactor0
              m θ (P ω)
            * V ω) ℙ :=
    hP0V.integrable_mul hPint.quadratic0 hmom.v_integrable
  have hterm1 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourCanonicalQuadraticFactor1
              m θ (P ω)
            * (V ω ^ 2 / L ω)) ℙ :=
    hP1V2L.integrable_mul hPint.quadratic1 hV2L_int
  have hterm2 :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourCanonicalQuadraticFactor2
              m θ (P ω)
            * (V ω ^ 3 / L ω ^ 2)) ℙ :=
    hP2V3L2.integrable_mul hPint.quadratic2 hV3L2_int
  apply
    (((hterm0.const_mul (unequalFixedDifferenceFourC m ^ 2)).sub
      (hterm1.const_mul
        (8 * (m : ℝ) * unequalFixedDifferenceFourC m))).add
      (hterm2.const_mul ((4 * (m : ℝ)) ^ 2))).congr
  filter_upwards [] with ω
  simpa only [Pi.add_apply, Pi.sub_apply] using
    (unequalFixedDifferenceFourCanonicalQuadraticH_expand
      m θ (P ω) (L ω) (V ω)).symm

/-! ## The two-moment risk bridge -/

theorem unequalFixedDifferenceFourCanonicalMomentBridge_of_product_reductions
    {m : ℕ} (hm : 7 ≤ m)
    (θ B C : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV :
      ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom :
      GeneralCanonicalFiveMoments (2 * (m : ℝ)) L V ℙ)
    (hPint :
      UnequalFixedDifferenceFourCanonicalPFactorIntegrability
        m θ P ℙ)
    (hlinear :
      (∫ ω,
        unequalFixedDifferenceFourCanonicalLinearPIntegrand
          m θ (P ω) ∂ℙ) = B)
    (hquadratic :
      (∫ ω,
        unequalFixedDifferenceFourCanonicalQuadraticPIntegrand
          m θ (P ω) ∂ℙ) = C) :
    UnequalDampedMomentBridge θ B C
      (fun ω => unequalFixedDifferenceFourCanonicalR m θ (P ω))
      (fun ω =>
        unequalFixedDifferenceFourCanonicalH
          m θ (P ω) (L ω) (V ω))
      V ℙ := by
  refine
    { linear_integrable :=
        unequalFixedDifferenceFourCanonicalLinearH_integrable_of_product
          m θ P L V ℙ hP_LV hVL hmom hPint
      quadratic_integrable :=
        unequalFixedDifferenceFourCanonicalQuadraticH_integrable_of_product
          m θ P L V ℙ hP_LV hVL hmom hPint
      linear_moment := ?_
      quadratic_moment := ?_ }
  · rw [unequalFixedDifferenceFourCanonicalLinearH_product_reduction
      hm θ P L V ℙ hP_LV hVL hmom hPint, hlinear]
  · rw [unequalFixedDifferenceFourCanonicalQuadraticH_product_reduction
      hm θ P L V ℙ hP_LV hVL hmom hPint, hquadratic]

/--
Specialize the generic bridge to the direct canonical coefficients
`B_m(θ)` and `C_m(θ)`.
-/
theorem unequalFixedDifferenceFourCanonicalMomentBridge_of_canonical_expectations
    {m : ℕ} (hm : 7 ≤ m)
    (θ : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV :
      ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom :
      GeneralCanonicalFiveMoments (2 * (m : ℝ)) L V ℙ)
    (hPint :
      UnequalFixedDifferenceFourCanonicalPFactorIntegrability
        m θ P ℙ)
    (hB :
      (∫ ω,
        unequalFixedDifferenceFourCanonicalBIntegrand
          m θ (P ω) ∂ℙ)
        = unequalFixedDifferenceFourCanonicalB m θ)
    (hC :
      (∫ ω,
        unequalFixedDifferenceFourCanonicalCIntegrand
          m θ (P ω) ∂ℙ)
        = unequalFixedDifferenceFourCanonicalC m θ) :
    UnequalDampedMomentBridge θ
      (unequalFixedDifferenceFourCanonicalB m θ)
      (unequalFixedDifferenceFourCanonicalC m θ)
      (fun ω => unequalFixedDifferenceFourCanonicalR m θ (P ω))
      (fun ω =>
        unequalFixedDifferenceFourCanonicalH
          m θ (P ω) (L ω) (V ω))
      V ℙ := by
  apply
    unequalFixedDifferenceFourCanonicalMomentBridge_of_product_reductions
      hm θ
      (unequalFixedDifferenceFourCanonicalB m θ)
      (unequalFixedDifferenceFourCanonicalC m θ)
      P L V ℙ hP_LV hVL hmom hPint
  · calc
      (∫ ω,
        unequalFixedDifferenceFourCanonicalLinearPIntegrand
          m θ (P ω) ∂ℙ)
          =
        ∫ ω,
          unequalFixedDifferenceFourCanonicalBIntegrand
            m θ (P ω) ∂ℙ := by
              apply integral_congr_ae
              filter_upwards [] with ω
              exact
                unequalFixedDifferenceFourCanonicalLinearPIntegrand_eq_BIntegrand
                  m θ (P ω)
      _ = unequalFixedDifferenceFourCanonicalB m θ := hB
  · calc
      (∫ ω,
        unequalFixedDifferenceFourCanonicalQuadraticPIntegrand
          m θ (P ω) ∂ℙ)
          =
        ∫ ω,
          unequalFixedDifferenceFourCanonicalCIntegrand
            m θ (P ω) ∂ℙ := by
              apply integral_congr_ae
              filter_upwards [] with ω
              exact
                unequalFixedDifferenceFourCanonicalQuadraticPIntegrand_eq_CIntegrand
                  m θ (P ω)
      _ = unequalFixedDifferenceFourCanonicalC m θ := hC

end

end GraybillDeal
