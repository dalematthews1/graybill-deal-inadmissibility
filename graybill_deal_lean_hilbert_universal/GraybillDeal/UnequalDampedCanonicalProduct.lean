import GraybillDeal.UnequalDampedCanonical
import GraybillDeal.UnequalDampedReduced
import GraybillDeal.UnequalDampedRisk
import GraybillDeal.GeneralCanonicalProduct
import Mathlib.Probability.Independence.Integration

/-!
# Product-moment reduction for the fixed unequal damped certificate

This file integrates the `L,V` coordinates out of the direct canonical
`(13,17)` construction.  Its probabilistic hypotheses are explicit:

* `P` is independent of the joint coordinate `(L,V)`;
* `V` is independent of `L`;
* `L,V` satisfy `GeneralCanonicalFiveMoments 14`;
* the five coefficient functions of `P` are integrable.

The resulting two moments are exactly the one-dimensional reduced
`P`-expectations used by the analytic certificate.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Coefficient of `V` in the unequal linear mixed-moment expansion. -/
def unequalDampedCanonicalLinearFactor0
    (θ p : ℝ) : ℝ :=
  (unequalDampedCanonicalR13_17 θ p - θ)
    * unequalDampedPhi13_17 (unequalDampedCanonicalR13_17 θ p)

/-- Coefficient of `V²/L` in the unequal linear mixed-moment expansion. -/
def unequalDampedCanonicalLinearFactor1
    (θ p : ℝ) : ℝ :=
  unequalDampedCanonicalLinearFactor0 θ p
    / unequalDampedCanonicalDenom13_17 θ p

/-- Coefficient of `V` in the unequal quadratic mixed-moment expansion. -/
def unequalDampedCanonicalQuadraticFactor0
    (θ p : ℝ) : ℝ :=
  unequalDampedPhi13_17 (unequalDampedCanonicalR13_17 θ p) ^ 2

/-- Coefficient of `V²/L` in the unequal quadratic mixed-moment expansion. -/
def unequalDampedCanonicalQuadraticFactor1
    (θ p : ℝ) : ℝ :=
  unequalDampedCanonicalQuadraticFactor0 θ p
    / unequalDampedCanonicalDenom13_17 θ p

/-- Coefficient of `V³/L²` in the unequal quadratic mixed-moment expansion. -/
def unequalDampedCanonicalQuadraticFactor2
    (θ p : ℝ) : ℝ :=
  unequalDampedCanonicalQuadraticFactor0 θ p
    / unequalDampedCanonicalDenom13_17 θ p ^ 2

/--
The reduced linear `P`-integrand after the `L,V` moments have been taken.
-/
def unequalDampedCanonicalLinearPIntegrand13_17
    (θ p : ℝ) : ℝ :=
  unequalDampedCanonicalLinearFactor0 θ p
    * unequalDampedC13_17
  - unequalDampedK13_17
    * unequalDampedCanonicalLinearFactor1 θ p

/--
The reduced quadratic `P`-integrand after the `L,V` moments have been taken.
-/
def unequalDampedCanonicalQuadraticPIntegrand13_17
    (θ p : ℝ) : ℝ :=
  unequalDampedCanonicalQuadraticFactor0 θ p
    * unequalDampedC13_17 ^ 2
  - (84 * unequalDampedC13_17 / 13)
    * unequalDampedCanonicalQuadraticFactor1 θ p
  + (245 / 13)
    * unequalDampedCanonicalQuadraticFactor2 θ p

theorem measurable_unequalDampedCanonicalLinearFactor0 (θ : ℝ) :
    Measurable (unequalDampedCanonicalLinearFactor0 θ) := by
  unfold unequalDampedCanonicalLinearFactor0
    unequalDampedCanonicalR13_17 unequalDampedCanonicalDenom13_17
    unequalDampedPhi13_17
  fun_prop

theorem measurable_unequalDampedCanonicalLinearFactor1 (θ : ℝ) :
    Measurable (unequalDampedCanonicalLinearFactor1 θ) := by
  unfold unequalDampedCanonicalLinearFactor1
  exact (measurable_unequalDampedCanonicalLinearFactor0 θ).div (by
    unfold unequalDampedCanonicalDenom13_17
    fun_prop)

theorem measurable_unequalDampedCanonicalQuadraticFactor0 (θ : ℝ) :
    Measurable (unequalDampedCanonicalQuadraticFactor0 θ) := by
  unfold unequalDampedCanonicalQuadraticFactor0
    unequalDampedCanonicalR13_17 unequalDampedCanonicalDenom13_17
    unequalDampedPhi13_17
  fun_prop

theorem measurable_unequalDampedCanonicalQuadraticFactor1 (θ : ℝ) :
    Measurable (unequalDampedCanonicalQuadraticFactor1 θ) := by
  unfold unequalDampedCanonicalQuadraticFactor1
  exact (measurable_unequalDampedCanonicalQuadraticFactor0 θ).div (by
    unfold unequalDampedCanonicalDenom13_17
    fun_prop)

theorem measurable_unequalDampedCanonicalQuadraticFactor2 (θ : ℝ) :
    Measurable (unequalDampedCanonicalQuadraticFactor2 θ) := by
  unfold unequalDampedCanonicalQuadraticFactor2
  exact (measurable_unequalDampedCanonicalQuadraticFactor0 θ).div (by
    unfold unequalDampedCanonicalDenom13_17
    fun_prop)

/-- Integrability of the five unequal `P`-coefficient functions. -/
structure UnequalDampedCanonicalPFactorIntegrability13_17
    (θ : ℝ) (P : Ω → ℝ) (ℙ : Measure Ω) : Prop where
  linear0 :
    Integrable
      (fun ω => unequalDampedCanonicalLinearFactor0 θ (P ω)) ℙ
  linear1 :
    Integrable
      (fun ω => unequalDampedCanonicalLinearFactor1 θ (P ω)) ℙ
  quadratic0 :
    Integrable
      (fun ω => unequalDampedCanonicalQuadraticFactor0 θ (P ω)) ℙ
  quadratic1 :
    Integrable
      (fun ω => unequalDampedCanonicalQuadraticFactor1 θ (P ω)) ℙ
  quadratic2 :
    Integrable
      (fun ω => unequalDampedCanonicalQuadraticFactor2 θ (P ω)) ℙ

/--
Pointwise expansion of `V (R-θ) H` into the two products that independence
factors.
-/
theorem unequalDampedCanonicalLinearH13_17_expand
    (θ p l v : ℝ) :
    v * (unequalDampedCanonicalR13_17 θ p - θ)
        * unequalDampedCanonicalH13_17 θ p l v
      =
    unequalDampedC13_17
      * (unequalDampedCanonicalLinearFactor0 θ p * v)
    - 28
      * (unequalDampedCanonicalLinearFactor1 θ p
        * (v ^ 2 / l)) := by
  unfold unequalDampedCanonicalH13_17
    unequalDampedCanonicalQ13_17
    unequalDampedCanonicalLinearFactor1
    unequalDampedCanonicalLinearFactor0
  simp only [div_eq_mul_inv, mul_inv]
  ring

/--
Pointwise expansion of `V H²` into the three products that independence
factors.
-/
theorem unequalDampedCanonicalQuadraticH13_17_expand
    (θ p l v : ℝ) :
    v * unequalDampedCanonicalH13_17 θ p l v ^ 2
      =
    unequalDampedC13_17 ^ 2
      * (unequalDampedCanonicalQuadraticFactor0 θ p * v)
    - (56 * unequalDampedC13_17)
      * (unequalDampedCanonicalQuadraticFactor1 θ p
        * (v ^ 2 / l))
    + 784
      * (unequalDampedCanonicalQuadraticFactor2 θ p
        * (v ^ 3 / l ^ 2)) := by
  unfold unequalDampedCanonicalH13_17
    unequalDampedCanonicalQ13_17
    unequalDampedCanonicalQuadraticFactor2
    unequalDampedCanonicalQuadraticFactor1
    unequalDampedCanonicalQuadraticFactor0
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-! ## Identification of the reduced `P`-integrands -/

/--
The factor form obtained from the `L,V` moments is the direct canonical
linear integrand used by the one-sided analytic certificate.
-/
theorem unequalDampedCanonicalLinearPIntegrand13_17_eq_BIntegrand
    (θ p : ℝ) :
    unequalDampedCanonicalLinearPIntegrand13_17 θ p
      =
    unequalDampedCanonicalBIntegrand13_17 θ p := by
  unfold unequalDampedCanonicalLinearPIntegrand13_17
    unequalDampedCanonicalLinearFactor1
    unequalDampedCanonicalLinearFactor0
    unequalDampedCanonicalBIntegrand13_17
  ring

/--
The factor form obtained from the `L,V` moments is the direct canonical
quadratic integrand used by the one-sided analytic certificate.
-/
theorem unequalDampedCanonicalQuadraticPIntegrand13_17_eq_CIntegrand
    (θ p : ℝ) :
    unequalDampedCanonicalQuadraticPIntegrand13_17 θ p
      =
    unequalDampedCanonicalCIntegrand13_17 θ p := by
  unfold unequalDampedCanonicalQuadraticPIntegrand13_17
    unequalDampedCanonicalQuadraticFactor2
    unequalDampedCanonicalQuadraticFactor1
    unequalDampedCanonicalQuadraticFactor0
    unequalDampedCanonicalCIntegrand13_17
    unequalDampedCKernel13_17
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-! ## Product-moment reductions -/

/--
Integrating out `L,V` reduces the canonical linear moment to the direct
one-dimensional `P`-integrand.
-/
theorem unequalDampedCanonicalLinearH13_17_product_reduction
    (θ : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : GeneralCanonicalFiveMoments 14 L V ℙ)
    (hPint : UnequalDampedCanonicalPFactorIntegrability13_17 θ P ℙ) :
    (∫ ω,
      V ω * (unequalDampedCanonicalR13_17 θ (P ω) - θ)
        * unequalDampedCanonicalH13_17
            θ (P ω) (L ω) (V ω) ∂ℙ)
      =
    ∫ ω, unequalDampedCanonicalLinearPIntegrand13_17 θ (P ω) ∂ℙ := by
  obtain ⟨hV2L_int, hV2L_mean⟩ :=
    general_integral_v_sq_div_l 14 L V ℙ hVL hmom
  have hP0V :
      ProbabilityTheory.IndepFun
        (fun ω => unequalDampedCanonicalLinearFactor0 θ (P ω)) V ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_unequalDampedCanonicalLinearFactor0 θ)
        (by fun_prop : Measurable fun z : ℝ × ℝ => z.2)
  have hP1V2L :
      ProbabilityTheory.IndepFun
        (fun ω => unequalDampedCanonicalLinearFactor1 θ (P ω))
        (fun ω => V ω ^ 2 / L ω) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_unequalDampedCanonicalLinearFactor1 θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 2 / z.1)
  have hterm0 :
      Integrable
        (fun ω =>
          unequalDampedCanonicalLinearFactor0 θ (P ω) * V ω) ℙ :=
    hP0V.integrable_mul hPint.linear0 hmom.v_integrable
  have hterm1 :
      Integrable
        (fun ω =>
          unequalDampedCanonicalLinearFactor1 θ (P ω)
            * (V ω ^ 2 / L ω)) ℙ :=
    hP1V2L.integrable_mul hPint.linear1 hV2L_int
  have hfactor0 :
      (∫ ω,
        unequalDampedCanonicalLinearFactor0 θ (P ω) * V ω ∂ℙ)
        =
      ∫ ω, unequalDampedCanonicalLinearFactor0 θ (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω, unequalDampedCanonicalLinearFactor0 θ (P ω) ∂ℙ)
            * ∫ ω, V ω ∂ℙ :=
        hP0V.integral_fun_mul_eq_mul_integral
          hPint.linear0.aestronglyMeasurable
          hmom.v_integrable.aestronglyMeasurable
      _ = _ := by rw [hmom.v_mean, mul_one]
  have hfactor1 :
      (∫ ω,
        unequalDampedCanonicalLinearFactor1 θ (P ω)
          * (V ω ^ 2 / L ω) ∂ℙ)
        =
      (3 / 26) *
        ∫ ω, unequalDampedCanonicalLinearFactor1 θ (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω, unequalDampedCanonicalLinearFactor1 θ (P ω) ∂ℙ)
            * ∫ ω, V ω ^ 2 / L ω ∂ℙ :=
        hP1V2L.integral_fun_mul_eq_mul_integral
          hPint.linear1.aestronglyMeasurable
          hV2L_int.aestronglyMeasurable
      _ =
          (3 / 26) *
            ∫ ω, unequalDampedCanonicalLinearFactor1 θ (P ω) ∂ℙ := by
        rw [hV2L_mean]
        ring
  have hreduced :
      (∫ ω, unequalDampedCanonicalLinearPIntegrand13_17 θ (P ω) ∂ℙ)
        =
      unequalDampedC13_17
          * (∫ ω, unequalDampedCanonicalLinearFactor0 θ (P ω) ∂ℙ)
        - unequalDampedK13_17
          * (∫ ω,
              unequalDampedCanonicalLinearFactor1 θ (P ω) ∂ℙ) := by
    calc
      _ =
          ∫ ω,
            unequalDampedCanonicalLinearFactor0 θ (P ω)
                * unequalDampedC13_17
              - unequalDampedK13_17
                * unequalDampedCanonicalLinearFactor1 θ (P ω) ∂ℙ := by
            rfl
      _ =
          (∫ ω,
            unequalDampedCanonicalLinearFactor0 θ (P ω)
              * unequalDampedC13_17 ∂ℙ)
            -
          ∫ ω,
            unequalDampedK13_17
              * unequalDampedCanonicalLinearFactor1 θ (P ω) ∂ℙ := by
            rw [integral_sub
              (hPint.linear0.mul_const unequalDampedC13_17)
              (hPint.linear1.const_mul unequalDampedK13_17)]
      _ = _ := by
        rw [integral_mul_const, integral_const_mul]
        ring
  calc
    (∫ ω,
      V ω * (unequalDampedCanonicalR13_17 θ (P ω) - θ)
        * unequalDampedCanonicalH13_17
            θ (P ω) (L ω) (V ω) ∂ℙ)
        =
      ∫ ω,
        unequalDampedC13_17
            * (unequalDampedCanonicalLinearFactor0 θ (P ω) * V ω)
          - 28
            * (unequalDampedCanonicalLinearFactor1 θ (P ω)
              * (V ω ^ 2 / L ω)) ∂ℙ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact unequalDampedCanonicalLinearH13_17_expand
          θ (P ω) (L ω) (V ω)
    _ =
      unequalDampedC13_17
          * (∫ ω,
            unequalDampedCanonicalLinearFactor0 θ (P ω) * V ω ∂ℙ)
        - 28
          * (∫ ω,
            unequalDampedCanonicalLinearFactor1 θ (P ω)
              * (V ω ^ 2 / L ω) ∂ℙ) := by
        rw [integral_sub
          (hterm0.const_mul unequalDampedC13_17)
          (hterm1.const_mul 28),
          integral_const_mul, integral_const_mul]
    _ =
      unequalDampedC13_17
          * (∫ ω, unequalDampedCanonicalLinearFactor0 θ (P ω) ∂ℙ)
        - 28 * ((3 / 26)
          * ∫ ω, unequalDampedCanonicalLinearFactor1 θ (P ω) ∂ℙ) := by
        rw [hfactor0, hfactor1]
    _ =
      ∫ ω, unequalDampedCanonicalLinearPIntegrand13_17 θ (P ω) ∂ℙ := by
        rw [hreduced]
        unfold unequalDampedK13_17
        ring

/--
Integrating out `L,V` reduces the canonical quadratic moment to the direct
one-dimensional `P`-integrand.
-/
theorem unequalDampedCanonicalQuadraticH13_17_product_reduction
    (θ : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : GeneralCanonicalFiveMoments 14 L V ℙ)
    (hPint : UnequalDampedCanonicalPFactorIntegrability13_17 θ P ℙ) :
    (∫ ω,
      V ω * unequalDampedCanonicalH13_17
          θ (P ω) (L ω) (V ω) ^ 2 ∂ℙ)
      =
    ∫ ω, unequalDampedCanonicalQuadraticPIntegrand13_17 θ (P ω) ∂ℙ := by
  obtain ⟨hV2L_int, hV2L_mean⟩ :=
    general_integral_v_sq_div_l 14 L V ℙ hVL hmom
  obtain ⟨hV3L2_int, hV3L2_mean⟩ :=
    general_integral_v_cube_div_l_sq 14 L V ℙ hVL hmom
  have hP0V :
      ProbabilityTheory.IndepFun
        (fun ω => unequalDampedCanonicalQuadraticFactor0 θ (P ω)) V ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_unequalDampedCanonicalQuadraticFactor0 θ)
        (by fun_prop : Measurable fun z : ℝ × ℝ => z.2)
  have hP1V2L :
      ProbabilityTheory.IndepFun
        (fun ω => unequalDampedCanonicalQuadraticFactor1 θ (P ω))
        (fun ω => V ω ^ 2 / L ω) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_unequalDampedCanonicalQuadraticFactor1 θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 2 / z.1)
  have hP2V3L2 :
      ProbabilityTheory.IndepFun
        (fun ω => unequalDampedCanonicalQuadraticFactor2 θ (P ω))
        (fun ω => V ω ^ 3 / L ω ^ 2) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_unequalDampedCanonicalQuadraticFactor2 θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 3 / z.1 ^ 2)
  have hterm0 :
      Integrable
        (fun ω =>
          unequalDampedCanonicalQuadraticFactor0 θ (P ω) * V ω) ℙ :=
    hP0V.integrable_mul hPint.quadratic0 hmom.v_integrable
  have hterm1 :
      Integrable
        (fun ω =>
          unequalDampedCanonicalQuadraticFactor1 θ (P ω)
            * (V ω ^ 2 / L ω)) ℙ :=
    hP1V2L.integrable_mul hPint.quadratic1 hV2L_int
  have hterm2 :
      Integrable
        (fun ω =>
          unequalDampedCanonicalQuadraticFactor2 θ (P ω)
            * (V ω ^ 3 / L ω ^ 2)) ℙ :=
    hP2V3L2.integrable_mul hPint.quadratic2 hV3L2_int
  have hfactor0 :
      (∫ ω,
        unequalDampedCanonicalQuadraticFactor0 θ (P ω) * V ω ∂ℙ)
        =
      ∫ ω, unequalDampedCanonicalQuadraticFactor0 θ (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω, unequalDampedCanonicalQuadraticFactor0 θ (P ω) ∂ℙ)
            * ∫ ω, V ω ∂ℙ :=
        hP0V.integral_fun_mul_eq_mul_integral
          hPint.quadratic0.aestronglyMeasurable
          hmom.v_integrable.aestronglyMeasurable
      _ = _ := by rw [hmom.v_mean, mul_one]
  have hfactor1 :
      (∫ ω,
        unequalDampedCanonicalQuadraticFactor1 θ (P ω)
          * (V ω ^ 2 / L ω) ∂ℙ)
        =
      (3 / 26) *
        ∫ ω, unequalDampedCanonicalQuadraticFactor1 θ (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω, unequalDampedCanonicalQuadraticFactor1 θ (P ω) ∂ℙ)
            * ∫ ω, V ω ^ 2 / L ω ∂ℙ :=
        hP1V2L.integral_fun_mul_eq_mul_integral
          hPint.quadratic1.aestronglyMeasurable
          hV2L_int.aestronglyMeasurable
      _ = _ := by
        rw [hV2L_mean]
        ring
  have hfactor2 :
      (∫ ω,
        unequalDampedCanonicalQuadraticFactor2 θ (P ω)
          * (V ω ^ 3 / L ω ^ 2) ∂ℙ)
        =
      (5 / 208) *
        ∫ ω, unequalDampedCanonicalQuadraticFactor2 θ (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω, unequalDampedCanonicalQuadraticFactor2 θ (P ω) ∂ℙ)
            * ∫ ω, V ω ^ 3 / L ω ^ 2 ∂ℙ :=
        hP2V3L2.integral_fun_mul_eq_mul_integral
          hPint.quadratic2.aestronglyMeasurable
          hV3L2_int.aestronglyMeasurable
      _ = _ := by
        rw [hV3L2_mean]
        ring
  have hreduced :
      (∫ ω, unequalDampedCanonicalQuadraticPIntegrand13_17 θ (P ω) ∂ℙ)
        =
      unequalDampedC13_17 ^ 2
          * (∫ ω,
            unequalDampedCanonicalQuadraticFactor0 θ (P ω) ∂ℙ)
        - (84 * unequalDampedC13_17 / 13)
          * (∫ ω,
            unequalDampedCanonicalQuadraticFactor1 θ (P ω) ∂ℙ)
        + (245 / 13)
          * (∫ ω,
            unequalDampedCanonicalQuadraticFactor2 θ (P ω) ∂ℙ) := by
    calc
      _ =
          ∫ ω,
            unequalDampedCanonicalQuadraticFactor0 θ (P ω)
                * unequalDampedC13_17 ^ 2
              - (84 * unequalDampedC13_17 / 13)
                * unequalDampedCanonicalQuadraticFactor1 θ (P ω)
              + (245 / 13)
                * unequalDampedCanonicalQuadraticFactor2 θ (P ω) ∂ℙ := by
            rfl
      _ =
          (∫ ω,
            unequalDampedCanonicalQuadraticFactor0 θ (P ω)
                * unequalDampedC13_17 ^ 2
              - (84 * unequalDampedC13_17 / 13)
                * unequalDampedCanonicalQuadraticFactor1 θ (P ω) ∂ℙ)
            +
          ∫ ω,
            (245 / 13)
              * unequalDampedCanonicalQuadraticFactor2 θ (P ω) ∂ℙ := by
            simpa only [Pi.add_apply, Pi.sub_apply] using
              integral_add
                ((hPint.quadratic0.mul_const
                    (unequalDampedC13_17 ^ 2)).sub
                  (hPint.quadratic1.const_mul
                    (84 * unequalDampedC13_17 / 13)))
                (hPint.quadratic2.const_mul (245 / 13))
      _ =
          ((∫ ω,
            unequalDampedCanonicalQuadraticFactor0 θ (P ω)
              * unequalDampedC13_17 ^ 2 ∂ℙ)
            -
          ∫ ω,
            (84 * unequalDampedC13_17 / 13)
              * unequalDampedCanonicalQuadraticFactor1 θ (P ω) ∂ℙ)
            +
          ∫ ω,
            (245 / 13)
              * unequalDampedCanonicalQuadraticFactor2 θ (P ω) ∂ℙ := by
            rw [integral_sub
              (hPint.quadratic0.mul_const
                (unequalDampedC13_17 ^ 2))
              (hPint.quadratic1.const_mul
                (84 * unequalDampedC13_17 / 13))]
      _ = _ := by
        rw [integral_mul_const, integral_const_mul, integral_const_mul]
        ring
  calc
    (∫ ω,
      V ω * unequalDampedCanonicalH13_17
          θ (P ω) (L ω) (V ω) ^ 2 ∂ℙ)
        =
      ∫ ω,
        unequalDampedC13_17 ^ 2
            * (unequalDampedCanonicalQuadraticFactor0 θ (P ω) * V ω)
          - (56 * unequalDampedC13_17)
            * (unequalDampedCanonicalQuadraticFactor1 θ (P ω)
              * (V ω ^ 2 / L ω))
          + 784
            * (unequalDampedCanonicalQuadraticFactor2 θ (P ω)
              * (V ω ^ 3 / L ω ^ 2)) ∂ℙ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact unequalDampedCanonicalQuadraticH13_17_expand
          θ (P ω) (L ω) (V ω)
    _ =
      unequalDampedC13_17 ^ 2
          * (∫ ω,
            unequalDampedCanonicalQuadraticFactor0 θ (P ω) * V ω ∂ℙ)
        - (56 * unequalDampedC13_17)
          * (∫ ω,
            unequalDampedCanonicalQuadraticFactor1 θ (P ω)
              * (V ω ^ 2 / L ω) ∂ℙ)
        + 784
          * (∫ ω,
            unequalDampedCanonicalQuadraticFactor2 θ (P ω)
              * (V ω ^ 3 / L ω ^ 2) ∂ℙ) := by
        calc
          _ =
              (∫ ω,
                unequalDampedC13_17 ^ 2
                    * (unequalDampedCanonicalQuadraticFactor0 θ (P ω)
                      * V ω)
                  - (56 * unequalDampedC13_17)
                    * (unequalDampedCanonicalQuadraticFactor1 θ (P ω)
                      * (V ω ^ 2 / L ω)) ∂ℙ)
                +
              ∫ ω,
                784
                  * (unequalDampedCanonicalQuadraticFactor2 θ (P ω)
                    * (V ω ^ 3 / L ω ^ 2)) ∂ℙ := by
                  simpa only [Pi.add_apply, Pi.sub_apply] using
                    integral_add
                      ((hterm0.const_mul (unequalDampedC13_17 ^ 2)).sub
                        (hterm1.const_mul
                          (56 * unequalDampedC13_17)))
                      (hterm2.const_mul 784)
          _ =
              ((∫ ω,
                unequalDampedC13_17 ^ 2
                    * (unequalDampedCanonicalQuadraticFactor0 θ (P ω)
                      * V ω) ∂ℙ)
                -
              ∫ ω,
                (56 * unequalDampedC13_17)
                  * (unequalDampedCanonicalQuadraticFactor1 θ (P ω)
                    * (V ω ^ 2 / L ω)) ∂ℙ)
                +
              ∫ ω,
                784
                  * (unequalDampedCanonicalQuadraticFactor2 θ (P ω)
                    * (V ω ^ 3 / L ω ^ 2)) ∂ℙ := by
                  rw [integral_sub
                    (hterm0.const_mul (unequalDampedC13_17 ^ 2))
                    (hterm1.const_mul (56 * unequalDampedC13_17))]
          _ = _ := by
            rw [integral_const_mul, integral_const_mul, integral_const_mul]
    _ =
      unequalDampedC13_17 ^ 2
          * (∫ ω, unequalDampedCanonicalQuadraticFactor0 θ (P ω) ∂ℙ)
        - (56 * unequalDampedC13_17) * ((3 / 26)
          * ∫ ω, unequalDampedCanonicalQuadraticFactor1 θ (P ω) ∂ℙ)
        + 784 * ((5 / 208)
          * ∫ ω, unequalDampedCanonicalQuadraticFactor2 θ (P ω) ∂ℙ) := by
        rw [hfactor0, hfactor1, hfactor2]
    _ =
      ∫ ω, unequalDampedCanonicalQuadraticPIntegrand13_17 θ (P ω) ∂ℙ := by
        rw [hreduced]
        ring

/-! ## Integrability and the generic risk bridge -/

/-- Integrability of the full unequal linear canonical integrand. -/
theorem unequalDampedCanonicalLinearH13_17_integrable_of_product
    (θ : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : GeneralCanonicalFiveMoments 14 L V ℙ)
    (hPint : UnequalDampedCanonicalPFactorIntegrability13_17 θ P ℙ) :
    Integrable
      (fun ω =>
        V ω * (unequalDampedCanonicalR13_17 θ (P ω) - θ)
          * unequalDampedCanonicalH13_17
              θ (P ω) (L ω) (V ω)) ℙ := by
  obtain ⟨hV2L_int, _⟩ :=
    general_integral_v_sq_div_l 14 L V ℙ hVL hmom
  have hP0V :
      ProbabilityTheory.IndepFun
        (fun ω => unequalDampedCanonicalLinearFactor0 θ (P ω)) V ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_unequalDampedCanonicalLinearFactor0 θ)
        (by fun_prop : Measurable fun z : ℝ × ℝ => z.2)
  have hP1V2L :
      ProbabilityTheory.IndepFun
        (fun ω => unequalDampedCanonicalLinearFactor1 θ (P ω))
        (fun ω => V ω ^ 2 / L ω) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_unequalDampedCanonicalLinearFactor1 θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 2 / z.1)
  have hterm0 :
      Integrable
        (fun ω =>
          unequalDampedCanonicalLinearFactor0 θ (P ω) * V ω) ℙ :=
    hP0V.integrable_mul hPint.linear0 hmom.v_integrable
  have hterm1 :
      Integrable
        (fun ω =>
          unequalDampedCanonicalLinearFactor1 θ (P ω)
            * (V ω ^ 2 / L ω)) ℙ :=
    hP1V2L.integrable_mul hPint.linear1 hV2L_int
  apply
    ((hterm0.const_mul unequalDampedC13_17).sub
      (hterm1.const_mul 28)).congr
  filter_upwards [] with ω
  simpa only [Pi.sub_apply] using
    (unequalDampedCanonicalLinearH13_17_expand
      θ (P ω) (L ω) (V ω)).symm

/-- Integrability of the full unequal quadratic canonical integrand. -/
theorem unequalDampedCanonicalQuadraticH13_17_integrable_of_product
    (θ : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : GeneralCanonicalFiveMoments 14 L V ℙ)
    (hPint : UnequalDampedCanonicalPFactorIntegrability13_17 θ P ℙ) :
    Integrable
      (fun ω =>
        V ω * unequalDampedCanonicalH13_17
            θ (P ω) (L ω) (V ω) ^ 2) ℙ := by
  obtain ⟨hV2L_int, _⟩ :=
    general_integral_v_sq_div_l 14 L V ℙ hVL hmom
  obtain ⟨hV3L2_int, _⟩ :=
    general_integral_v_cube_div_l_sq 14 L V ℙ hVL hmom
  have hP0V :
      ProbabilityTheory.IndepFun
        (fun ω => unequalDampedCanonicalQuadraticFactor0 θ (P ω)) V ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_unequalDampedCanonicalQuadraticFactor0 θ)
        (by fun_prop : Measurable fun z : ℝ × ℝ => z.2)
  have hP1V2L :
      ProbabilityTheory.IndepFun
        (fun ω => unequalDampedCanonicalQuadraticFactor1 θ (P ω))
        (fun ω => V ω ^ 2 / L ω) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_unequalDampedCanonicalQuadraticFactor1 θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 2 / z.1)
  have hP2V3L2 :
      ProbabilityTheory.IndepFun
        (fun ω => unequalDampedCanonicalQuadraticFactor2 θ (P ω))
        (fun ω => V ω ^ 3 / L ω ^ 2) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_unequalDampedCanonicalQuadraticFactor2 θ)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 3 / z.1 ^ 2)
  have hterm0 :
      Integrable
        (fun ω =>
          unequalDampedCanonicalQuadraticFactor0 θ (P ω) * V ω) ℙ :=
    hP0V.integrable_mul hPint.quadratic0 hmom.v_integrable
  have hterm1 :
      Integrable
        (fun ω =>
          unequalDampedCanonicalQuadraticFactor1 θ (P ω)
            * (V ω ^ 2 / L ω)) ℙ :=
    hP1V2L.integrable_mul hPint.quadratic1 hV2L_int
  have hterm2 :
      Integrable
        (fun ω =>
          unequalDampedCanonicalQuadraticFactor2 θ (P ω)
            * (V ω ^ 3 / L ω ^ 2)) ℙ :=
    hP2V3L2.integrable_mul hPint.quadratic2 hV3L2_int
  apply
    (((hterm0.const_mul (unequalDampedC13_17 ^ 2)).sub
      (hterm1.const_mul (56 * unequalDampedC13_17))).add
      (hterm2.const_mul 784)).congr
  filter_upwards [] with ω
  simpa only [Pi.add_apply, Pi.sub_apply] using
    (unequalDampedCanonicalQuadraticH13_17_expand
      θ (P ω) (L ω) (V ω)).symm

/--
Construct the two-moment risk bridge from product independence, the five
`L,V` moments, the five `P`-factor integrability facts, and identifications
of the two remaining `P`-expectations.
-/
theorem unequalDampedCanonicalMomentBridge13_17_of_product_reductions
    (θ B C : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : GeneralCanonicalFiveMoments 14 L V ℙ)
    (hPint : UnequalDampedCanonicalPFactorIntegrability13_17 θ P ℙ)
    (hlinear :
      (∫ ω, unequalDampedCanonicalLinearPIntegrand13_17 θ (P ω) ∂ℙ)
        = B)
    (hquadratic :
      (∫ ω, unequalDampedCanonicalQuadraticPIntegrand13_17 θ (P ω) ∂ℙ)
        = C) :
    UnequalDampedMomentBridge θ B C
      (fun ω => unequalDampedCanonicalR13_17 θ (P ω))
      (fun ω =>
        unequalDampedCanonicalH13_17 θ (P ω) (L ω) (V ω))
      V ℙ := by
  refine
    { linear_integrable :=
        unequalDampedCanonicalLinearH13_17_integrable_of_product
          θ P L V ℙ hP_LV hVL hmom hPint
      quadratic_integrable :=
        unequalDampedCanonicalQuadraticH13_17_integrable_of_product
          θ P L V ℙ hP_LV hVL hmom hPint
      linear_moment := ?_
      quadratic_moment := ?_ }
  · rw [unequalDampedCanonicalLinearH13_17_product_reduction
      θ P L V ℙ hP_LV hVL hmom hPint, hlinear]
  · rw [unequalDampedCanonicalQuadraticH13_17_product_reduction
      θ P L V ℙ hP_LV hVL hmom hPint, hquadratic]

/--
Convenient specialization of the generic bridge to the canonical reduced
coefficients `B₁₃,₁₇(θ)` and `C₁₃,₁₇(θ)`.
-/
theorem unequalDampedCanonicalMomentBridge13_17_of_canonical_expectations
    (θ : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : GeneralCanonicalFiveMoments 14 L V ℙ)
    (hPint : UnequalDampedCanonicalPFactorIntegrability13_17 θ P ℙ)
    (hB :
      (∫ ω, unequalDampedCanonicalBIntegrand13_17 θ (P ω) ∂ℙ)
        = unequalDampedCanonicalB13_17 θ)
    (hC :
      (∫ ω, unequalDampedCanonicalCIntegrand13_17 θ (P ω) ∂ℙ)
        = unequalDampedCanonicalC13_17 θ) :
    UnequalDampedMomentBridge θ
      (unequalDampedCanonicalB13_17 θ)
      (unequalDampedCanonicalC13_17 θ)
      (fun ω => unequalDampedCanonicalR13_17 θ (P ω))
      (fun ω =>
        unequalDampedCanonicalH13_17 θ (P ω) (L ω) (V ω))
      V ℙ := by
  apply unequalDampedCanonicalMomentBridge13_17_of_product_reductions
    θ (unequalDampedCanonicalB13_17 θ)
      (unequalDampedCanonicalC13_17 θ)
      P L V ℙ hP_LV hVL hmom hPint
  · calc
      (∫ ω,
        unequalDampedCanonicalLinearPIntegrand13_17 θ (P ω) ∂ℙ)
          =
        ∫ ω, unequalDampedCanonicalBIntegrand13_17 θ (P ω) ∂ℙ := by
            apply integral_congr_ae
            filter_upwards [] with ω
            exact
              unequalDampedCanonicalLinearPIntegrand13_17_eq_BIntegrand
                θ (P ω)
      _ = unequalDampedCanonicalB13_17 θ := hB
  · calc
      (∫ ω,
        unequalDampedCanonicalQuadraticPIntegrand13_17 θ (P ω) ∂ℙ)
          =
        ∫ ω, unequalDampedCanonicalCIntegrand13_17 θ (P ω) ∂ℙ := by
            apply integral_congr_ae
            filter_upwards [] with ω
            exact
              unequalDampedCanonicalQuadraticPIntegrand13_17_eq_CIntegrand
                θ (P ω)
      _ = unequalDampedCanonicalC13_17 θ := hC

end

end GraybillDeal
