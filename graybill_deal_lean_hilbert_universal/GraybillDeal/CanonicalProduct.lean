import GraybillDeal.Canonical
import GraybillDeal.GammaMoments
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.HasLaw

/-!
# Product-moment reductions for the canonical `n = 13` law

This file proves the two product reductions left as hypotheses in
`canonicalMomentBridge13_of_product_reductions`.  The probabilistic input is
kept explicit:

* `P` is independent of the joint coordinate `(L,V)`;
* `V` and `L` are independent;
* the three moments of `V` and two inverse moments of `L` have their
  canonical values;
* the five coefficient functions of `P` are integrable.

The joint-coordinate independence is intentional: pairwise independence of
`P`, `L`, and `V` would not suffice to factor the mixed products below.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The coefficient of `V` in the linear mixed-moment expansion. -/
def canonicalLinearFactor0 (s pcoord : ℝ) : ℝ :=
  (canonicalR s pcoord - canonicalTheta s)
    * weightPolynomial (canonicalR s pcoord)

/-- The coefficient of `V²/L` in the linear mixed-moment expansion. -/
def canonicalLinearFactor1 (s pcoord : ℝ) : ℝ :=
  canonicalLinearFactor0 s pcoord / canonicalDenom s pcoord

/-- The coefficient of `V` in the quadratic mixed-moment expansion. -/
def canonicalQuadraticFactor0 (s pcoord : ℝ) : ℝ :=
  weightPolynomial (canonicalR s pcoord) ^ 2

/-- The coefficient of `V²/L` in the quadratic mixed-moment expansion. -/
def canonicalQuadraticFactor1 (s pcoord : ℝ) : ℝ :=
  canonicalQuadraticFactor0 s pcoord / canonicalDenom s pcoord

/-- The coefficient of `V³/L²` in the quadratic mixed-moment expansion. -/
def canonicalQuadraticFactor2 (s pcoord : ℝ) : ℝ :=
  canonicalQuadraticFactor0 s pcoord / canonicalDenom s pcoord ^ 2

theorem measurable_canonicalLinearFactor0 (s : ℝ) :
    Measurable (canonicalLinearFactor0 s) := by
  unfold canonicalLinearFactor0 canonicalR canonicalDenom canonicalTheta
    weightPolynomial
  fun_prop

theorem measurable_canonicalLinearFactor1 (s : ℝ) :
    Measurable (canonicalLinearFactor1 s) := by
  unfold canonicalLinearFactor1
  exact (measurable_canonicalLinearFactor0 s).div (by
    unfold canonicalDenom canonicalTheta
    fun_prop)

theorem measurable_canonicalQuadraticFactor0 (s : ℝ) :
    Measurable (canonicalQuadraticFactor0 s) := by
  unfold canonicalQuadraticFactor0 canonicalR canonicalDenom canonicalTheta
    weightPolynomial
  fun_prop

theorem measurable_canonicalQuadraticFactor1 (s : ℝ) :
    Measurable (canonicalQuadraticFactor1 s) := by
  unfold canonicalQuadraticFactor1
  exact (measurable_canonicalQuadraticFactor0 s).div (by
    unfold canonicalDenom canonicalTheta
    fun_prop)

theorem measurable_canonicalQuadraticFactor2 (s : ℝ) :
    Measurable (canonicalQuadraticFactor2 s) := by
  unfold canonicalQuadraticFactor2
  exact (measurable_canonicalQuadraticFactor0 s).div (by
    unfold canonicalDenom canonicalTheta
    fun_prop)

/--
The five scalar moment facts needed at `n = 13`, with the corresponding
integrability facts stated explicitly.
-/
structure CanonicalFiveMoments13
    (L V : Ω → ℝ) (ℙ : Measure Ω) : Prop where
  v_integrable : Integrable V ℙ
  v_sq_integrable : Integrable (fun ω => V ω ^ 2) ℙ
  v_cube_integrable : Integrable (fun ω => V ω ^ 3) ℙ
  l_inv_integrable : Integrable (fun ω => (L ω)⁻¹) ℙ
  l_sq_inv_integrable : Integrable (fun ω => (L ω ^ 2)⁻¹) ℙ
  v_mean : (∫ ω, V ω ∂ℙ) = 1
  v_sq_mean : (∫ ω, V ω ^ 2 ∂ℙ) = 3
  v_cube_mean : (∫ ω, V ω ^ 3 ∂ℙ) = 15
  l_inv_mean : (∫ ω, (L ω)⁻¹ ∂ℙ) = 1 / 22
  l_sq_inv_mean : (∫ ω, (L ω ^ 2)⁻¹ ∂ℙ) = 1 / 440

/-- Transfer integrability of a scalar function through an exact law. -/
private theorem integrable_comp_of_hasLaw
    {X : Ω → ℝ} {μ : Measure ℝ} {ℙ : Measure Ω} {f : ℝ → ℝ}
    (hX : ProbabilityTheory.HasLaw X μ ℙ) (hf : Integrable f μ) :
    Integrable (fun ω => f (X ω)) ℙ := by
  have hfmap : Integrable f (ℙ.map X) := by
    rw [hX.map_eq]
    exact hf
  simpa only [Function.comp_def] using
    (integrable_map_measure hfmap.aestronglyMeasurable hX.aemeasurable).mp hfmap

/--
The two actual gamma laws imply all five moment and integrability facts.
Here `Gamma(1/2,1/2)` is `χ²₁`, while `Gamma(12,1/2)` is `χ²₂₄`.
-/
theorem canonicalFiveMoments13_of_gamma_laws
    (L V : Ω → ℝ) (ℙ : Measure Ω)
    (hL :
      ProbabilityTheory.HasLaw L
        (ProbabilityTheory.gammaMeasure 12 (1 / 2)) ℙ)
    (hV :
      ProbabilityTheory.HasLaw V
        (ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) ℙ) :
    CanonicalFiveMoments13 L V ℙ := by
  have hv1 :
      Integrable (fun x : ℝ => x)
        (ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) := by
    simpa only [Real.rpow_one] using
      (integrable_rpow_gammaMeasure
        (a := (1 / 2 : ℝ)) (r := (1 / 2 : ℝ)) (q := (1 : ℝ))
        (by norm_num) (by norm_num) (by norm_num))
  have hv2 :
      Integrable (fun x : ℝ => x ^ 2)
        (ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) := by
    convert integrable_rpow_gammaMeasure
      (a := (1 / 2 : ℝ)) (r := (1 / 2 : ℝ)) (q := (2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) using 1
    funext x
    rw [Real.rpow_two]
  have hv3 :
      Integrable (fun x : ℝ => x ^ 3)
        (ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) := by
    convert integrable_rpow_gammaMeasure
      (a := (1 / 2 : ℝ)) (r := (1 / 2 : ℝ)) (q := (3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) using 1
    funext x
    norm_num [Real.rpow_natCast]
  have hl1 :
      Integrable (fun x : ℝ => x⁻¹)
        (ProbabilityTheory.gammaMeasure 12 (1 / 2)) := by
    convert integrable_rpow_gammaMeasure
      (a := (12 : ℝ)) (r := (1 / 2 : ℝ)) (q := (-1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) using 1
    funext x
    rw [Real.rpow_neg_one]
  have hl2 :
      Integrable (fun x : ℝ => (x ^ 2)⁻¹)
        (ProbabilityTheory.gammaMeasure 12 (1 / 2)) := by
    convert integrable_rpow_gammaMeasure
      (a := (12 : ℝ)) (r := (1 / 2 : ℝ)) (q := (-2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) using 1
    funext x
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_two]
    simp only [inv_pow]
  refine
    { v_integrable :=
        integrable_comp_of_hasLaw (f := fun x : ℝ => x) hV hv1
      v_sq_integrable :=
        integrable_comp_of_hasLaw (f := fun x : ℝ => x ^ 2) hV hv2
      v_cube_integrable :=
        integrable_comp_of_hasLaw (f := fun x : ℝ => x ^ 3) hV hv3
      l_inv_integrable :=
        integrable_comp_of_hasLaw (f := fun x : ℝ => x⁻¹) hL hl1
      l_sq_inv_integrable :=
        integrable_comp_of_hasLaw (f := fun x : ℝ => (x ^ 2)⁻¹) hL hl2
      v_mean := ?_
      v_sq_mean := ?_
      v_cube_mean := ?_
      l_inv_mean := ?_
      l_sq_inv_mean := ?_ }
  · calc
      (∫ ω, V ω ∂ℙ)
          =
        ∫ x : ℝ, x
          ∂ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2) := by
            simpa only [Function.comp_def] using
              hV.integral_comp hv1.aestronglyMeasurable
      _ = 1 := integral_id_gammaMeasure_half_half
  · calc
      (∫ ω, V ω ^ 2 ∂ℙ)
          =
        ∫ x : ℝ, x ^ 2
          ∂ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2) := by
            simpa only [Function.comp_def] using
              hV.integral_comp hv2.aestronglyMeasurable
      _ = 3 := integral_sq_gammaMeasure_half_half
  · calc
      (∫ ω, V ω ^ 3 ∂ℙ)
          =
        ∫ x : ℝ, x ^ 3
          ∂ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2) := by
            simpa only [Function.comp_def] using
              hV.integral_comp hv3.aestronglyMeasurable
      _ = 15 := integral_cube_gammaMeasure_half_half
  · calc
      (∫ ω, (L ω)⁻¹ ∂ℙ)
          =
        ∫ x : ℝ, x⁻¹
          ∂ProbabilityTheory.gammaMeasure 12 (1 / 2) := by
            simpa only [Function.comp_def] using
              hL.integral_comp hl1.aestronglyMeasurable
      _ = 1 / 22 := integral_inv_gammaMeasure_twelve_half
  · calc
      (∫ ω, (L ω ^ 2)⁻¹ ∂ℙ)
          =
        ∫ x : ℝ, (x ^ 2)⁻¹
          ∂ProbabilityTheory.gammaMeasure 12 (1 / 2) := by
            simpa only [Function.comp_def] using
              hL.integral_comp hl2.aestronglyMeasurable
      _ = 1 / 440 := integral_inv_sq_gammaMeasure_twelve_half

/-- Integrability of the five `P`-coefficient functions used in the reduction. -/
structure CanonicalPFactorIntegrability13
    (s : ℝ) (P : Ω → ℝ) (ℙ : Measure Ω) : Prop where
  linear0 :
    Integrable (fun ω => canonicalLinearFactor0 s (P ω)) ℙ
  linear1 :
    Integrable (fun ω => canonicalLinearFactor1 s (P ω)) ℙ
  quadratic0 :
    Integrable (fun ω => canonicalQuadraticFactor0 s (P ω)) ℙ
  quadratic1 :
    Integrable (fun ω => canonicalQuadraticFactor1 s (P ω)) ℙ
  quadratic2 :
    Integrable (fun ω => canonicalQuadraticFactor2 s (P ω)) ℙ

/-- Independence factors the first nontrivial mixed moment. -/
theorem integral_v_sq_div_l
    (L V : Ω → ℝ) (ℙ : Measure Ω)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : CanonicalFiveMoments13 L V ℙ) :
    Integrable (fun ω => V ω ^ 2 / L ω) ℙ ∧
      (∫ ω, V ω ^ 2 / L ω ∂ℙ) = 3 / 22 := by
  have hind :
      ProbabilityTheory.IndepFun
        (fun ω => V ω ^ 2) (fun ω => (L ω)⁻¹) ℙ := by
    simpa only [Function.comp_def] using
      hVL.comp (by fun_prop : Measurable fun x : ℝ => x ^ 2)
        (by fun_prop : Measurable fun x : ℝ => x⁻¹)
  have hint :
      Integrable (fun ω => V ω ^ 2 / L ω) ℙ := by
    apply (hind.integrable_mul
      hmom.v_sq_integrable hmom.l_inv_integrable).congr
    filter_upwards [] with ω
    simp only [Pi.mul_apply, div_eq_mul_inv]
  refine ⟨hint, ?_⟩
  calc
    (∫ ω, V ω ^ 2 / L ω ∂ℙ)
        =
      (∫ ω, V ω ^ 2 ∂ℙ) * ∫ ω, (L ω)⁻¹ ∂ℙ := by
        simpa only [Pi.mul_apply, div_eq_mul_inv, Function.comp_def] using
          hind.integral_fun_mul_eq_mul_integral
            hmom.v_sq_integrable.aestronglyMeasurable
            hmom.l_inv_integrable.aestronglyMeasurable
    _ = 3 / 22 := by
      rw [hmom.v_sq_mean, hmom.l_inv_mean]
      ring

/-- Independence factors the second nontrivial mixed moment. -/
theorem integral_v_cube_div_l_sq
    (L V : Ω → ℝ) (ℙ : Measure Ω)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : CanonicalFiveMoments13 L V ℙ) :
    Integrable (fun ω => V ω ^ 3 / L ω ^ 2) ℙ ∧
      (∫ ω, V ω ^ 3 / L ω ^ 2 ∂ℙ) = 3 / 88 := by
  have hind :
      ProbabilityTheory.IndepFun
        (fun ω => V ω ^ 3) (fun ω => (L ω ^ 2)⁻¹) ℙ := by
    simpa only [Function.comp_def] using
      hVL.comp (by fun_prop : Measurable fun x : ℝ => x ^ 3)
        (by fun_prop : Measurable fun x : ℝ => (x ^ 2)⁻¹)
  have hint :
      Integrable (fun ω => V ω ^ 3 / L ω ^ 2) ℙ := by
    apply (hind.integrable_mul
      hmom.v_cube_integrable hmom.l_sq_inv_integrable).congr
    filter_upwards [] with ω
    simp only [Pi.mul_apply, div_eq_mul_inv]
  refine ⟨hint, ?_⟩
  calc
    (∫ ω, V ω ^ 3 / L ω ^ 2 ∂ℙ)
        =
      (∫ ω, V ω ^ 3 ∂ℙ) * ∫ ω, (L ω ^ 2)⁻¹ ∂ℙ := by
        simpa only [Pi.mul_apply, div_eq_mul_inv, Function.comp_def] using
          hind.integral_fun_mul_eq_mul_integral
            hmom.v_cube_integrable.aestronglyMeasurable
            hmom.l_sq_inv_integrable.aestronglyMeasurable
    _ = 3 / 88 := by
      rw [hmom.v_cube_mean, hmom.l_sq_inv_mean]
      norm_num

theorem canonicalLinearPIntegrand13_eq_factors (s pcoord : ℝ) :
    canonicalLinearPIntegrand13 s pcoord
      =
    canonicalLinearFactor0 s pcoord
      - (9 / 22) * canonicalLinearFactor1 s pcoord := by
  simp only [canonicalLinearPIntegrand13, canonicalLinearFactor1,
    canonicalLinearFactor0]
  ring

theorem canonicalQuadraticPIntegrand13_eq_factors (s pcoord : ℝ) :
    canonicalQuadraticPIntegrand13 s pcoord
      =
    canonicalQuadraticFactor0 s pcoord
      - (9 / 11) * canonicalQuadraticFactor1 s pcoord
      + (27 / 88) * canonicalQuadraticFactor2 s pcoord := by
  simp only [canonicalQuadraticPIntegrand13, canonicalQuadraticFactor2,
    canonicalQuadraticFactor1, canonicalQuadraticFactor0]
  ring

/--
The linear product reduction required by
`canonicalMomentBridge13_of_product_reductions`.
-/
theorem canonicalLinearH13_product_reduction
    (s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : CanonicalFiveMoments13 L V ℙ)
    (hPint : CanonicalPFactorIntegrability13 s P ℙ) :
    (∫ ω,
      V ω * (canonicalR s (P ω) - canonicalTheta s)
        * canonicalH13 s (P ω) (L ω) (V ω) ∂ℙ)
      =
    4 * ∫ ω, canonicalLinearPIntegrand13 s (P ω) ∂ℙ := by
  obtain ⟨hV2L_int, hV2L_mean⟩ := integral_v_sq_div_l L V ℙ hVL hmom
  have hP0V :
      ProbabilityTheory.IndepFun
        (fun ω => canonicalLinearFactor0 s (P ω)) V ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_canonicalLinearFactor0 s)
        (by fun_prop : Measurable fun z : ℝ × ℝ => z.2)
  have hP1V2L :
      ProbabilityTheory.IndepFun
        (fun ω => canonicalLinearFactor1 s (P ω))
        (fun ω => V ω ^ 2 / L ω) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_canonicalLinearFactor1 s)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 2 / z.1)
  have hterm0 :
      Integrable
        (fun ω => canonicalLinearFactor0 s (P ω) * V ω) ℙ :=
    hP0V.integrable_mul hPint.linear0 hmom.v_integrable
  have hterm1 :
      Integrable
        (fun ω =>
          canonicalLinearFactor1 s (P ω) * (V ω ^ 2 / L ω)) ℙ :=
    hP1V2L.integrable_mul hPint.linear1 hV2L_int
  have hfactor0 :
      (∫ ω, canonicalLinearFactor0 s (P ω) * V ω ∂ℙ)
        =
      ∫ ω, canonicalLinearFactor0 s (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω, canonicalLinearFactor0 s (P ω) ∂ℙ)
            * ∫ ω, V ω ∂ℙ :=
        hP0V.integral_fun_mul_eq_mul_integral
          hPint.linear0.aestronglyMeasurable
          hmom.v_integrable.aestronglyMeasurable
      _ = _ := by rw [hmom.v_mean, mul_one]
  have hfactor1 :
      (∫ ω,
        canonicalLinearFactor1 s (P ω) * (V ω ^ 2 / L ω) ∂ℙ)
        =
      (3 / 22) * ∫ ω, canonicalLinearFactor1 s (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω, canonicalLinearFactor1 s (P ω) ∂ℙ)
            * ∫ ω, V ω ^ 2 / L ω ∂ℙ :=
        hP1V2L.integral_fun_mul_eq_mul_integral
          hPint.linear1.aestronglyMeasurable
          hV2L_int.aestronglyMeasurable
      _ = (3 / 22) * ∫ ω, canonicalLinearFactor1 s (P ω) ∂ℙ := by
        rw [hV2L_mean]
        ring
  calc
    (∫ ω,
      V ω * (canonicalR s (P ω) - canonicalTheta s)
        * canonicalH13 s (P ω) (L ω) (V ω) ∂ℙ)
        =
      ∫ ω,
        4 * (canonicalLinearFactor0 s (P ω) * V ω)
          - 12 *
            (canonicalLinearFactor1 s (P ω)
              * (V ω ^ 2 / L ω)) ∂ℙ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [canonicalLinearH13_expand]
        simp only [canonicalLinearFactor1, canonicalLinearFactor0]
        ring
    _ =
      4 * (∫ ω, canonicalLinearFactor0 s (P ω) * V ω ∂ℙ)
        - 12 *
          (∫ ω,
            canonicalLinearFactor1 s (P ω)
              * (V ω ^ 2 / L ω) ∂ℙ) := by
        rw [integral_sub (hterm0.const_mul 4) (hterm1.const_mul 12),
          integral_const_mul, integral_const_mul]
    _ =
      4 * ∫ ω, canonicalLinearFactor0 s (P ω) ∂ℙ
        - 12 * ((3 / 22) *
          ∫ ω, canonicalLinearFactor1 s (P ω) ∂ℙ) := by
        rw [hfactor0, hfactor1]
    _ =
      4 * ∫ ω, canonicalLinearPIntegrand13 s (P ω) ∂ℙ := by
        rw [show
          (∫ ω, canonicalLinearPIntegrand13 s (P ω) ∂ℙ)
            =
          (∫ ω, canonicalLinearFactor0 s (P ω) ∂ℙ)
            - (9 / 22) *
              ∫ ω, canonicalLinearFactor1 s (P ω) ∂ℙ by
            calc
              _ =
                  ∫ ω,
                    canonicalLinearFactor0 s (P ω)
                      - (9 / 22) *
                        canonicalLinearFactor1 s (P ω) ∂ℙ := by
                    apply integral_congr_ae
                    filter_upwards [] with ω
                    exact canonicalLinearPIntegrand13_eq_factors s (P ω)
              _ = _ := by
                rw [integral_sub hPint.linear0
                  (hPint.linear1.const_mul (9 / 22)),
                  integral_const_mul]]
        ring

/--
The quadratic product reduction required by
`canonicalMomentBridge13_of_product_reductions`.
-/
theorem canonicalQuadraticH13_product_reduction
    (s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : CanonicalFiveMoments13 L V ℙ)
    (hPint : CanonicalPFactorIntegrability13 s P ℙ) :
    (∫ ω,
      V ω * (canonicalH13 s (P ω) (L ω) (V ω)) ^ 2 ∂ℙ)
      =
    16 * ∫ ω, canonicalQuadraticPIntegrand13 s (P ω) ∂ℙ := by
  obtain ⟨hV2L_int, hV2L_mean⟩ := integral_v_sq_div_l L V ℙ hVL hmom
  obtain ⟨hV3L2_int, hV3L2_mean⟩ :=
    integral_v_cube_div_l_sq L V ℙ hVL hmom
  have hP0V :
      ProbabilityTheory.IndepFun
        (fun ω => canonicalQuadraticFactor0 s (P ω)) V ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_canonicalQuadraticFactor0 s)
        (by fun_prop : Measurable fun z : ℝ × ℝ => z.2)
  have hP1V2L :
      ProbabilityTheory.IndepFun
        (fun ω => canonicalQuadraticFactor1 s (P ω))
        (fun ω => V ω ^ 2 / L ω) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_canonicalQuadraticFactor1 s)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 2 / z.1)
  have hP2V3L2 :
      ProbabilityTheory.IndepFun
        (fun ω => canonicalQuadraticFactor2 s (P ω))
        (fun ω => V ω ^ 3 / L ω ^ 2) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_canonicalQuadraticFactor2 s)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 3 / z.1 ^ 2)
  have hterm0 :
      Integrable
        (fun ω => canonicalQuadraticFactor0 s (P ω) * V ω) ℙ :=
    hP0V.integrable_mul hPint.quadratic0 hmom.v_integrable
  have hterm1 :
      Integrable
        (fun ω =>
          canonicalQuadraticFactor1 s (P ω) * (V ω ^ 2 / L ω)) ℙ :=
    hP1V2L.integrable_mul hPint.quadratic1 hV2L_int
  have hterm2 :
      Integrable
        (fun ω =>
          canonicalQuadraticFactor2 s (P ω)
            * (V ω ^ 3 / L ω ^ 2)) ℙ :=
    hP2V3L2.integrable_mul hPint.quadratic2 hV3L2_int
  have hfactor0 :
      (∫ ω, canonicalQuadraticFactor0 s (P ω) * V ω ∂ℙ)
        =
      ∫ ω, canonicalQuadraticFactor0 s (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω, canonicalQuadraticFactor0 s (P ω) ∂ℙ)
            * ∫ ω, V ω ∂ℙ :=
        hP0V.integral_fun_mul_eq_mul_integral
          hPint.quadratic0.aestronglyMeasurable
          hmom.v_integrable.aestronglyMeasurable
      _ = _ := by rw [hmom.v_mean, mul_one]
  have hfactor1 :
      (∫ ω,
        canonicalQuadraticFactor1 s (P ω) * (V ω ^ 2 / L ω) ∂ℙ)
        =
      (3 / 22) * ∫ ω, canonicalQuadraticFactor1 s (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω, canonicalQuadraticFactor1 s (P ω) ∂ℙ)
            * ∫ ω, V ω ^ 2 / L ω ∂ℙ :=
        hP1V2L.integral_fun_mul_eq_mul_integral
          hPint.quadratic1.aestronglyMeasurable
          hV2L_int.aestronglyMeasurable
      _ = _ := by rw [hV2L_mean]; ring
  have hfactor2 :
      (∫ ω,
        canonicalQuadraticFactor2 s (P ω) * (V ω ^ 3 / L ω ^ 2) ∂ℙ)
        =
      (3 / 88) * ∫ ω, canonicalQuadraticFactor2 s (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω, canonicalQuadraticFactor2 s (P ω) ∂ℙ)
            * ∫ ω, V ω ^ 3 / L ω ^ 2 ∂ℙ :=
        hP2V3L2.integral_fun_mul_eq_mul_integral
          hPint.quadratic2.aestronglyMeasurable
          hV3L2_int.aestronglyMeasurable
      _ = _ := by rw [hV3L2_mean]; ring
  calc
    (∫ ω,
      V ω * (canonicalH13 s (P ω) (L ω) (V ω)) ^ 2 ∂ℙ)
        =
      ∫ ω,
        16 * (canonicalQuadraticFactor0 s (P ω) * V ω)
          - 96 *
            (canonicalQuadraticFactor1 s (P ω)
              * (V ω ^ 2 / L ω))
          + 144 *
            (canonicalQuadraticFactor2 s (P ω)
              * (V ω ^ 3 / L ω ^ 2)) ∂ℙ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [canonicalQuadraticH13_expand]
        simp only [canonicalQuadraticFactor2, canonicalQuadraticFactor1,
          canonicalQuadraticFactor0]
        ring
    _ =
      16 * (∫ ω, canonicalQuadraticFactor0 s (P ω) * V ω ∂ℙ)
        - 96 *
          (∫ ω,
            canonicalQuadraticFactor1 s (P ω)
              * (V ω ^ 2 / L ω) ∂ℙ)
        + 144 *
          (∫ ω,
            canonicalQuadraticFactor2 s (P ω)
              * (V ω ^ 3 / L ω ^ 2) ∂ℙ) := by
        calc
          _ =
              (∫ ω,
                16 * (canonicalQuadraticFactor0 s (P ω) * V ω)
                  - 96 *
                    (canonicalQuadraticFactor1 s (P ω)
                      * (V ω ^ 2 / L ω)) ∂ℙ)
                +
              ∫ ω,
                144 *
                  (canonicalQuadraticFactor2 s (P ω)
                    * (V ω ^ 3 / L ω ^ 2)) ∂ℙ := by
                  simpa only [Pi.add_apply, Pi.sub_apply] using
                    integral_add
                      ((hterm0.const_mul 16).sub (hterm1.const_mul 96))
                      (hterm2.const_mul 144)
          _ =
              ((∫ ω,
                16 * (canonicalQuadraticFactor0 s (P ω) * V ω) ∂ℙ)
                  -
                ∫ ω,
                  96 *
                    (canonicalQuadraticFactor1 s (P ω)
                      * (V ω ^ 2 / L ω)) ∂ℙ)
                +
              ∫ ω,
                144 *
                  (canonicalQuadraticFactor2 s (P ω)
                    * (V ω ^ 3 / L ω ^ 2)) ∂ℙ := by
                  rw [integral_sub
                    (hterm0.const_mul 16) (hterm1.const_mul 96)]
          _ = _ := by
            rw [integral_const_mul, integral_const_mul, integral_const_mul]
    _ =
      16 * ∫ ω, canonicalQuadraticFactor0 s (P ω) ∂ℙ
        - 96 * ((3 / 22) *
          ∫ ω, canonicalQuadraticFactor1 s (P ω) ∂ℙ)
        + 144 * ((3 / 88) *
          ∫ ω, canonicalQuadraticFactor2 s (P ω) ∂ℙ) := by
        rw [hfactor0, hfactor1, hfactor2]
    _ =
      16 * ∫ ω, canonicalQuadraticPIntegrand13 s (P ω) ∂ℙ := by
        rw [show
          (∫ ω, canonicalQuadraticPIntegrand13 s (P ω) ∂ℙ)
            =
          (∫ ω, canonicalQuadraticFactor0 s (P ω) ∂ℙ)
            - (9 / 11) *
              ∫ ω, canonicalQuadraticFactor1 s (P ω) ∂ℙ
            + (27 / 88) *
              ∫ ω, canonicalQuadraticFactor2 s (P ω) ∂ℙ by
            calc
              _ =
                  ∫ ω,
                    canonicalQuadraticFactor0 s (P ω)
                      - (9 / 11) *
                        canonicalQuadraticFactor1 s (P ω)
                      + (27 / 88) *
                        canonicalQuadraticFactor2 s (P ω) ∂ℙ := by
                    apply integral_congr_ae
                    filter_upwards [] with ω
                    exact canonicalQuadraticPIntegrand13_eq_factors s (P ω)
              _ = _ := by
                calc
                  _ =
                      (∫ ω,
                        canonicalQuadraticFactor0 s (P ω)
                          - (9 / 11) *
                            canonicalQuadraticFactor1 s (P ω) ∂ℙ)
                        +
                      ∫ ω,
                        (27 / 88) *
                          canonicalQuadraticFactor2 s (P ω) ∂ℙ := by
                            simpa only [Pi.add_apply, Pi.sub_apply] using
                              integral_add
                                (hPint.quadratic0.sub
                                  (hPint.quadratic1.const_mul (9 / 11)))
                                (hPint.quadratic2.const_mul (27 / 88))
                  _ =
                      ((∫ ω, canonicalQuadraticFactor0 s (P ω) ∂ℙ)
                        -
                      ∫ ω,
                        (9 / 11) *
                          canonicalQuadraticFactor1 s (P ω) ∂ℙ)
                        +
                      ∫ ω,
                        (27 / 88) *
                          canonicalQuadraticFactor2 s (P ω) ∂ℙ := by
                            rw [integral_sub hPint.quadratic0
                              (hPint.quadratic1.const_mul (9 / 11))]
                  _ = _ := by
                    rw [integral_const_mul, integral_const_mul]]
        ring

/--
The full linear canonical integrand is integrable under the same product-law
assumptions.  Thus integrability is not an additional bridge hypothesis.
-/
theorem canonicalLinearH13_integrable_of_product
    (s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : CanonicalFiveMoments13 L V ℙ)
    (hPint : CanonicalPFactorIntegrability13 s P ℙ) :
    Integrable
      (fun ω =>
        V ω * (canonicalR s (P ω) - canonicalTheta s)
          * canonicalH13 s (P ω) (L ω) (V ω)) ℙ := by
  obtain ⟨hV2L_int, _⟩ := integral_v_sq_div_l L V ℙ hVL hmom
  have hP0V :
      ProbabilityTheory.IndepFun
        (fun ω => canonicalLinearFactor0 s (P ω)) V ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_canonicalLinearFactor0 s)
        (by fun_prop : Measurable fun z : ℝ × ℝ => z.2)
  have hP1V2L :
      ProbabilityTheory.IndepFun
        (fun ω => canonicalLinearFactor1 s (P ω))
        (fun ω => V ω ^ 2 / L ω) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_canonicalLinearFactor1 s)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 2 / z.1)
  have hterm0 :
      Integrable
        (fun ω => canonicalLinearFactor0 s (P ω) * V ω) ℙ :=
    hP0V.integrable_mul hPint.linear0 hmom.v_integrable
  have hterm1 :
      Integrable
        (fun ω =>
          canonicalLinearFactor1 s (P ω) * (V ω ^ 2 / L ω)) ℙ :=
    hP1V2L.integrable_mul hPint.linear1 hV2L_int
  apply ((hterm0.const_mul 4).sub (hterm1.const_mul 12)).congr
  filter_upwards [] with ω
  rw [canonicalLinearH13_expand]
  simp only [canonicalLinearFactor1, canonicalLinearFactor0,
    Pi.sub_apply]
  ring

/--
The full quadratic canonical integrand is integrable under the same
product-law assumptions.
-/
theorem canonicalQuadraticH13_integrable_of_product
    (s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : CanonicalFiveMoments13 L V ℙ)
    (hPint : CanonicalPFactorIntegrability13 s P ℙ) :
    Integrable
      (fun ω =>
        V ω * (canonicalH13 s (P ω) (L ω) (V ω)) ^ 2) ℙ := by
  obtain ⟨hV2L_int, _⟩ := integral_v_sq_div_l L V ℙ hVL hmom
  obtain ⟨hV3L2_int, _⟩ :=
    integral_v_cube_div_l_sq L V ℙ hVL hmom
  have hP0V :
      ProbabilityTheory.IndepFun
        (fun ω => canonicalQuadraticFactor0 s (P ω)) V ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_canonicalQuadraticFactor0 s)
        (by fun_prop : Measurable fun z : ℝ × ℝ => z.2)
  have hP1V2L :
      ProbabilityTheory.IndepFun
        (fun ω => canonicalQuadraticFactor1 s (P ω))
        (fun ω => V ω ^ 2 / L ω) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_canonicalQuadraticFactor1 s)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 2 / z.1)
  have hP2V3L2 :
      ProbabilityTheory.IndepFun
        (fun ω => canonicalQuadraticFactor2 s (P ω))
        (fun ω => V ω ^ 3 / L ω ^ 2) ℙ := by
    simpa only [Function.comp_def] using
      hP_LV.comp (measurable_canonicalQuadraticFactor2 s)
        (by fun_prop :
          Measurable fun z : ℝ × ℝ => z.2 ^ 3 / z.1 ^ 2)
  have hterm0 :
      Integrable
        (fun ω => canonicalQuadraticFactor0 s (P ω) * V ω) ℙ :=
    hP0V.integrable_mul hPint.quadratic0 hmom.v_integrable
  have hterm1 :
      Integrable
        (fun ω =>
          canonicalQuadraticFactor1 s (P ω) * (V ω ^ 2 / L ω)) ℙ :=
    hP1V2L.integrable_mul hPint.quadratic1 hV2L_int
  have hterm2 :
      Integrable
        (fun ω =>
          canonicalQuadraticFactor2 s (P ω)
            * (V ω ^ 3 / L ω ^ 2)) ℙ :=
    hP2V3L2.integrable_mul hPint.quadratic2 hV3L2_int
  apply (((hterm0.const_mul 16).sub (hterm1.const_mul 96)).add
    (hterm2.const_mul 144)).congr
  filter_upwards [] with ω
  rw [canonicalQuadraticH13_expand]
  simp only [canonicalQuadraticFactor2, canonicalQuadraticFactor1,
    canonicalQuadraticFactor0, Pi.add_apply, Pi.sub_apply]
  ring

/--
Construct the complete canonical moment bridge from joint independence, the
five scalar moments, integrability of the five `P` factors, and the two
centered-beta integration formulas.
-/
theorem canonicalMomentBridge13_of_independence_and_moments
    (Ka s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hs : |s| < 1)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : CanonicalFiveMoments13 L V ℙ)
    (hPint : CanonicalPFactorIntegrability13 s P ℙ)
    (hbeta_linear :
      (∫ ω, canonicalLinearPIntegrand13 s (P ω) ∂ℙ)
        =
      Ka * ∫ x in (-1 : ℝ)..1,
        canonicalLinearPIntegrand13 s ((1 + x) / 2)
          * (1 - x ^ 2) ^ 5)
    (hbeta_quadratic :
      (∫ ω, canonicalQuadraticPIntegrand13 s (P ω) ∂ℙ)
        =
      Ka * ∫ x in (-1 : ℝ)..1,
        canonicalQuadraticPIntegrand13 s ((1 + x) / 2)
          * (1 - x ^ 2) ^ 5) :
    CanonicalMomentBridge13 Ka s P L V ℙ := by
  exact canonicalMomentBridge13_of_product_reductions
    Ka s P L V ℙ hs
    (canonicalLinearH13_integrable_of_product
      s P L V ℙ hP_LV hVL hmom hPint)
    (canonicalQuadraticH13_integrable_of_product
      s P L V ℙ hP_LV hVL hmom hPint)
    (canonicalLinearH13_product_reduction
      s P L V ℙ hP_LV hVL hmom hPint)
    (canonicalQuadraticH13_product_reduction
      s P L V ℙ hP_LV hVL hmom hPint)
    hbeta_linear hbeta_quadratic

/--
Law-level version of `canonicalMomentBridge13_of_independence_and_moments`.
The five scalar moments are discharged from the two gamma laws.
-/
theorem canonicalMomentBridge13_of_gamma_product_laws
    (Ka s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hs : |s| < 1)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hL :
      ProbabilityTheory.HasLaw L
        (ProbabilityTheory.gammaMeasure 12 (1 / 2)) ℙ)
    (hV :
      ProbabilityTheory.HasLaw V
        (ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) ℙ)
    (hPint : CanonicalPFactorIntegrability13 s P ℙ)
    (hbeta_linear :
      (∫ ω, canonicalLinearPIntegrand13 s (P ω) ∂ℙ)
        =
      Ka * ∫ x in (-1 : ℝ)..1,
        canonicalLinearPIntegrand13 s ((1 + x) / 2)
          * (1 - x ^ 2) ^ 5)
    (hbeta_quadratic :
      (∫ ω, canonicalQuadraticPIntegrand13 s (P ω) ∂ℙ)
        =
      Ka * ∫ x in (-1 : ℝ)..1,
        canonicalQuadraticPIntegrand13 s ((1 + x) / 2)
          * (1 - x ^ 2) ^ 5) :
    CanonicalMomentBridge13 Ka s P L V ℙ := by
  exact canonicalMomentBridge13_of_independence_and_moments
    Ka s P L V ℙ hs hP_LV hVL
    (canonicalFiveMoments13_of_gamma_laws L V ℙ hL hV)
    hPint hbeta_linear hbeta_quadratic

end

end GraybillDeal
