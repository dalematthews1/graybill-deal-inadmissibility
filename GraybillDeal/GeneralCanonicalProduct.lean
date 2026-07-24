import GraybillDeal.GeneralCanonicalAlgebra
import GraybillDeal.GeneralGammaMoments
import GraybillDeal.CanonicalProduct
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.HasLaw

/-!
# Product-moment reductions at arbitrary residual degrees of freedom

This file generalizes the probability calculation in `CanonicalProduct.lean`
from the fixed residual degrees of freedom `ν = 12` to arbitrary `ν ≥ 9`.
The only `ν`-dependent scalar inputs are the first two inverse moments of
`L ~ Gamma(ν, 1/2)`.

The joint-coordinate independence assumption

`P ⟂ (L,V)`

is retained explicitly.  Pairwise independence of the three coordinates
would not suffice to factor all of the mixed products below.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/--
The five scalar moments needed for the generic product reduction.

The three `V` moments are independent of `ν`; the two inverse `L` moments
are those of `Gamma(ν,1/2)`.
-/
structure GeneralCanonicalFiveMoments
    (ν : ℝ) (L V : Ω → ℝ) (ℙ : Measure Ω) : Prop where
  v_integrable : Integrable V ℙ
  v_sq_integrable : Integrable (fun ω => V ω ^ 2) ℙ
  v_cube_integrable : Integrable (fun ω => V ω ^ 3) ℙ
  l_inv_integrable : Integrable (fun ω => (L ω)⁻¹) ℙ
  l_sq_inv_integrable : Integrable (fun ω => (L ω ^ 2)⁻¹) ℙ
  v_mean : (∫ ω, V ω ∂ℙ) = 1
  v_sq_mean : (∫ ω, V ω ^ 2 ∂ℙ) = 3
  v_cube_mean : (∫ ω, V ω ^ 3 ∂ℙ) = 15
  l_inv_mean : (∫ ω, (L ω)⁻¹ ∂ℙ) = 1 / (2 * (ν - 1))
  l_sq_inv_mean :
    (∫ ω, (L ω ^ 2)⁻¹ ∂ℙ) = 1 / (4 * (ν - 1) * (ν - 2))

/-- Transfer integrability of a real-valued test function through an exact law. -/
private theorem general_integrable_comp_of_hasLaw
    {X : Ω → ℝ} {μ : Measure ℝ} {ℙ : Measure Ω} {f : ℝ → ℝ}
    (hX : ProbabilityTheory.HasLaw X μ ℙ) (hf : Integrable f μ) :
    Integrable (fun ω => f (X ω)) ℙ := by
  have hfmap : Integrable f (ℙ.map X) := by
    rw [hX.map_eq]
    exact hf
  simpa only [Function.comp_def] using
    (integrable_map_measure hfmap.aestronglyMeasurable hX.aemeasurable).mp hfmap

/--
The laws `L ~ Gamma(ν,1/2)` and `V ~ Gamma(1/2,1/2)` supply all five
moments needed in the reduction.
-/
theorem generalCanonicalFiveMoments_of_gamma_laws
    (ν : ℝ) (hν : 9 ≤ ν)
    (L V : Ω → ℝ) (ℙ : Measure Ω)
    (hL :
      ProbabilityTheory.HasLaw L
        (ProbabilityTheory.gammaMeasure ν (1 / 2)) ℙ)
    (hV :
      ProbabilityTheory.HasLaw V
        (ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) ℙ) :
    GeneralCanonicalFiveMoments ν L V ℙ := by
  have hν1 : 1 < ν := by linarith
  have hν2 : 2 < ν := by linarith
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
        (ProbabilityTheory.gammaMeasure ν (1 / 2)) :=
    integrable_inv_gammaMeasure_half hν1
  have hl2 :
      Integrable (fun x : ℝ => (x ^ 2)⁻¹)
        (ProbabilityTheory.gammaMeasure ν (1 / 2)) :=
    integrable_inv_sq_gammaMeasure_half hν2
  refine
    { v_integrable :=
        general_integrable_comp_of_hasLaw (f := fun x : ℝ => x) hV hv1
      v_sq_integrable :=
        general_integrable_comp_of_hasLaw (f := fun x : ℝ => x ^ 2) hV hv2
      v_cube_integrable :=
        general_integrable_comp_of_hasLaw (f := fun x : ℝ => x ^ 3) hV hv3
      l_inv_integrable :=
        general_integrable_comp_of_hasLaw (f := fun x : ℝ => x⁻¹) hL hl1
      l_sq_inv_integrable :=
        general_integrable_comp_of_hasLaw
          (f := fun x : ℝ => (x ^ 2)⁻¹) hL hl2
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
          ∂ProbabilityTheory.gammaMeasure ν (1 / 2) := by
            simpa only [Function.comp_def] using
              hL.integral_comp hl1.aestronglyMeasurable
      _ = 1 / (2 * (ν - 1)) := integral_inv_gammaMeasure_half hν1
  · calc
      (∫ ω, (L ω ^ 2)⁻¹ ∂ℙ)
          =
        ∫ x : ℝ, (x ^ 2)⁻¹
          ∂ProbabilityTheory.gammaMeasure ν (1 / 2) := by
            simpa only [Function.comp_def] using
              hL.integral_comp hl2.aestronglyMeasurable
      _ = 1 / (4 * (ν - 1) * (ν - 2)) :=
        integral_inv_sq_gammaMeasure_half hν2

/-- Independence factors `E[V²/L]` at arbitrary `ν`. -/
theorem general_integral_v_sq_div_l
    (ν : ℝ) (L V : Ω → ℝ) (ℙ : Measure Ω)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : GeneralCanonicalFiveMoments ν L V ℙ) :
    Integrable (fun ω => V ω ^ 2 / L ω) ℙ ∧
      (∫ ω, V ω ^ 2 / L ω ∂ℙ) = 3 / (2 * (ν - 1)) := by
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
    _ = 3 / (2 * (ν - 1)) := by
      rw [hmom.v_sq_mean, hmom.l_inv_mean]
      ring

/-- Independence factors `E[V³/L²]` at arbitrary `ν`. -/
theorem general_integral_v_cube_div_l_sq
    (ν : ℝ) (L V : Ω → ℝ) (ℙ : Measure Ω)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : GeneralCanonicalFiveMoments ν L V ℙ) :
    Integrable (fun ω => V ω ^ 3 / L ω ^ 2) ℙ ∧
      (∫ ω, V ω ^ 3 / L ω ^ 2 ∂ℙ)
        = 15 / (4 * (ν - 1) * (ν - 2)) := by
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
    _ = 15 / (4 * (ν - 1) * (ν - 2)) := by
      rw [hmom.v_cube_mean, hmom.l_sq_inv_mean]
      ring

/--
Pointwise expansion of the generic linear `V(r-θ)h` integrand into the two
mixed products used by the independence calculation.
-/
theorem generalCanonicalLinearH_expand
    (ν s pcoord l v : ℝ) :
    v * (canonicalR s pcoord - canonicalTheta s)
        * generalCanonicalH ν s pcoord l v
      =
    4 * (canonicalLinearFactor0 s pcoord * v)
      - ν * (canonicalLinearFactor1 s pcoord * (v ^ 2 / l)) := by
  calc
    v * (canonicalR s pcoord - canonicalTheta s)
          * generalCanonicalH ν s pcoord l v
        =
      4 *
        (v * (canonicalRTheta (canonicalTheta s) pcoord
            - canonicalTheta s)
          * canonicalG ν (canonicalTheta s) pcoord l v) := by
            unfold generalCanonicalH
            rw [canonicalRTheta_canonicalTheta]
            ring
    _ =
      4 *
        (((canonicalRTheta (canonicalTheta s) pcoord
              - canonicalTheta s)
            * weightPolynomial
              (canonicalRTheta (canonicalTheta s) pcoord)) * v
          - (ν / 4)
            * (((canonicalRTheta (canonicalTheta s) pcoord
                  - canonicalTheta s)
                * weightPolynomial
                  (canonicalRTheta (canonicalTheta s) pcoord))
              / canonicalDenomTheta (canonicalTheta s) pcoord)
            * (v ^ 2 / l)) := by
              rw [canonicalLinearIntegrand_expand]
    _ =
      4 * (canonicalLinearFactor0 s pcoord * v)
        - ν * (canonicalLinearFactor1 s pcoord * (v ^ 2 / l)) := by
          simp only [canonicalRTheta_canonicalTheta,
            canonicalDenomTheta_canonicalTheta,
            canonicalLinearFactor0, canonicalLinearFactor1]
          ring

/--
Pointwise expansion of the generic quadratic `Vh²` integrand into the three
mixed products used by the independence calculation.
-/
theorem generalCanonicalQuadraticH_expand
    (ν s pcoord l v : ℝ) :
    v * generalCanonicalH ν s pcoord l v ^ 2
      =
    16 * (canonicalQuadraticFactor0 s pcoord * v)
      - (8 * ν)
        * (canonicalQuadraticFactor1 s pcoord * (v ^ 2 / l))
      + ν ^ 2
        * (canonicalQuadraticFactor2 s pcoord * (v ^ 3 / l ^ 2)) := by
  calc
    v * generalCanonicalH ν s pcoord l v ^ 2
        =
      16 *
        (v * canonicalG ν (canonicalTheta s) pcoord l v ^ 2) := by
          unfold generalCanonicalH
          ring
    _ =
      16 *
        (weightPolynomial
              (canonicalRTheta (canonicalTheta s) pcoord) ^ 2 * v
          - (ν / 2)
            * (weightPolynomial
                  (canonicalRTheta (canonicalTheta s) pcoord) ^ 2
              / canonicalDenomTheta (canonicalTheta s) pcoord)
            * (v ^ 2 / l)
          + (ν ^ 2 / 16)
            * (weightPolynomial
                  (canonicalRTheta (canonicalTheta s) pcoord) ^ 2
              / canonicalDenomTheta (canonicalTheta s) pcoord ^ 2)
            * (v ^ 3 / l ^ 2)) := by
              rw [canonicalQuadraticIntegrand_expand]
    _ =
      16 * (canonicalQuadraticFactor0 s pcoord * v)
        - (8 * ν)
          * (canonicalQuadraticFactor1 s pcoord * (v ^ 2 / l))
        + ν ^ 2
          * (canonicalQuadraticFactor2 s pcoord * (v ^ 3 / l ^ 2)) := by
            simp only [canonicalRTheta_canonicalTheta,
              canonicalDenomTheta_canonicalTheta,
              canonicalQuadraticFactor0, canonicalQuadraticFactor1,
              canonicalQuadraticFactor2]
            ring

theorem generalCanonicalLinearPIntegrand_eq_factors
    (ν s pcoord : ℝ) :
    generalCanonicalLinearPIntegrand ν s pcoord
      =
    canonicalLinearFactor0 s pcoord
      - (3 * ν / (8 * (ν - 1)))
        * canonicalLinearFactor1 s pcoord := by
  simp only [generalCanonicalLinearPIntegrand, canonicalLinearFactor1,
    canonicalLinearFactor0, div_eq_mul_inv, mul_inv]
  ring

theorem generalCanonicalQuadraticPIntegrand_eq_factors
    (ν s pcoord : ℝ) :
    generalCanonicalQuadraticPIntegrand ν s pcoord
      =
    canonicalQuadraticFactor0 s pcoord
      - (3 * ν / (4 * (ν - 1)))
        * canonicalQuadraticFactor1 s pcoord
      + (15 * ν ^ 2 / (64 * (ν - 1) * (ν - 2)))
        * canonicalQuadraticFactor2 s pcoord := by
  simp only [generalCanonicalQuadraticPIntegrand, canonicalQuadraticFactor2,
    canonicalQuadraticFactor1, canonicalQuadraticFactor0,
    div_eq_mul_inv, mul_inv]
  ring

/--
Integrating out `L,V` reduces the generic linear canonical moment to its
one-dimensional `P`-integrand.
-/
theorem generalCanonicalLinearH_product_reduction
    (ν s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : GeneralCanonicalFiveMoments ν L V ℙ)
    (hPint : CanonicalPFactorIntegrability13 s P ℙ) :
    (∫ ω,
      V ω * (canonicalR s (P ω) - canonicalTheta s)
        * generalCanonicalH ν s (P ω) (L ω) (V ω) ∂ℙ)
      =
    4 * ∫ ω, generalCanonicalLinearPIntegrand ν s (P ω) ∂ℙ := by
  obtain ⟨hV2L_int, hV2L_mean⟩ :=
    general_integral_v_sq_div_l ν L V ℙ hVL hmom
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
      (3 / (2 * (ν - 1)))
        * ∫ ω, canonicalLinearFactor1 s (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω, canonicalLinearFactor1 s (P ω) ∂ℙ)
            * ∫ ω, V ω ^ 2 / L ω ∂ℙ :=
        hP1V2L.integral_fun_mul_eq_mul_integral
          hPint.linear1.aestronglyMeasurable
          hV2L_int.aestronglyMeasurable
      _ =
        (3 / (2 * (ν - 1)))
          * ∫ ω, canonicalLinearFactor1 s (P ω) ∂ℙ := by
            rw [hV2L_mean]
            ring
  calc
    (∫ ω,
      V ω * (canonicalR s (P ω) - canonicalTheta s)
        * generalCanonicalH ν s (P ω) (L ω) (V ω) ∂ℙ)
        =
      ∫ ω,
        4 * (canonicalLinearFactor0 s (P ω) * V ω)
          - ν *
            (canonicalLinearFactor1 s (P ω)
              * (V ω ^ 2 / L ω)) ∂ℙ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact generalCanonicalLinearH_expand
          ν s (P ω) (L ω) (V ω)
    _ =
      4 * (∫ ω, canonicalLinearFactor0 s (P ω) * V ω ∂ℙ)
        - ν *
          (∫ ω,
            canonicalLinearFactor1 s (P ω)
              * (V ω ^ 2 / L ω) ∂ℙ) := by
        rw [integral_sub (hterm0.const_mul 4) (hterm1.const_mul ν),
          integral_const_mul, integral_const_mul]
    _ =
      4 * ∫ ω, canonicalLinearFactor0 s (P ω) ∂ℙ
        - ν * ((3 / (2 * (ν - 1))) *
          ∫ ω, canonicalLinearFactor1 s (P ω) ∂ℙ) := by
        rw [hfactor0, hfactor1]
    _ =
      4 * ∫ ω, generalCanonicalLinearPIntegrand ν s (P ω) ∂ℙ := by
        rw [show
          (∫ ω, generalCanonicalLinearPIntegrand ν s (P ω) ∂ℙ)
            =
          (∫ ω, canonicalLinearFactor0 s (P ω) ∂ℙ)
            - (3 * ν / (8 * (ν - 1))) *
              ∫ ω, canonicalLinearFactor1 s (P ω) ∂ℙ by
            calc
              _ =
                  ∫ ω,
                    canonicalLinearFactor0 s (P ω)
                      - (3 * ν / (8 * (ν - 1))) *
                        canonicalLinearFactor1 s (P ω) ∂ℙ := by
                    apply integral_congr_ae
                    filter_upwards [] with ω
                    exact generalCanonicalLinearPIntegrand_eq_factors
                      ν s (P ω)
              _ = _ := by
                rw [integral_sub hPint.linear0
                  (hPint.linear1.const_mul
                    (3 * ν / (8 * (ν - 1)))),
                  integral_const_mul]]
        simp only [div_eq_mul_inv, mul_inv]
        ring

/--
Integrating out `L,V` reduces the generic quadratic canonical moment to its
one-dimensional `P`-integrand.
-/
theorem generalCanonicalQuadraticH_product_reduction
    (ν s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : GeneralCanonicalFiveMoments ν L V ℙ)
    (hPint : CanonicalPFactorIntegrability13 s P ℙ) :
    (∫ ω,
      V ω * generalCanonicalH ν s (P ω) (L ω) (V ω) ^ 2 ∂ℙ)
      =
    16 * ∫ ω, generalCanonicalQuadraticPIntegrand ν s (P ω) ∂ℙ := by
  obtain ⟨hV2L_int, hV2L_mean⟩ :=
    general_integral_v_sq_div_l ν L V ℙ hVL hmom
  obtain ⟨hV3L2_int, hV3L2_mean⟩ :=
    general_integral_v_cube_div_l_sq ν L V ℙ hVL hmom
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
      (3 / (2 * (ν - 1)))
        * ∫ ω, canonicalQuadraticFactor1 s (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω, canonicalQuadraticFactor1 s (P ω) ∂ℙ)
            * ∫ ω, V ω ^ 2 / L ω ∂ℙ :=
        hP1V2L.integral_fun_mul_eq_mul_integral
          hPint.quadratic1.aestronglyMeasurable
          hV2L_int.aestronglyMeasurable
      _ = _ := by
        rw [hV2L_mean]
        ring
  have hfactor2 :
      (∫ ω,
        canonicalQuadraticFactor2 s (P ω)
          * (V ω ^ 3 / L ω ^ 2) ∂ℙ)
        =
      (15 / (4 * (ν - 1) * (ν - 2)))
        * ∫ ω, canonicalQuadraticFactor2 s (P ω) ∂ℙ := by
    calc
      _ =
          (∫ ω, canonicalQuadraticFactor2 s (P ω) ∂ℙ)
            * ∫ ω, V ω ^ 3 / L ω ^ 2 ∂ℙ :=
        hP2V3L2.integral_fun_mul_eq_mul_integral
          hPint.quadratic2.aestronglyMeasurable
          hV3L2_int.aestronglyMeasurable
      _ = _ := by
        rw [hV3L2_mean]
        ring
  calc
    (∫ ω,
      V ω * generalCanonicalH ν s (P ω) (L ω) (V ω) ^ 2 ∂ℙ)
        =
      ∫ ω,
        16 * (canonicalQuadraticFactor0 s (P ω) * V ω)
          - (8 * ν) *
            (canonicalQuadraticFactor1 s (P ω)
              * (V ω ^ 2 / L ω))
          + ν ^ 2 *
            (canonicalQuadraticFactor2 s (P ω)
              * (V ω ^ 3 / L ω ^ 2)) ∂ℙ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact generalCanonicalQuadraticH_expand
          ν s (P ω) (L ω) (V ω)
    _ =
      16 * (∫ ω, canonicalQuadraticFactor0 s (P ω) * V ω ∂ℙ)
        - (8 * ν) *
          (∫ ω,
            canonicalQuadraticFactor1 s (P ω)
              * (V ω ^ 2 / L ω) ∂ℙ)
        + ν ^ 2 *
          (∫ ω,
            canonicalQuadraticFactor2 s (P ω)
              * (V ω ^ 3 / L ω ^ 2) ∂ℙ) := by
        calc
          _ =
              (∫ ω,
                16 * (canonicalQuadraticFactor0 s (P ω) * V ω)
                  - (8 * ν) *
                    (canonicalQuadraticFactor1 s (P ω)
                      * (V ω ^ 2 / L ω)) ∂ℙ)
                +
              ∫ ω,
                ν ^ 2 *
                  (canonicalQuadraticFactor2 s (P ω)
                    * (V ω ^ 3 / L ω ^ 2)) ∂ℙ := by
                  simpa only [Pi.add_apply, Pi.sub_apply] using
                    integral_add
                      ((hterm0.const_mul 16).sub
                        (hterm1.const_mul (8 * ν)))
                      (hterm2.const_mul (ν ^ 2))
          _ =
              ((∫ ω,
                16 * (canonicalQuadraticFactor0 s (P ω) * V ω) ∂ℙ)
                  -
                ∫ ω,
                  (8 * ν) *
                    (canonicalQuadraticFactor1 s (P ω)
                      * (V ω ^ 2 / L ω)) ∂ℙ)
                +
              ∫ ω,
                ν ^ 2 *
                  (canonicalQuadraticFactor2 s (P ω)
                    * (V ω ^ 3 / L ω ^ 2)) ∂ℙ := by
                  rw [integral_sub
                    (hterm0.const_mul 16)
                    (hterm1.const_mul (8 * ν))]
          _ = _ := by
            rw [integral_const_mul, integral_const_mul, integral_const_mul]
    _ =
      16 * ∫ ω, canonicalQuadraticFactor0 s (P ω) ∂ℙ
        - (8 * ν) * ((3 / (2 * (ν - 1))) *
          ∫ ω, canonicalQuadraticFactor1 s (P ω) ∂ℙ)
        + ν ^ 2 * ((15 / (4 * (ν - 1) * (ν - 2))) *
          ∫ ω, canonicalQuadraticFactor2 s (P ω) ∂ℙ) := by
        rw [hfactor0, hfactor1, hfactor2]
    _ =
      16 * ∫ ω, generalCanonicalQuadraticPIntegrand ν s (P ω) ∂ℙ := by
        rw [show
          (∫ ω, generalCanonicalQuadraticPIntegrand ν s (P ω) ∂ℙ)
            =
          (∫ ω, canonicalQuadraticFactor0 s (P ω) ∂ℙ)
            - (3 * ν / (4 * (ν - 1))) *
              ∫ ω, canonicalQuadraticFactor1 s (P ω) ∂ℙ
            + (15 * ν ^ 2 / (64 * (ν - 1) * (ν - 2))) *
              ∫ ω, canonicalQuadraticFactor2 s (P ω) ∂ℙ by
            calc
              _ =
                  ∫ ω,
                    canonicalQuadraticFactor0 s (P ω)
                      - (3 * ν / (4 * (ν - 1))) *
                        canonicalQuadraticFactor1 s (P ω)
                      + (15 * ν ^ 2 /
                          (64 * (ν - 1) * (ν - 2))) *
                        canonicalQuadraticFactor2 s (P ω) ∂ℙ := by
                    apply integral_congr_ae
                    filter_upwards [] with ω
                    exact generalCanonicalQuadraticPIntegrand_eq_factors
                      ν s (P ω)
              _ = _ := by
                calc
                  _ =
                      (∫ ω,
                        canonicalQuadraticFactor0 s (P ω)
                          - (3 * ν / (4 * (ν - 1))) *
                            canonicalQuadraticFactor1 s (P ω) ∂ℙ)
                        +
                      ∫ ω,
                        (15 * ν ^ 2 /
                          (64 * (ν - 1) * (ν - 2))) *
                          canonicalQuadraticFactor2 s (P ω) ∂ℙ := by
                            simpa only [Pi.add_apply, Pi.sub_apply] using
                              integral_add
                                (hPint.quadratic0.sub
                                  (hPint.quadratic1.const_mul
                                    (3 * ν / (4 * (ν - 1)))))
                                (hPint.quadratic2.const_mul
                                  (15 * ν ^ 2 /
                                    (64 * (ν - 1) * (ν - 2))))
                  _ =
                      ((∫ ω, canonicalQuadraticFactor0 s (P ω) ∂ℙ)
                        -
                      ∫ ω,
                        (3 * ν / (4 * (ν - 1))) *
                          canonicalQuadraticFactor1 s (P ω) ∂ℙ)
                        +
                      ∫ ω,
                        (15 * ν ^ 2 /
                          (64 * (ν - 1) * (ν - 2))) *
                          canonicalQuadraticFactor2 s (P ω) ∂ℙ := by
                            rw [integral_sub hPint.quadratic0
                              (hPint.quadratic1.const_mul
                                (3 * ν / (4 * (ν - 1))))]
                  _ = _ := by
                    rw [integral_const_mul, integral_const_mul]]
        simp only [div_eq_mul_inv, mul_inv]
        ring

/-- Integrability of the full generic linear canonical integrand. -/
theorem generalCanonicalLinearH_integrable_of_product
    (ν s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : GeneralCanonicalFiveMoments ν L V ℙ)
    (hPint : CanonicalPFactorIntegrability13 s P ℙ) :
    Integrable
      (fun ω =>
        V ω * (canonicalR s (P ω) - canonicalTheta s)
          * generalCanonicalH ν s (P ω) (L ω) (V ω)) ℙ := by
  obtain ⟨hV2L_int, _⟩ :=
    general_integral_v_sq_div_l ν L V ℙ hVL hmom
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
  apply ((hterm0.const_mul 4).sub (hterm1.const_mul ν)).congr
  filter_upwards [] with ω
  simpa only [Pi.sub_apply] using
    (generalCanonicalLinearH_expand ν s (P ω) (L ω) (V ω)).symm

/-- Integrability of the full generic quadratic canonical integrand. -/
theorem generalCanonicalQuadraticH_integrable_of_product
    (ν s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : GeneralCanonicalFiveMoments ν L V ℙ)
    (hPint : CanonicalPFactorIntegrability13 s P ℙ) :
    Integrable
      (fun ω =>
        V ω * generalCanonicalH ν s (P ω) (L ω) (V ω) ^ 2) ℙ := by
  obtain ⟨hV2L_int, _⟩ :=
    general_integral_v_sq_div_l ν L V ℙ hVL hmom
  obtain ⟨hV3L2_int, _⟩ :=
    general_integral_v_cube_div_l_sq ν L V ℙ hVL hmom
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
  apply (((hterm0.const_mul 16).sub (hterm1.const_mul (8 * ν))).add
    (hterm2.const_mul (ν ^ 2))).congr
  filter_upwards [] with ω
  simpa only [Pi.add_apply, Pi.sub_apply] using
    (generalCanonicalQuadraticH_expand ν s (P ω) (L ω) (V ω)).symm

/--
Construct the generic canonical moment bridge from joint independence, the
five scalar moments, integrability of the five `P` factors, and the two
centered-beta integration formulas.
-/
theorem generalCanonicalMomentBridge_of_independence_and_moments
    (Ka ν s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hν : 9 ≤ ν) (hs : |s| < 1)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hmom : GeneralCanonicalFiveMoments ν L V ℙ)
    (hPint : CanonicalPFactorIntegrability13 s P ℙ)
    (hbeta_linear :
      (∫ ω, generalCanonicalLinearPIntegrand ν s (P ω) ∂ℙ)
        =
      Ka * ∫ x in (-1 : ℝ)..1,
        generalCanonicalLinearPIntegrand ν s ((1 + x) / 2)
          * (1 - x ^ 2) ^ (ν / 2 - 1))
    (hbeta_quadratic :
      (∫ ω, generalCanonicalQuadraticPIntegrand ν s (P ω) ∂ℙ)
        =
      Ka * ∫ x in (-1 : ℝ)..1,
        generalCanonicalQuadraticPIntegrand ν s ((1 + x) / 2)
          * (1 - x ^ 2) ^ (ν / 2 - 1)) :
    GeneralCanonicalMomentBridge Ka ν s P L V ℙ := by
  refine
    { linear_integrable :=
        generalCanonicalLinearH_integrable_of_product
          ν s P L V ℙ hP_LV hVL hmom hPint
      quadratic_integrable :=
        generalCanonicalQuadraticH_integrable_of_product
          ν s P L V ℙ hP_LV hVL hmom hPint
      linear_moment := ?_
      quadratic_moment := ?_ }
  · rw [generalCanonicalLinearH_product_reduction
          ν s P L V ℙ hP_LV hVL hmom hPint,
      generalCanonicalLinearPExpectation_eq_generalBg
        Ka ν s P ℙ hν hs hbeta_linear]
    unfold generalBtheta
    rfl
  · rw [generalCanonicalQuadraticH_product_reduction
          ν s P L V ℙ hP_LV hVL hmom hPint,
      generalCanonicalQuadraticPExpectation_eq_generalCg
        Ka ν s P ℙ hν hs hbeta_quadratic]
    unfold generalCtheta
    rfl

/--
Law-level version of
`generalCanonicalMomentBridge_of_independence_and_moments`: the five scalar
moments are discharged from the two gamma laws.
-/
theorem generalCanonicalMomentBridge_of_gamma_product_laws
    (Ka ν s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hν : 9 ≤ ν) (hs : |s| < 1)
    (hP_LV : ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) ℙ)
    (hVL : ProbabilityTheory.IndepFun V L ℙ)
    (hL :
      ProbabilityTheory.HasLaw L
        (ProbabilityTheory.gammaMeasure ν (1 / 2)) ℙ)
    (hV :
      ProbabilityTheory.HasLaw V
        (ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) ℙ)
    (hPint : CanonicalPFactorIntegrability13 s P ℙ)
    (hbeta_linear :
      (∫ ω, generalCanonicalLinearPIntegrand ν s (P ω) ∂ℙ)
        =
      Ka * ∫ x in (-1 : ℝ)..1,
        generalCanonicalLinearPIntegrand ν s ((1 + x) / 2)
          * (1 - x ^ 2) ^ (ν / 2 - 1))
    (hbeta_quadratic :
      (∫ ω, generalCanonicalQuadraticPIntegrand ν s (P ω) ∂ℙ)
        =
      Ka * ∫ x in (-1 : ℝ)..1,
        generalCanonicalQuadraticPIntegrand ν s ((1 + x) / 2)
          * (1 - x ^ 2) ^ (ν / 2 - 1)) :
    GeneralCanonicalMomentBridge Ka ν s P L V ℙ := by
  exact generalCanonicalMomentBridge_of_independence_and_moments
    Ka ν s P L V ℙ hν hs hP_LV hVL
    (generalCanonicalFiveMoments_of_gamma_laws ν hν L V ℙ hL hV)
    hPint hbeta_linear hbeta_quadratic

end

end GraybillDeal
