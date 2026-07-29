import GraybillDeal.GeneralBetaBridge
import GraybillDeal.GeneralCanonicalAlgebra
import GraybillDeal.GeneralCanonicalProduct
import GraybillDeal.CanonicalLaws

/-!
# Canonical component-law bridge at arbitrary sample size

This file supplies the law-level endpoint of the general canonical product
reduction.  The first section is independent of the residual degrees of
freedom: every symmetric beta law is supported on `[0,1]`, and therefore
the five rational `P`-factors used by the canonical product expansion are
integrable for every interior variance ratio.
-/

namespace GraybillDeal

open MeasureTheory Set ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Every symmetric beta measure is concentrated on `[0,1]`. -/
theorem betaMeasure_same_ae_mem_Icc (a : ℝ) :
    ∀ᵐ p : ℝ ∂betaMeasure a a, p ∈ Icc (0 : ℝ) 1 := by
  unfold betaMeasure betaPDF
  rw [ae_withDensity_iff
    ((measurable_betaPDFReal a a).ennreal_ofReal)]
  filter_upwards [] with p hp
  have hp_pos : 0 < p := by
    by_contra h
    exact hp (betaPDF_eq_zero_of_nonpos (le_of_not_gt h))
  have hp_lt : p < 1 := by
    by_contra h
    exact hp (betaPDF_eq_zero_of_one_le (le_of_not_gt h))
  exact ⟨hp_pos.le, hp_lt.le⟩

/--
All five coefficient functions of `P` in the canonical product reduction
are integrable under any `Beta(a,a)` law with `a > 0`.
-/
theorem canonicalPFactorIntegrability13_of_beta_same_law
    {a : ℝ} (ha : 0 < a)
    (s : ℝ) (P : Ω → ℝ) (Pmeasure : Measure Ω)
    (hs : |s| < 1)
    (hP : HasLaw P (betaMeasure a a) Pmeasure) :
    CanonicalPFactorIntegrability13 s P Pmeasure := by
  let c : ℝ := (1 - |s|) / 2
  have hcpos : 0 < c := by
    dsimp only [c]
    linarith
  letI : IsProbabilityMeasure (betaMeasure a a) :=
    isProbabilityMeasureBeta ha ha
  letI : IsProbabilityMeasure Pmeasure := hP.isProbabilityMeasure
  have hP_support :
      ∀ᵐ ω ∂Pmeasure, P ω ∈ Icc (0 : ℝ) 1 := by
    exact (hP.ae_iff measurableSet_Icc.mem).2
      (betaMeasure_same_ae_mem_Icc a)
  have hfactor_bounds :
      ∀ᵐ ω ∂Pmeasure,
        |canonicalLinearFactor0 s (P ω)| ≤ 1
        ∧ |canonicalLinearFactor1 s (P ω)| ≤ c⁻¹
        ∧ |canonicalQuadraticFactor0 s (P ω)| ≤ 1
        ∧ |canonicalQuadraticFactor1 s (P ω)| ≤ c⁻¹
        ∧ |canonicalQuadraticFactor2 s (P ω)| ≤ (c ^ 2)⁻¹ := by
    filter_upwards [hP_support] with ω hp
    have hr := canonicalR_mem_Icc_of_mem_Icc hs hp
    have htheta := canonicalTheta_mem_Icc hs
    have hden_lower :
        c ≤ canonicalDenom s (P ω) := by
      exact canonicalDenom_lower_of_mem_Icc hs hp
    have hdenpos : 0 < canonicalDenom s (P ω) :=
      lt_of_lt_of_le hcpos hden_lower
    have hpoly :
        |weightPolynomial (canonicalR s (P ω))| ≤ 1 :=
      abs_weightPolynomial_le_one hr
    have hrtheta :
        |canonicalR s (P ω) - canonicalTheta s| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hr.1, hr.2, htheta.1, htheta.2]
    have hlinear0 :
        |canonicalLinearFactor0 s (P ω)| ≤ 1 := by
      unfold canonicalLinearFactor0
      rw [abs_mul]
      calc
        |canonicalR s (P ω) - canonicalTheta s|
              * |weightPolynomial (canonicalR s (P ω))|
            ≤ 1 * 1 :=
          mul_le_mul hrtheta hpoly (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hlinear1 :
        |canonicalLinearFactor1 s (P ω)| ≤ c⁻¹ := by
      unfold canonicalLinearFactor1
      rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
      calc
        |canonicalLinearFactor0 s (P ω)| ≤ 1 := hlinear0
        _ ≤ c⁻¹ * canonicalDenom s (P ω) := by
          rw [inv_mul_eq_div, le_div_iff₀ hcpos]
          simpa only [one_mul] using hden_lower
    have hquadratic0 :
        |canonicalQuadraticFactor0 s (P ω)| ≤ 1 := by
      unfold canonicalQuadraticFactor0
      rw [abs_sq]
      rw [← one_pow 2, sq_le_sq, abs_one]
      exact hpoly
    have hquadratic1 :
        |canonicalQuadraticFactor1 s (P ω)| ≤ c⁻¹ := by
      unfold canonicalQuadraticFactor1
      rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
      calc
        |canonicalQuadraticFactor0 s (P ω)| ≤ 1 := hquadratic0
        _ ≤ c⁻¹ * canonicalDenom s (P ω) := by
          rw [inv_mul_eq_div, le_div_iff₀ hcpos]
          simpa only [one_mul] using hden_lower
    have hden_sq_lower :
        c ^ 2 ≤ canonicalDenom s (P ω) ^ 2 := by
      nlinarith
    have hden_sq_pos :
        0 < canonicalDenom s (P ω) ^ 2 := sq_pos_of_pos hdenpos
    have hc_sq_pos : 0 < c ^ 2 := sq_pos_of_pos hcpos
    have hquadratic2 :
        |canonicalQuadraticFactor2 s (P ω)| ≤ (c ^ 2)⁻¹ := by
      unfold canonicalQuadraticFactor2
      rw [abs_div, abs_of_pos hden_sq_pos, div_le_iff₀ hden_sq_pos]
      calc
        |canonicalQuadraticFactor0 s (P ω)| ≤ 1 := hquadratic0
        _ ≤ (c ^ 2)⁻¹ * canonicalDenom s (P ω) ^ 2 := by
          rw [inv_mul_eq_div, le_div_iff₀ hc_sq_pos]
          simpa only [one_mul] using hden_sq_lower
    exact
      ⟨hlinear0, hlinear1, hquadratic0, hquadratic1, hquadratic2⟩
  refine
    { linear0 := ?_
      linear1 := ?_
      quadratic0 := ?_
      quadratic1 := ?_
      quadratic2 := ?_ }
  · apply (integrable_const (c := (1 : ℝ))).mono'
      (show AEStronglyMeasurable
          (fun ω => canonicalLinearFactor0 s (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_canonicalLinearFactor0 s).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa only [Real.norm_eq_abs, norm_one] using hω.1
  · apply (integrable_const (c := c⁻¹)).mono'
      (show AEStronglyMeasurable
          (fun ω => canonicalLinearFactor1 s (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_canonicalLinearFactor1 s).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa [Real.norm_eq_abs, abs_of_pos hcpos] using hω.2.1
  · apply (integrable_const (c := (1 : ℝ))).mono'
      (show AEStronglyMeasurable
          (fun ω => canonicalQuadraticFactor0 s (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_canonicalQuadraticFactor0 s).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa only [Real.norm_eq_abs, norm_one] using hω.2.2.1
  · apply (integrable_const (c := c⁻¹)).mono'
      (show AEStronglyMeasurable
          (fun ω => canonicalQuadraticFactor1 s (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_canonicalQuadraticFactor1 s).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa [Real.norm_eq_abs, abs_of_pos hcpos] using hω.2.2.2.1
  · apply (integrable_const (c := (c ^ 2)⁻¹)).mono'
      (show AEStronglyMeasurable
          (fun ω => canonicalQuadraticFactor2 s (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_canonicalQuadraticFactor2 s).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa [Real.norm_eq_abs, abs_of_pos hcpos,
      abs_of_pos (sq_pos_of_pos hcpos)] using hω.2.2.2.2

/-- The centered-beta formula for the generic linear `P`-integrand. -/
theorem generalCanonicalLinear_beta_formula_of_hasLaw
    {ν : ℝ} (hν : 0 < ν)
    (s : ℝ) (P : Ω → ℝ) (Pmeasure : Measure Ω)
    (hP : HasLaw P (betaMeasure (ν / 2) (ν / 2)) Pmeasure) :
    (∫ ω, generalCanonicalLinearPIntegrand ν s (P ω) ∂Pmeasure)
      =
    centeredBetaKa (ν / 2) * ∫ x in (-1 : ℝ)..1,
      generalCanonicalLinearPIntegrand ν s ((1 + x) / 2)
        * (1 - x ^ 2) ^ (ν / 2 - 1) := by
  apply integral_comp_eq_centered_of_hasLaw_beta_same
    (a := ν / 2) (by positivity) P Pmeasure hP
  apply Measurable.aestronglyMeasurable
  unfold generalCanonicalLinearPIntegrand canonicalR canonicalDenom
    canonicalTheta weightPolynomial
  fun_prop

/-- The centered-beta formula for the generic quadratic `P`-integrand. -/
theorem generalCanonicalQuadratic_beta_formula_of_hasLaw
    {ν : ℝ} (hν : 0 < ν)
    (s : ℝ) (P : Ω → ℝ) (Pmeasure : Measure Ω)
    (hP : HasLaw P (betaMeasure (ν / 2) (ν / 2)) Pmeasure) :
    (∫ ω, generalCanonicalQuadraticPIntegrand ν s (P ω) ∂Pmeasure)
      =
    centeredBetaKa (ν / 2) * ∫ x in (-1 : ℝ)..1,
      generalCanonicalQuadraticPIntegrand ν s ((1 + x) / 2)
        * (1 - x ^ 2) ^ (ν / 2 - 1) := by
  apply integral_comp_eq_centered_of_hasLaw_beta_same
    (a := ν / 2) (by positivity) P Pmeasure hP
  apply Measurable.aestronglyMeasurable
  unfold generalCanonicalQuadraticPIntegrand canonicalR canonicalDenom
    canonicalTheta weightPolynomial
  fun_prop

/--
The general canonical moment bridge follows solely from its three component
laws and the two required independence statements.
-/
theorem generalCanonicalMomentBridge_of_component_laws
    (ν : ℕ) (hν : 9 ≤ ν)
    (s : ℝ) (P L V : Ω → ℝ) (Pmeasure : Measure Ω)
    (hs : |s| < 1)
    (hP :
      HasLaw P
        (betaMeasure ((ν : ℝ) / 2) ((ν : ℝ) / 2)) Pmeasure)
    (hL :
      HasLaw L
        (gammaMeasure (ν : ℝ) (1 / 2)) Pmeasure)
    (hV :
      HasLaw V
        (gammaMeasure (1 / 2) (1 / 2)) Pmeasure)
    (hP_LV :
      IndepFun P (fun ω => (L ω, V ω)) Pmeasure)
    (hVL : IndepFun V L Pmeasure) :
    GeneralCanonicalMomentBridge
      (centeredBetaKa ((ν : ℝ) / 2)) (ν : ℝ) s
        P L V Pmeasure := by
  have hνR : (9 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
  have hshape : 0 < (ν : ℝ) / 2 := by linarith
  exact generalCanonicalMomentBridge_of_gamma_product_laws
    (centeredBetaKa ((ν : ℝ) / 2)) (ν : ℝ) s
      P L V Pmeasure hνR hs hP_LV hVL hL hV
    (canonicalPFactorIntegrability13_of_beta_same_law
      hshape s P Pmeasure hs hP)
    (generalCanonicalLinear_beta_formula_of_hasLaw
      (show 0 < (ν : ℝ) by linarith)
      s P Pmeasure hP)
    (generalCanonicalQuadratic_beta_formula_of_hasLaw
      (show 0 < (ν : ℝ) by linarith)
      s P Pmeasure hP)

/--
Under the component laws, one positive perturbation coefficient has
strictly negative normalized risk difference for every interior variance
ratio `|s| < 1`.
-/
theorem exists_generalCanonicalRisk_epsilon_of_component_laws
    (ν : ℕ) (hν : 9 ≤ ν)
    (P L V : Ω → ℝ) (Pmeasure : Measure Ω)
    (hP :
      HasLaw P
        (betaMeasure ((ν : ℝ) / 2) ((ν : ℝ) / 2)) Pmeasure)
    (hL :
      HasLaw L
        (gammaMeasure (ν : ℝ) (1 / 2)) Pmeasure)
    (hV :
      HasLaw V
        (gammaMeasure (1 / 2) (1 / 2)) Pmeasure)
    (hP_LV :
      IndepFun P (fun ω => (L ω, V ω)) Pmeasure)
    (hVL : IndepFun V L Pmeasure) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℝ, |s| < 1 →
        generalCanonicalNormalizedRiskDifference
          ε (ν : ℝ) s P L V Pmeasure < 0 := by
  have hνR : (9 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
  have hshape : 0 < (ν : ℝ) / 2 := by linarith
  apply exists_generalCanonicalRisk_epsilon
    (centeredBetaKa ((ν : ℝ) / 2)) ν hν
      (centeredBetaKa_pos hshape) P L V Pmeasure
  intro s hs
  exact generalCanonicalMomentBridge_of_component_laws
    ν hν s P L V Pmeasure hs hP hL hV hP_LV hVL

end

end GraybillDeal
