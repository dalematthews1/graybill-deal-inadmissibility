import GraybillDeal.BetaBridge
import GraybillDeal.CanonicalProduct

/-!
# The canonical probability-law bridge

This file closes the gap between the component laws and
`CanonicalMomentBridge13`.

The only probabilistic inputs of the main theorem are:

* `P ~ Beta(6,6)`;
* `L ~ Gamma(12,1/2)`;
* `V ~ Gamma(1/2,1/2)`;
* `P` is independent of `(L,V)`, and `V` is independent of `L`.

The beta law supplies both the centered integration formula and the
integrability of the five rational `P`-factors.  The gamma laws supply all
five scalar moments.  Thus no expectation or integrability identity remains
as a hypothesis of the canonical moment bridge.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/--
On the beta support, the canonical denominator is uniformly separated from
zero by `(1-|s|)/2`.
-/
theorem canonicalDenom_lower_of_mem_Icc
    {s pcoord : ℝ} (hs : |s| < 1) (hp : pcoord ∈ Icc (0 : ℝ) 1) :
    (1 - |s|) / 2 ≤ canonicalDenom s pcoord := by
  have htheta := canonicalTheta_mem_Icc hs
  have htheta_lower :
      (1 - |s|) / 2 ≤ canonicalTheta s := by
    unfold canonicalTheta
    linarith [neg_abs_le s]
  have hone_theta_lower :
      (1 - |s|) / 2 ≤ 1 - canonicalTheta s := by
    unfold canonicalTheta
    linarith [le_abs_self s]
  calc
    (1 - |s|) / 2
        =
      (1 - |s|) / 2 * pcoord
        + (1 - |s|) / 2 * (1 - pcoord) := by ring
    _ ≤
      canonicalTheta s * pcoord
        + (1 - canonicalTheta s) * (1 - pcoord) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right htheta_lower hp.1)
            (mul_le_mul_of_nonneg_right hone_theta_lower (by linarith [hp.2]))
    _ = canonicalDenom s pcoord := rfl

/-- The canonical Graybill--Deal weight lies in `[0,1]` on the beta support. -/
theorem canonicalR_mem_Icc_of_mem_Icc
    {s pcoord : ℝ} (hs : |s| < 1) (hp : pcoord ∈ Icc (0 : ℝ) 1) :
    canonicalR s pcoord ∈ Icc (0 : ℝ) 1 := by
  have htheta := canonicalTheta_mem_Icc hs
  have hcpos : 0 < (1 - |s|) / 2 := by linarith
  have hdenpos : 0 < canonicalDenom s pcoord :=
    lt_of_lt_of_le hcpos (canonicalDenom_lower_of_mem_Icc hs hp)
  have hnum : 0 ≤ canonicalTheta s * pcoord :=
    mul_nonneg htheta.1 hp.1
  have hrest :
      0 ≤ (1 - canonicalTheta s) * (1 - pcoord) :=
    mul_nonneg (by linarith [htheta.2]) (by linarith [hp.2])
  unfold canonicalR
  constructor
  · exact div_nonneg hnum hdenpos.le
  · rw [div_le_one hdenpos]
    unfold canonicalDenom
    linarith

/-- A coarse uniform bound sufficient for all subsequent integrability proofs. -/
theorem abs_weightPolynomial_le_one
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    |weightPolynomial r| ≤ 1 := by
  have hr_abs : |r| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hr.1, hr.2]
  have hOneSub_abs : |1 - r| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hr.1, hr.2]
  have hTwo_abs : |1 - 2 * r| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hr.1, hr.2]
  unfold weightPolynomial
  rw [abs_mul, abs_mul]
  calc
    |r| * |1 - r| * |1 - 2 * r|
        ≤ 1 * 1 * 1 := by
          exact mul_le_mul
            (mul_le_mul hr_abs hOneSub_abs (abs_nonneg _) (by norm_num))
            hTwo_abs (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- The `Beta(6,6)` measure is concentrated on `[0,1]`. -/
theorem betaMeasure_six_six_ae_mem_Icc :
    ∀ᵐ p : ℝ ∂ProbabilityTheory.betaMeasure 6 6,
      p ∈ Icc (0 : ℝ) 1 := by
  unfold ProbabilityTheory.betaMeasure ProbabilityTheory.betaPDF
  rw [ae_withDensity_iff
    ((ProbabilityTheory.measurable_betaPDFReal 6 6).ennreal_ofReal)]
  filter_upwards [] with p hp
  have hp_pos : 0 < p := by
    by_contra h
    exact hp (ProbabilityTheory.betaPDF_eq_zero_of_nonpos (le_of_not_gt h))
  have hp_lt : p < 1 := by
    by_contra h
    exact hp (ProbabilityTheory.betaPDF_eq_zero_of_one_le (le_of_not_gt h))
  exact ⟨hp_pos.le, hp_lt.le⟩

/--
All five coefficient functions of `P` used in the product reduction are
automatically integrable under the `Beta(6,6)` law.
-/
theorem canonicalPFactorIntegrability13_of_beta_law
    (s : ℝ) (P : Ω → ℝ) (Pmeasure : Measure Ω)
    (hs : |s| < 1)
    (hP :
      ProbabilityTheory.HasLaw P
        (ProbabilityTheory.betaMeasure 6 6) Pmeasure) :
    CanonicalPFactorIntegrability13 s P Pmeasure := by
  let c : ℝ := (1 - |s|) / 2
  have hcpos : 0 < c := by
    dsimp only [c]
    linarith
  letI : IsProbabilityMeasure
      (ProbabilityTheory.betaMeasure 6 6) :=
    ProbabilityTheory.isProbabilityMeasureBeta (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure Pmeasure := hP.isProbabilityMeasure
  have hP_support :
      ∀ᵐ ω ∂Pmeasure, P ω ∈ Icc (0 : ℝ) 1 := by
    exact (hP.ae_iff measurableSet_Icc.mem).2
      betaMeasure_six_six_ae_mem_Icc
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
    exact ⟨hlinear0, hlinear1, hquadratic0, hquadratic1, hquadratic2⟩
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

/--
The probability-law bridge needed by the counterexample.

No moment, integral, or integrability identity appears among the hypotheses:
they are all derived from the three laws and the two independence statements.
-/
theorem canonicalMomentBridge13_of_component_laws
    (s : ℝ) (P L V : Ω → ℝ) (Pmeasure : Measure Ω)
    (hs : |s| < 1)
    (hP :
      ProbabilityTheory.HasLaw P
        (ProbabilityTheory.betaMeasure 6 6) Pmeasure)
    (hL :
      ProbabilityTheory.HasLaw L
        (ProbabilityTheory.gammaMeasure 12 (1 / 2)) Pmeasure)
    (hV :
      ProbabilityTheory.HasLaw V
        (ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) Pmeasure)
    (hP_LV :
      ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) Pmeasure)
    (hVL : ProbabilityTheory.IndepFun V L Pmeasure) :
    CanonicalMomentBridge13 canonicalKa13 s P L V Pmeasure := by
  exact canonicalMomentBridge13_of_gamma_product_laws
    canonicalKa13 s P L V Pmeasure hs hP_LV hVL hL hV
    (canonicalPFactorIntegrability13_of_beta_law
      s P Pmeasure hs hP)
    (canonicalLinear_beta_formula_of_hasLaw s P Pmeasure hP)
    (canonicalQuadratic_beta_formula_of_hasLaw s P Pmeasure hP)

/--
Consequently, the un-clipped canonical competitor has strictly negative
normalized risk difference under the component laws themselves.
-/
theorem canonicalNormalizedRiskDifference13_neg_of_component_laws
    (s : ℝ) (P L V : Ω → ℝ) (Pmeasure : Measure Ω)
    (hs : |s| < 1)
    (hP :
      ProbabilityTheory.HasLaw P
        (ProbabilityTheory.betaMeasure 6 6) Pmeasure)
    (hL :
      ProbabilityTheory.HasLaw L
        (ProbabilityTheory.gammaMeasure 12 (1 / 2)) Pmeasure)
    (hV :
      ProbabilityTheory.HasLaw V
        (ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) Pmeasure)
    (hP_LV :
      ProbabilityTheory.IndepFun P (fun ω => (L ω, V ω)) Pmeasure)
    (hVL : ProbabilityTheory.IndepFun V L Pmeasure) :
    canonicalNormalizedRiskDifference13
      epsilon13 s P L V Pmeasure < 0 := by
  exact canonicalNormalizedRiskDifference13_neg
    canonicalKa13 s P L V Pmeasure canonicalKa13_pos hs
    (canonicalMomentBridge13_of_component_laws
      s P L V Pmeasure hs hP hL hV hP_LV hVL)

end

end GraybillDeal
