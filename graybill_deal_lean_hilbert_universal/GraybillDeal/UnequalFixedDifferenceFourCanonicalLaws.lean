import GraybillDeal.UnequalFixedDifferenceFourCanonicalProduct

/-!
# Component-law bridge for the fixed-difference-four family

For `m ≥ 7`, the canonical residual summaries have laws

* `P ~ Beta(m-1,m+1)`;
* `L ~ Gamma(2m,1/2)`;
* `V ~ Gamma(1/2,1/2)`.

This module proves integrability of the five rational `P`-factors and
assembles those component laws with the product-moment reduction.
-/

namespace GraybillDeal

open MeasureTheory Set ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem unequalFD4CanonicalLaws_cast_seven_le
    {m : ℕ} (hm : 7 ≤ m) :
    (7 : ℝ) ≤ (m : ℝ) := by
  exact_mod_cast hm

/-! ## Beta support and canonical denominator bounds -/

/-- The family beta law is concentrated on `[0,1]`. -/
theorem betaMeasure_unequalFixedDifferenceFour_ae_mem_Icc
    (m : ℕ) :
    ∀ᵐ p : ℝ
      ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1),
      p ∈ Icc (0 : ℝ) 1 := by
  unfold betaMeasure betaPDF
  rw [ae_withDensity_iff
    ((measurable_betaPDFReal
      ((m : ℝ) - 1) ((m : ℝ) + 1)).ennreal_ofReal)]
  filter_upwards [] with p hp
  have hp_pos : 0 < p := by
    by_contra h
    exact hp (betaPDF_eq_zero_of_nonpos (le_of_not_gt h))
  have hp_lt : p < 1 := by
    by_contra h
    exact hp (betaPDF_eq_zero_of_one_le (le_of_not_gt h))
  exact ⟨hp_pos.le, hp_lt.le⟩

/--
The family canonical denominator is bounded below by its smaller positive
endpoint coefficient.
-/
theorem unequalFixedDifferenceFourCanonicalDenom_lower
    {m : ℕ} (hm : 7 ≤ m)
    {θ p : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hp : p ∈ Icc (0 : ℝ) 1) :
    min
        (θ / unequalFixedDifferenceFourT m)
        ((1 - θ) / unequalFixedDifferenceFourQ m)
      ≤ unequalFixedDifferenceFourCanonicalDenom m θ p := by
  let α : ℝ := θ / unequalFixedDifferenceFourT m
  let β : ℝ := (1 - θ) / unequalFixedDifferenceFourQ m
  let c : ℝ := min α β
  have hp0 : 0 ≤ p := hp.1
  have h1p0 : 0 ≤ 1 - p := sub_nonneg.mpr hp.2
  have hcα : c ≤ α := min_le_left _ _
  have hcβ : c ≤ β := min_le_right _ _
  have hleft : c * p ≤ α * p :=
    mul_le_mul_of_nonneg_right hcα hp0
  have hright : c * (1 - p) ≤ β * (1 - p) :=
    mul_le_mul_of_nonneg_right hcβ h1p0
  change c ≤ unequalFixedDifferenceFourCanonicalDenom m θ p
  calc
    c = c * p + c * (1 - p) := by ring
    _ ≤ α * p + β * (1 - p) := add_le_add hleft hright
    _ = unequalFixedDifferenceFourCanonicalDenom m θ p := by
      simp only [α, β, unequalFixedDifferenceFourCanonicalDenom]

/-- The endpoint minimum is strictly positive for interior oracle weights. -/
theorem unequalFixedDifferenceFourCanonicalEndpointMin_pos
    {m : ℕ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    0 <
      min
        (θ / unequalFixedDifferenceFourT m)
        ((1 - θ) / unequalFixedDifferenceFourQ m) := by
  rw [lt_min_iff]
  exact
    ⟨div_pos hθ0 (unequalFixedDifferenceFourT_pos hm),
      div_pos (sub_pos.mpr hθ1)
        (unequalFixedDifferenceFourQ_pos hm)⟩

/--
The family endpoint-damped direction has absolute value at most one on
the unit interval.
-/
theorem abs_unequalFixedDifferenceFourCanonicalPhi_le_one
    {m : ℕ} (hm : 7 ≤ m)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    |unequalDampedPhi
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourKappa m) r|
      ≤ 1 := by
  have hr_abs : |r| ≤ 1 := by
    rw [abs_of_nonneg hr.1]
    exact hr.2
  have hOneSub_abs : |1 - r| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hr.2)]
    linarith [hr.1]
  have hprod :
      |r * (1 - r)| ≤ 1 := by
    rw [abs_mul]
    calc
      |r| * |1 - r| ≤ 1 * 1 :=
        mul_le_mul hr_abs hOneSub_abs (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hinner :=
    abs_unequalFixedDifferenceFourInner_le_Q hm hr
  have hq1 := unequalFixedDifferenceFourQ_le_one hm
  unfold unequalDampedPhi
  rw [abs_mul]
  calc
    |r * (1 - r)|
          *
        |unequalDampedInner
          (unequalFixedDifferenceFourT m)
          (unequalFixedDifferenceFourKappa m) r|
        ≤ 1 * unequalFixedDifferenceFourQ m :=
      mul_le_mul hprod hinner (abs_nonneg _)
        (by norm_num)
    _ ≤ 1 := by simpa using hq1

/-! ## Integrability of the five canonical `P` factors -/

/--
All five family coefficient functions are integrable under the canonical
`Beta(m-1,m+1)` law of `P`.
-/
theorem
    unequalFixedDifferenceFourCanonicalPFactorIntegrability_of_beta_law
    {m : ℕ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (P : Ω → ℝ) (Pmeasure : Measure Ω)
    (hP :
      HasLaw P
        (betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
        Pmeasure) :
    UnequalFixedDifferenceFourCanonicalPFactorIntegrability
      m θ P Pmeasure := by
  let c : ℝ :=
    min
      (θ / unequalFixedDifferenceFourT m)
      ((1 - θ) / unequalFixedDifferenceFourQ m)
  have hcpos : 0 < c :=
    unequalFixedDifferenceFourCanonicalEndpointMin_pos
      hm hθ0 hθ1
  have hmR := unequalFD4CanonicalLaws_cast_seven_le hm
  letI :
      IsProbabilityMeasure
        (betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1)) :=
    isProbabilityMeasureBeta (by linarith) (by linarith)
  letI : IsProbabilityMeasure Pmeasure := hP.isProbabilityMeasure
  have hP_support :
      ∀ᵐ ω ∂Pmeasure, P ω ∈ Icc (0 : ℝ) 1 := by
    exact (hP.ae_iff measurableSet_Icc.mem).2
      (betaMeasure_unequalFixedDifferenceFour_ae_mem_Icc m)
  have hfactor_bounds :
      ∀ᵐ ω ∂Pmeasure,
        |unequalFixedDifferenceFourCanonicalLinearFactor0
            m θ (P ω)| ≤ 1
        ∧
        |unequalFixedDifferenceFourCanonicalLinearFactor1
            m θ (P ω)| ≤ c⁻¹
        ∧
        |unequalFixedDifferenceFourCanonicalQuadraticFactor0
            m θ (P ω)| ≤ 1
        ∧
        |unequalFixedDifferenceFourCanonicalQuadraticFactor1
            m θ (P ω)| ≤ c⁻¹
        ∧
        |unequalFixedDifferenceFourCanonicalQuadraticFactor2
            m θ (P ω)| ≤ (c ^ 2)⁻¹ := by
    filter_upwards [hP_support] with ω hp
    have hr :=
      unequalFixedDifferenceFourCanonicalR_mem_Icc
        hm hθ0 hθ1 hp
    have hθ : θ ∈ Icc (0 : ℝ) 1 :=
      ⟨hθ0.le, hθ1.le⟩
    have hden_lower :
        c ≤ unequalFixedDifferenceFourCanonicalDenom m θ (P ω) :=
      unequalFixedDifferenceFourCanonicalDenom_lower
        hm hθ0 hθ1 hp
    have hdenpos :
        0 < unequalFixedDifferenceFourCanonicalDenom m θ (P ω) :=
      lt_of_lt_of_le hcpos hden_lower
    have hphi :
        |unequalDampedPhi
            (unequalFixedDifferenceFourT m)
            (unequalFixedDifferenceFourKappa m)
            (unequalFixedDifferenceFourCanonicalR m θ (P ω))|
          ≤ 1 :=
      abs_unequalFixedDifferenceFourCanonicalPhi_le_one hm hr
    have hrtheta :
        |unequalFixedDifferenceFourCanonicalR m θ (P ω) - θ|
          ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hr.1, hr.2, hθ.1, hθ.2]
    have hlinear0 :
        |unequalFixedDifferenceFourCanonicalLinearFactor0
            m θ (P ω)| ≤ 1 := by
      unfold unequalFixedDifferenceFourCanonicalLinearFactor0
      rw [abs_mul]
      calc
        |unequalFixedDifferenceFourCanonicalR m θ (P ω) - θ|
            *
          |unequalDampedPhi
            (unequalFixedDifferenceFourT m)
            (unequalFixedDifferenceFourKappa m)
            (unequalFixedDifferenceFourCanonicalR m θ (P ω))|
            ≤ 1 * 1 :=
          mul_le_mul hrtheta hphi (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hlinear1 :
        |unequalFixedDifferenceFourCanonicalLinearFactor1
            m θ (P ω)| ≤ c⁻¹ := by
      unfold unequalFixedDifferenceFourCanonicalLinearFactor1
      rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
      calc
        |unequalFixedDifferenceFourCanonicalLinearFactor0
            m θ (P ω)| ≤ 1 := hlinear0
        _ ≤
          c⁻¹ * unequalFixedDifferenceFourCanonicalDenom m θ (P ω) := by
            rw [inv_mul_eq_div, le_div_iff₀ hcpos]
            simpa only [one_mul] using hden_lower
    have hquadratic0 :
        |unequalFixedDifferenceFourCanonicalQuadraticFactor0
            m θ (P ω)| ≤ 1 := by
      unfold unequalFixedDifferenceFourCanonicalQuadraticFactor0
      rw [abs_sq]
      have hpows :=
        pow_le_pow_left₀ (abs_nonneg _) hphi 2
      simpa using hpows
    have hquadratic1 :
        |unequalFixedDifferenceFourCanonicalQuadraticFactor1
            m θ (P ω)| ≤ c⁻¹ := by
      unfold unequalFixedDifferenceFourCanonicalQuadraticFactor1
      rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
      calc
        |unequalFixedDifferenceFourCanonicalQuadraticFactor0
            m θ (P ω)| ≤ 1 := hquadratic0
        _ ≤
          c⁻¹ * unequalFixedDifferenceFourCanonicalDenom m θ (P ω) := by
            rw [inv_mul_eq_div, le_div_iff₀ hcpos]
            simpa only [one_mul] using hden_lower
    have hden_sq_lower :
        c ^ 2
          ≤ unequalFixedDifferenceFourCanonicalDenom
              m θ (P ω) ^ 2 := by
      nlinarith
    have hden_sq_pos :
        0 <
          unequalFixedDifferenceFourCanonicalDenom m θ (P ω) ^ 2 :=
      sq_pos_of_pos hdenpos
    have hc_sq_pos : 0 < c ^ 2 := sq_pos_of_pos hcpos
    have hquadratic2 :
        |unequalFixedDifferenceFourCanonicalQuadraticFactor2
            m θ (P ω)| ≤ (c ^ 2)⁻¹ := by
      unfold unequalFixedDifferenceFourCanonicalQuadraticFactor2
      rw [abs_div, abs_of_pos hden_sq_pos,
        div_le_iff₀ hden_sq_pos]
      calc
        |unequalFixedDifferenceFourCanonicalQuadraticFactor0
            m θ (P ω)| ≤ 1 := hquadratic0
        _ ≤
          (c ^ 2)⁻¹
            * unequalFixedDifferenceFourCanonicalDenom
                m θ (P ω) ^ 2 := by
              rw [inv_mul_eq_div, le_div_iff₀ hc_sq_pos]
              simpa only [one_mul] using hden_sq_lower
    exact
      ⟨hlinear0, hlinear1, hquadratic0,
        hquadratic1, hquadratic2⟩
  refine
    { linear0 := ?_
      linear1 := ?_
      quadratic0 := ?_
      quadratic1 := ?_
      quadratic2 := ?_ }
  · apply (integrable_const (c := (1 : ℝ))).mono'
      (show AEStronglyMeasurable
          (fun ω =>
            unequalFixedDifferenceFourCanonicalLinearFactor0
              m θ (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_unequalFixedDifferenceFourCanonicalLinearFactor0
              m θ).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa only [Real.norm_eq_abs, norm_one] using hω.1
  · apply (integrable_const (c := c⁻¹)).mono'
      (show AEStronglyMeasurable
          (fun ω =>
            unequalFixedDifferenceFourCanonicalLinearFactor1
              m θ (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_unequalFixedDifferenceFourCanonicalLinearFactor1
              m θ).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa [Real.norm_eq_abs, abs_of_pos hcpos] using hω.2.1
  · apply (integrable_const (c := (1 : ℝ))).mono'
      (show AEStronglyMeasurable
          (fun ω =>
            unequalFixedDifferenceFourCanonicalQuadraticFactor0
              m θ (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_unequalFixedDifferenceFourCanonicalQuadraticFactor0
              m θ).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa only [Real.norm_eq_abs, norm_one] using hω.2.2.1
  · apply (integrable_const (c := c⁻¹)).mono'
      (show AEStronglyMeasurable
          (fun ω =>
            unequalFixedDifferenceFourCanonicalQuadraticFactor1
              m θ (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_unequalFixedDifferenceFourCanonicalQuadraticFactor1
              m θ).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa [Real.norm_eq_abs, abs_of_pos hcpos] using hω.2.2.2.1
  · apply (integrable_const (c := (c ^ 2)⁻¹)).mono'
      (show AEStronglyMeasurable
          (fun ω =>
            unequalFixedDifferenceFourCanonicalQuadraticFactor2
              m θ (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_unequalFixedDifferenceFourCanonicalQuadraticFactor2
              m θ).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa [Real.norm_eq_abs, abs_of_pos hcpos,
      abs_of_pos (sq_pos_of_pos hcpos)] using hω.2.2.2.2

/-! ## Expectation transport and the component-law bridge -/

/-- Transport the canonical linear coefficient through the law of `P`. -/
theorem
    unequalFixedDifferenceFourCanonicalB_expectation_of_hasLaw
    {m : ℕ} (θ : ℝ) (P : Ω → ℝ) (Pmeasure : Measure Ω)
    (hP :
      HasLaw P
        (betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
        Pmeasure) :
    (∫ ω,
      unequalFixedDifferenceFourCanonicalBIntegrand
        m θ (P ω) ∂Pmeasure)
      = unequalFixedDifferenceFourCanonicalB m θ := by
  calc
    (∫ ω,
      unequalFixedDifferenceFourCanonicalBIntegrand
        m θ (P ω) ∂Pmeasure)
        =
      ∫ p,
        unequalFixedDifferenceFourCanonicalBIntegrand m θ p
        ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1) := by
          simpa only [Function.comp_def] using
            hP.integral_comp
              (Measurable.aestronglyMeasurable
                (measurable_unequalFixedDifferenceFourCanonicalBIntegrand
                  m θ))
    _ = unequalFixedDifferenceFourCanonicalB m θ := rfl

/-- Transport the canonical quadratic coefficient through the law of `P`. -/
theorem
    unequalFixedDifferenceFourCanonicalC_expectation_of_hasLaw
    {m : ℕ} (θ : ℝ) (P : Ω → ℝ) (Pmeasure : Measure Ω)
    (hP :
      HasLaw P
        (betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
        Pmeasure) :
    (∫ ω,
      unequalFixedDifferenceFourCanonicalCIntegrand
        m θ (P ω) ∂Pmeasure)
      = unequalFixedDifferenceFourCanonicalC m θ := by
  calc
    (∫ ω,
      unequalFixedDifferenceFourCanonicalCIntegrand
        m θ (P ω) ∂Pmeasure)
        =
      ∫ p,
        unequalFixedDifferenceFourCanonicalCIntegrand m θ p
        ∂betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1) := by
          simpa only [Function.comp_def] using
            hP.integral_comp
              (Measurable.aestronglyMeasurable
                (measurable_unequalFixedDifferenceFourCanonicalCIntegrand
                  m θ))
    _ = unequalFixedDifferenceFourCanonicalC m θ := rfl

/--
The family canonical two-moment bridge follows from the three component
laws and the two required independence statements.
-/
theorem
    unequalFixedDifferenceFourCanonicalMomentBridge_of_component_laws
    {m : ℕ} (hm : 7 ≤ m)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (P L V : Ω → ℝ) (Pmeasure : Measure Ω)
    (hP :
      HasLaw P
        (betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
        Pmeasure)
    (hL :
      HasLaw L
        (gammaMeasure (2 * (m : ℝ)) (1 / 2))
        Pmeasure)
    (hV :
      HasLaw V
        (gammaMeasure (1 / 2) (1 / 2))
        Pmeasure)
    (hP_LV : IndepFun P (fun ω => (L ω, V ω)) Pmeasure)
    (hVL : IndepFun V L Pmeasure) :
    UnequalDampedMomentBridge θ
      (unequalFixedDifferenceFourCanonicalB m θ)
      (unequalFixedDifferenceFourCanonicalC m θ)
      (fun ω =>
        unequalFixedDifferenceFourCanonicalR m θ (P ω))
      (fun ω =>
        unequalFixedDifferenceFourCanonicalH
          m θ (P ω) (L ω) (V ω))
      V Pmeasure := by
  have hmR := unequalFD4CanonicalLaws_cast_seven_le hm
  exact
    unequalFixedDifferenceFourCanonicalMomentBridge_of_canonical_expectations
      hm θ P L V Pmeasure hP_LV hVL
      (generalCanonicalFiveMoments_of_gamma_laws
        (2 * (m : ℝ)) (by linarith)
        L V Pmeasure hL hV)
      (unequalFixedDifferenceFourCanonicalPFactorIntegrability_of_beta_law
        hm hθ0 hθ1 P Pmeasure hP)
      (unequalFixedDifferenceFourCanonicalB_expectation_of_hasLaw
        θ P Pmeasure hP)
      (unequalFixedDifferenceFourCanonicalC_expectation_of_hasLaw
        θ P Pmeasure hP)

end

end GraybillDeal
