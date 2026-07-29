import GraybillDeal.UnequalFixedDifferenceFourRealCanonicalProduct

/-!
# Real-parameter component-law bridge for the difference-four family

For every real `m ≥ 7`, the canonical residual summaries have laws

* `P ~ Beta(m-1,m+1)`;
* `L ~ Gamma(2m,1/2)`;
* `V ~ Gamma(1/2,1/2)`.

This module proves integrability of the five rational `P`-factors and
assembles those component laws with the real-parameter product-moment
reduction.

No argument in this bridge uses integrality of `m`: only positivity of the
real shapes `m-1`, `m+1`, and `2m` is required.
-/

namespace GraybillDeal

open MeasureTheory Set ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Beta support and canonical denominator bounds -/

/-- The real-family beta law is concentrated on `[0,1]`. -/
theorem betaMeasure_unequalFixedDifferenceFourReal_ae_mem_Icc
    (m : ℝ) :
    ∀ᵐ p : ℝ ∂betaMeasure (m - 1) (m + 1),
      p ∈ Icc (0 : ℝ) 1 := by
  unfold betaMeasure betaPDF
  rw [ae_withDensity_iff
    ((measurable_betaPDFReal (m - 1) (m + 1)).ennreal_ofReal)]
  filter_upwards [] with p hp
  have hp_pos : 0 < p := by
    by_contra h
    exact hp (betaPDF_eq_zero_of_nonpos (le_of_not_gt h))
  have hp_lt : p < 1 := by
    by_contra h
    exact hp (betaPDF_eq_zero_of_one_le (le_of_not_gt h))
  exact ⟨hp_pos.le, hp_lt.le⟩

/--
The real-family canonical denominator is bounded below by its smaller
positive endpoint coefficient.
-/
theorem unequalFixedDifferenceFourRealCanonicalDenom_lower
    {m : ℝ} (hm : 7 ≤ m)
    {θ p : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hp : p ∈ Icc (0 : ℝ) 1) :
    min
        (θ / unequalFixedDifferenceFourRealT m)
        ((1 - θ) / unequalFixedDifferenceFourRealQ m)
      ≤ unequalFixedDifferenceFourRealCanonicalDenom m θ p := by
  let α : ℝ := θ / unequalFixedDifferenceFourRealT m
  let β : ℝ := (1 - θ) / unequalFixedDifferenceFourRealQ m
  let c : ℝ := min α β
  have hp0 : 0 ≤ p := hp.1
  have h1p0 : 0 ≤ 1 - p := sub_nonneg.mpr hp.2
  have hcα : c ≤ α := min_le_left _ _
  have hcβ : c ≤ β := min_le_right _ _
  have hleft : c * p ≤ α * p :=
    mul_le_mul_of_nonneg_right hcα hp0
  have hright : c * (1 - p) ≤ β * (1 - p) :=
    mul_le_mul_of_nonneg_right hcβ h1p0
  change c ≤ unequalFixedDifferenceFourRealCanonicalDenom m θ p
  calc
    c = c * p + c * (1 - p) := by ring
    _ ≤ α * p + β * (1 - p) := add_le_add hleft hright
    _ = unequalFixedDifferenceFourRealCanonicalDenom m θ p := by
      simp only [α, β, unequalFixedDifferenceFourRealCanonicalDenom]

/-- The real-family endpoint minimum is strictly positive. -/
theorem unequalFixedDifferenceFourRealCanonicalEndpointMin_pos
    {m : ℝ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    0 <
      min
        (θ / unequalFixedDifferenceFourRealT m)
        ((1 - θ) / unequalFixedDifferenceFourRealQ m) := by
  rw [lt_min_iff]
  exact
    ⟨div_pos hθ0 (unequalFixedDifferenceFourRealT_pos hm),
      div_pos (sub_pos.mpr hθ1)
        (unequalFixedDifferenceFourRealQ_pos hm)⟩

/--
The real-family endpoint-damped direction has absolute value at most one on
the unit interval.
-/
theorem abs_unequalFixedDifferenceFourRealCanonicalPhi_le_one
    {m : ℝ} (hm : 7 ≤ m)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    |unequalDampedPhi
        (unequalFixedDifferenceFourRealT m)
        (unequalFixedDifferenceFourRealKappa m) r|
      ≤ 1 := by
  have hr_abs : |r| ≤ 1 := by
    rw [abs_of_nonneg hr.1]
    exact hr.2
  have hOneSub_abs : |1 - r| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hr.2)]
    linarith [hr.1]
  have hprod : |r * (1 - r)| ≤ 1 := by
    rw [abs_mul]
    calc
      |r| * |1 - r| ≤ 1 * 1 :=
        mul_le_mul hr_abs hOneSub_abs (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hinner :=
    abs_unequalFixedDifferenceFourRealInner_le_Q hm hr
  have hq1 := unequalFixedDifferenceFourRealQ_le_one hm
  unfold unequalDampedPhi
  rw [abs_mul]
  calc
    |r * (1 - r)|
          *
        |unequalDampedInner
          (unequalFixedDifferenceFourRealT m)
          (unequalFixedDifferenceFourRealKappa m) r|
        ≤ 1 * unequalFixedDifferenceFourRealQ m :=
      mul_le_mul hprod hinner (abs_nonneg _) (by norm_num)
    _ ≤ 1 := by simpa using hq1

/-! ## Integrability of the five canonical `P` factors -/

/--
All five real-family coefficient functions are integrable under the
canonical `Beta(m-1,m+1)` law of `P`.
-/
theorem
    unequalFixedDifferenceFourRealCanonicalPFactorIntegrability_of_beta_law
    {m : ℝ} (hm : 7 ≤ m)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (P : Ω → ℝ) (Pmeasure : Measure Ω)
    (hP :
      HasLaw P (betaMeasure (m - 1) (m + 1)) Pmeasure) :
    UnequalFixedDifferenceFourRealCanonicalPFactorIntegrability
      m θ P Pmeasure := by
  let c : ℝ :=
    min
      (θ / unequalFixedDifferenceFourRealT m)
      ((1 - θ) / unequalFixedDifferenceFourRealQ m)
  have hcpos : 0 < c :=
    unequalFixedDifferenceFourRealCanonicalEndpointMin_pos
      hm hθ0 hθ1
  letI : IsProbabilityMeasure (betaMeasure (m - 1) (m + 1)) :=
    isProbabilityMeasureBeta (by linarith) (by linarith)
  letI : IsProbabilityMeasure Pmeasure := hP.isProbabilityMeasure
  have hP_support :
      ∀ᵐ ω ∂Pmeasure, P ω ∈ Icc (0 : ℝ) 1 := by
    exact (hP.ae_iff measurableSet_Icc.mem).2
      (betaMeasure_unequalFixedDifferenceFourReal_ae_mem_Icc m)
  have hfactor_bounds :
      ∀ᵐ ω ∂Pmeasure,
        |unequalFixedDifferenceFourRealCanonicalLinearFactor0
            m θ (P ω)| ≤ 1
        ∧
        |unequalFixedDifferenceFourRealCanonicalLinearFactor1
            m θ (P ω)| ≤ c⁻¹
        ∧
        |unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
            m θ (P ω)| ≤ 1
        ∧
        |unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
            m θ (P ω)| ≤ c⁻¹
        ∧
        |unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
            m θ (P ω)| ≤ (c ^ 2)⁻¹ := by
    filter_upwards [hP_support] with ω hp
    have hr :=
      unequalFixedDifferenceFourRealCanonicalR_mem_Icc
        hm hθ0 hθ1 hp
    have hθ : θ ∈ Icc (0 : ℝ) 1 :=
      ⟨hθ0.le, hθ1.le⟩
    have hden_lower :
        c ≤ unequalFixedDifferenceFourRealCanonicalDenom m θ (P ω) :=
      unequalFixedDifferenceFourRealCanonicalDenom_lower
        hm hθ0 hθ1 hp
    have hdenpos :
        0 < unequalFixedDifferenceFourRealCanonicalDenom m θ (P ω) :=
      lt_of_lt_of_le hcpos hden_lower
    have hphi :
        |unequalDampedPhi
            (unequalFixedDifferenceFourRealT m)
            (unequalFixedDifferenceFourRealKappa m)
            (unequalFixedDifferenceFourRealCanonicalR m θ (P ω))|
          ≤ 1 :=
      abs_unequalFixedDifferenceFourRealCanonicalPhi_le_one hm hr
    have hrtheta :
        |unequalFixedDifferenceFourRealCanonicalR m θ (P ω) - θ|
          ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hr.1, hr.2, hθ.1, hθ.2]
    have hlinear0 :
        |unequalFixedDifferenceFourRealCanonicalLinearFactor0
            m θ (P ω)| ≤ 1 := by
      unfold unequalFixedDifferenceFourRealCanonicalLinearFactor0
      rw [abs_mul]
      calc
        |unequalFixedDifferenceFourRealCanonicalR m θ (P ω) - θ|
            *
          |unequalDampedPhi
            (unequalFixedDifferenceFourRealT m)
            (unequalFixedDifferenceFourRealKappa m)
            (unequalFixedDifferenceFourRealCanonicalR m θ (P ω))|
            ≤ 1 * 1 :=
          mul_le_mul hrtheta hphi (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hlinear1 :
        |unequalFixedDifferenceFourRealCanonicalLinearFactor1
            m θ (P ω)| ≤ c⁻¹ := by
      unfold unequalFixedDifferenceFourRealCanonicalLinearFactor1
      rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
      calc
        |unequalFixedDifferenceFourRealCanonicalLinearFactor0
            m θ (P ω)| ≤ 1 := hlinear0
        _ ≤
          c⁻¹ * unequalFixedDifferenceFourRealCanonicalDenom m θ (P ω) := by
            rw [inv_mul_eq_div, le_div_iff₀ hcpos]
            simpa only [one_mul] using hden_lower
    have hquadratic0 :
        |unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
            m θ (P ω)| ≤ 1 := by
      unfold unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
      rw [abs_sq]
      have hpows :=
        pow_le_pow_left₀ (abs_nonneg _) hphi 2
      simpa using hpows
    have hquadratic1 :
        |unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
            m θ (P ω)| ≤ c⁻¹ := by
      unfold unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
      rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
      calc
        |unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
            m θ (P ω)| ≤ 1 := hquadratic0
        _ ≤
          c⁻¹ * unequalFixedDifferenceFourRealCanonicalDenom m θ (P ω) := by
            rw [inv_mul_eq_div, le_div_iff₀ hcpos]
            simpa only [one_mul] using hden_lower
    have hden_sq_lower :
        c ^ 2
          ≤ unequalFixedDifferenceFourRealCanonicalDenom
              m θ (P ω) ^ 2 := by
      nlinarith
    have hden_sq_pos :
        0 <
          unequalFixedDifferenceFourRealCanonicalDenom m θ (P ω) ^ 2 :=
      sq_pos_of_pos hdenpos
    have hc_sq_pos : 0 < c ^ 2 := sq_pos_of_pos hcpos
    have hquadratic2 :
        |unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
            m θ (P ω)| ≤ (c ^ 2)⁻¹ := by
      unfold unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
      rw [abs_div, abs_of_pos hden_sq_pos, div_le_iff₀ hden_sq_pos]
      calc
        |unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
            m θ (P ω)| ≤ 1 := hquadratic0
        _ ≤
          (c ^ 2)⁻¹
            * unequalFixedDifferenceFourRealCanonicalDenom
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
            unequalFixedDifferenceFourRealCanonicalLinearFactor0
              m θ (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_unequalFixedDifferenceFourRealCanonicalLinearFactor0
              m θ).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa only [Real.norm_eq_abs, norm_one] using hω.1
  · apply (integrable_const (c := c⁻¹)).mono'
      (show AEStronglyMeasurable
          (fun ω =>
            unequalFixedDifferenceFourRealCanonicalLinearFactor1
              m θ (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_unequalFixedDifferenceFourRealCanonicalLinearFactor1
              m θ).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa [Real.norm_eq_abs, abs_of_pos hcpos] using hω.2.1
  · apply (integrable_const (c := (1 : ℝ))).mono'
      (show AEStronglyMeasurable
          (fun ω =>
            unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
              m θ (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_unequalFixedDifferenceFourRealCanonicalQuadraticFactor0
              m θ).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa only [Real.norm_eq_abs, norm_one] using hω.2.2.1
  · apply (integrable_const (c := c⁻¹)).mono'
      (show AEStronglyMeasurable
          (fun ω =>
            unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
              m θ (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_unequalFixedDifferenceFourRealCanonicalQuadraticFactor1
              m θ).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa [Real.norm_eq_abs, abs_of_pos hcpos] using hω.2.2.2.1
  · apply (integrable_const (c := (c ^ 2)⁻¹)).mono'
      (show AEStronglyMeasurable
          (fun ω =>
            unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
              m θ (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_unequalFixedDifferenceFourRealCanonicalQuadraticFactor2
              m θ).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa [Real.norm_eq_abs, abs_of_pos hcpos,
      abs_of_pos (sq_pos_of_pos hcpos)] using hω.2.2.2.2

/-! ## Expectation transport and the component-law bridge -/

/-- Transport the real canonical linear coefficient through the law of `P`. -/
theorem
    unequalFixedDifferenceFourRealCanonicalB_expectation_of_hasLaw
    {m : ℝ} (θ : ℝ) (P : Ω → ℝ) (Pmeasure : Measure Ω)
    (hP :
      HasLaw P (betaMeasure (m - 1) (m + 1)) Pmeasure) :
    (∫ ω,
      unequalFixedDifferenceFourRealCanonicalBIntegrand
        m θ (P ω) ∂Pmeasure)
      = unequalFixedDifferenceFourRealCanonicalB m θ := by
  calc
    (∫ ω,
      unequalFixedDifferenceFourRealCanonicalBIntegrand
        m θ (P ω) ∂Pmeasure)
        =
      ∫ p,
        unequalFixedDifferenceFourRealCanonicalBIntegrand m θ p
        ∂betaMeasure (m - 1) (m + 1) := by
          simpa only [Function.comp_def] using
            hP.integral_comp
              (Measurable.aestronglyMeasurable
                (measurable_unequalFixedDifferenceFourRealCanonicalBIntegrand
                  m θ))
    _ = unequalFixedDifferenceFourRealCanonicalB m θ := rfl

/-- Transport the real canonical quadratic coefficient through the law of `P`. -/
theorem
    unequalFixedDifferenceFourRealCanonicalC_expectation_of_hasLaw
    {m : ℝ} (θ : ℝ) (P : Ω → ℝ) (Pmeasure : Measure Ω)
    (hP :
      HasLaw P (betaMeasure (m - 1) (m + 1)) Pmeasure) :
    (∫ ω,
      unequalFixedDifferenceFourRealCanonicalCIntegrand
        m θ (P ω) ∂Pmeasure)
      = unequalFixedDifferenceFourRealCanonicalC m θ := by
  calc
    (∫ ω,
      unequalFixedDifferenceFourRealCanonicalCIntegrand
        m θ (P ω) ∂Pmeasure)
        =
      ∫ p,
        unequalFixedDifferenceFourRealCanonicalCIntegrand m θ p
        ∂betaMeasure (m - 1) (m + 1) := by
          simpa only [Function.comp_def] using
            hP.integral_comp
              (Measurable.aestronglyMeasurable
                (measurable_unequalFixedDifferenceFourRealCanonicalCIntegrand
                  m θ))
    _ = unequalFixedDifferenceFourRealCanonicalC m θ := rfl

/--
The real-family canonical two-moment bridge follows from the three component
laws and the two required independence statements.
-/
theorem
    unequalFixedDifferenceFourRealCanonicalMomentBridge_of_component_laws
    {m : ℝ} (hm : 7 ≤ m)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (P L V : Ω → ℝ) (Pmeasure : Measure Ω)
    (hP :
      HasLaw P (betaMeasure (m - 1) (m + 1)) Pmeasure)
    (hL :
      HasLaw L (gammaMeasure (2 * m) (1 / 2)) Pmeasure)
    (hV :
      HasLaw V (gammaMeasure (1 / 2) (1 / 2)) Pmeasure)
    (hP_LV : IndepFun P (fun ω => (L ω, V ω)) Pmeasure)
    (hVL : IndepFun V L Pmeasure) :
    UnequalDampedMomentBridge θ
      (unequalFixedDifferenceFourRealCanonicalB m θ)
      (unequalFixedDifferenceFourRealCanonicalC m θ)
      (fun ω =>
        unequalFixedDifferenceFourRealCanonicalR m θ (P ω))
      (fun ω =>
        unequalFixedDifferenceFourRealCanonicalH
          m θ (P ω) (L ω) (V ω))
      V Pmeasure := by
  exact
    unequalFixedDifferenceFourRealCanonicalMomentBridge_of_canonical_expectations
      hm θ P L V Pmeasure hP_LV hVL
      (generalCanonicalFiveMoments_of_gamma_laws
        (2 * m) (by linarith)
        L V Pmeasure hL hV)
      (unequalFixedDifferenceFourRealCanonicalPFactorIntegrability_of_beta_law
        hm hθ0 hθ1 P Pmeasure hP)
      (unequalFixedDifferenceFourRealCanonicalB_expectation_of_hasLaw
        θ P Pmeasure hP)
      (unequalFixedDifferenceFourRealCanonicalC_expectation_of_hasLaw
        θ P Pmeasure hP)

end

end GraybillDeal
