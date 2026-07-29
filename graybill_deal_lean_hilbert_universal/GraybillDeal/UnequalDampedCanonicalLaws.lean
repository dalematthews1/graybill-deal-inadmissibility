import GraybillDeal.UnequalDampedCanonicalProduct

/-!
# Beta-law integrability for the fixed unequal canonical factors

For an interior oracle weight `0 < θ < 1`, the normalized denominator

`(7θ/3) p + (7(1-θ)/4) (1-p)`

is bounded below on `p ∈ [0,1]` by the positive minimum of its two endpoint
values.  Together with the elementary bound on the damped direction, this
makes all five rational `P`-factors in the product-moment reduction bounded
and hence integrable under `Beta(6,8)`.
-/

namespace GraybillDeal

open MeasureTheory Set ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Every unequal beta measure is concentrated on `[0,1]`. -/
theorem betaMeasure_unequal_ae_mem_Icc (a b : ℝ) :
    ∀ᵐ p : ℝ ∂betaMeasure a b, p ∈ Icc (0 : ℝ) 1 := by
  unfold betaMeasure betaPDF
  rw [ae_withDensity_iff
    ((measurable_betaPDFReal a b).ennreal_ofReal)]
  filter_upwards [] with p hp
  have hp_pos : 0 < p := by
    by_contra h
    exact hp (betaPDF_eq_zero_of_nonpos (le_of_not_gt h))
  have hp_lt : p < 1 := by
    by_contra h
    exact hp (betaPDF_eq_zero_of_one_le (le_of_not_gt h))
  exact ⟨hp_pos.le, hp_lt.le⟩

/--
The direct unequal denominator is bounded below by the smaller of its two
positive endpoint values.
-/
theorem unequalDampedCanonicalDenom13_17_lower
    {θ p : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hp : p ∈ Icc (0 : ℝ) 1) :
    min (7 * θ / 3) (7 * (1 - θ) / 4)
      ≤ unequalDampedCanonicalDenom13_17 θ p := by
  let α : ℝ := 7 * θ / 3
  let β : ℝ := 7 * (1 - θ) / 4
  let c : ℝ := min α β
  have hp0 : 0 ≤ p := hp.1
  have h1p0 : 0 ≤ 1 - p := sub_nonneg.mpr hp.2
  have hcα : c ≤ α := min_le_left _ _
  have hcβ : c ≤ β := min_le_right _ _
  have hleft : c * p ≤ α * p :=
    mul_le_mul_of_nonneg_right hcα hp0
  have hright : c * (1 - p) ≤ β * (1 - p) :=
    mul_le_mul_of_nonneg_right hcβ h1p0
  change c ≤ unequalDampedCanonicalDenom13_17 θ p
  calc
    c = c * p + c * (1 - p) := by ring
    _ ≤ α * p + β * (1 - p) := add_le_add hleft hright
    _ = unequalDampedCanonicalDenom13_17 θ p := by
      simp only [α, β, unequalDampedCanonicalDenom13_17]

/-- The endpoint minimum used above is strictly positive in the interior. -/
theorem unequalDampedCanonicalEndpointMin_pos
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    0 < min (7 * θ / 3) (7 * (1 - θ) / 4) := by
  rw [lt_min_iff]
  constructor <;> positivity

/--
The fixed damped direction has absolute value at most one on `[0,1]`.
The deliberately loose constant one keeps the later integrability bounds
simple.
-/
theorem abs_unequalDampedPhi13_17_le_one
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    |unequalDampedPhi13_17 r| ≤ 1 := by
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
  have hinner := abs_unequalDampedInner13_17_le hr
  unfold unequalDampedPhi13_17
  rw [abs_mul]
  calc
    |r * (1 - r)|
          * |3 / 7 - r + unequalDampedKappa13_17 * r * (1 - r)|
        ≤ 1 * (4 / 7) :=
      mul_le_mul hprod hinner (abs_nonneg _) (by norm_num)
    _ ≤ 1 := by norm_num

/--
All five coefficient functions in the unequal product reduction are
integrable under the required `Beta(6,8)` law.
-/
theorem unequalDampedCanonicalPFactorIntegrability13_17_of_beta_law
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (P : Ω → ℝ) (Pmeasure : Measure Ω)
    (hP : HasLaw P (betaMeasure 6 8) Pmeasure) :
    UnequalDampedCanonicalPFactorIntegrability13_17
      θ P Pmeasure := by
  let c : ℝ := min (7 * θ / 3) (7 * (1 - θ) / 4)
  have hcpos : 0 < c :=
    unequalDampedCanonicalEndpointMin_pos hθ0 hθ1
  letI : IsProbabilityMeasure (betaMeasure 6 8) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure Pmeasure := hP.isProbabilityMeasure
  have hP_support :
      ∀ᵐ ω ∂Pmeasure, P ω ∈ Icc (0 : ℝ) 1 := by
    exact (hP.ae_iff measurableSet_Icc.mem).2
      (betaMeasure_unequal_ae_mem_Icc 6 8)
  have hfactor_bounds :
      ∀ᵐ ω ∂Pmeasure,
        |unequalDampedCanonicalLinearFactor0 θ (P ω)| ≤ 1
        ∧
        |unequalDampedCanonicalLinearFactor1 θ (P ω)| ≤ c⁻¹
        ∧
        |unequalDampedCanonicalQuadraticFactor0 θ (P ω)| ≤ 1
        ∧
        |unequalDampedCanonicalQuadraticFactor1 θ (P ω)| ≤ c⁻¹
        ∧
        |unequalDampedCanonicalQuadraticFactor2 θ (P ω)|
          ≤ (c ^ 2)⁻¹ := by
    filter_upwards [hP_support] with ω hp
    have hr :=
      unequalDampedCanonicalR13_17_mem_Icc hθ0 hθ1 hp
    have hθ : θ ∈ Icc (0 : ℝ) 1 := ⟨hθ0.le, hθ1.le⟩
    have hden_lower :
        c ≤ unequalDampedCanonicalDenom13_17 θ (P ω) := by
      exact unequalDampedCanonicalDenom13_17_lower hθ0 hθ1 hp
    have hdenpos :
        0 < unequalDampedCanonicalDenom13_17 θ (P ω) :=
      lt_of_lt_of_le hcpos hden_lower
    have hphi :
        |unequalDampedPhi13_17
            (unequalDampedCanonicalR13_17 θ (P ω))| ≤ 1 :=
      abs_unequalDampedPhi13_17_le_one hr
    have hrtheta :
        |unequalDampedCanonicalR13_17 θ (P ω) - θ| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hr.1, hr.2, hθ.1, hθ.2]
    have hlinear0 :
        |unequalDampedCanonicalLinearFactor0 θ (P ω)| ≤ 1 := by
      unfold unequalDampedCanonicalLinearFactor0
      rw [abs_mul]
      calc
        |unequalDampedCanonicalR13_17 θ (P ω) - θ|
              * |unequalDampedPhi13_17
                  (unequalDampedCanonicalR13_17 θ (P ω))|
            ≤ 1 * 1 :=
          mul_le_mul hrtheta hphi (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hlinear1 :
        |unequalDampedCanonicalLinearFactor1 θ (P ω)| ≤ c⁻¹ := by
      unfold unequalDampedCanonicalLinearFactor1
      rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
      calc
        |unequalDampedCanonicalLinearFactor0 θ (P ω)| ≤ 1 :=
          hlinear0
        _ ≤ c⁻¹ * unequalDampedCanonicalDenom13_17 θ (P ω) := by
          rw [inv_mul_eq_div, le_div_iff₀ hcpos]
          simpa only [one_mul] using hden_lower
    have hquadratic0 :
        |unequalDampedCanonicalQuadraticFactor0 θ (P ω)| ≤ 1 := by
      unfold unequalDampedCanonicalQuadraticFactor0
      rw [abs_sq]
      have hpows :=
        pow_le_pow_left₀ (abs_nonneg _)
          hphi 2
      simpa using hpows
    have hquadratic1 :
        |unequalDampedCanonicalQuadraticFactor1 θ (P ω)| ≤ c⁻¹ := by
      unfold unequalDampedCanonicalQuadraticFactor1
      rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
      calc
        |unequalDampedCanonicalQuadraticFactor0 θ (P ω)| ≤ 1 :=
          hquadratic0
        _ ≤ c⁻¹ * unequalDampedCanonicalDenom13_17 θ (P ω) := by
          rw [inv_mul_eq_div, le_div_iff₀ hcpos]
          simpa only [one_mul] using hden_lower
    have hden_sq_lower :
        c ^ 2 ≤ unequalDampedCanonicalDenom13_17 θ (P ω) ^ 2 := by
      nlinarith
    have hden_sq_pos :
        0 < unequalDampedCanonicalDenom13_17 θ (P ω) ^ 2 :=
      sq_pos_of_pos hdenpos
    have hc_sq_pos : 0 < c ^ 2 := sq_pos_of_pos hcpos
    have hquadratic2 :
        |unequalDampedCanonicalQuadraticFactor2 θ (P ω)|
          ≤ (c ^ 2)⁻¹ := by
      unfold unequalDampedCanonicalQuadraticFactor2
      rw [abs_div, abs_of_pos hden_sq_pos, div_le_iff₀ hden_sq_pos]
      calc
        |unequalDampedCanonicalQuadraticFactor0 θ (P ω)| ≤ 1 :=
          hquadratic0
        _ ≤ (c ^ 2)⁻¹
              * unequalDampedCanonicalDenom13_17 θ (P ω) ^ 2 := by
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
          (fun ω =>
            unequalDampedCanonicalLinearFactor0 θ (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_unequalDampedCanonicalLinearFactor0 θ).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa only [Real.norm_eq_abs, norm_one] using hω.1
  · apply (integrable_const (c := c⁻¹)).mono'
      (show AEStronglyMeasurable
          (fun ω =>
            unequalDampedCanonicalLinearFactor1 θ (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_unequalDampedCanonicalLinearFactor1 θ).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa [Real.norm_eq_abs, abs_of_pos hcpos] using hω.2.1
  · apply (integrable_const (c := (1 : ℝ))).mono'
      (show AEStronglyMeasurable
          (fun ω =>
            unequalDampedCanonicalQuadraticFactor0 θ (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_unequalDampedCanonicalQuadraticFactor0 θ).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa only [Real.norm_eq_abs, norm_one] using hω.2.2.1
  · apply (integrable_const (c := c⁻¹)).mono'
      (show AEStronglyMeasurable
          (fun ω =>
            unequalDampedCanonicalQuadraticFactor1 θ (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_unequalDampedCanonicalQuadraticFactor1 θ).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa [Real.norm_eq_abs, abs_of_pos hcpos] using hω.2.2.2.1
  · apply (integrable_const (c := (c ^ 2)⁻¹)).mono'
      (show AEStronglyMeasurable
          (fun ω =>
            unequalDampedCanonicalQuadraticFactor2 θ (P ω)) Pmeasure from by
        simpa only [Function.comp_def] using
          ((measurable_unequalDampedCanonicalQuadraticFactor2 θ).comp_aemeasurable
            hP.aemeasurable).aestronglyMeasurable)
    filter_upwards [hfactor_bounds] with ω hω
    simpa [Real.norm_eq_abs, abs_of_pos hcpos,
      abs_of_pos (sq_pos_of_pos hcpos)] using hω.2.2.2.2

/-! ## Exact expectations and the component-law moment bridge -/

/--
Transport the direct canonical linear coefficient through the
`Beta(6,8)` law of `P`.
-/
theorem unequalDampedCanonicalB13_17_expectation_of_hasLaw
    (θ : ℝ) (P : Ω → ℝ) (Pmeasure : Measure Ω)
    (hP : HasLaw P (betaMeasure 6 8) Pmeasure) :
    (∫ ω, unequalDampedCanonicalBIntegrand13_17 θ (P ω) ∂Pmeasure)
      = unequalDampedCanonicalB13_17 θ := by
  calc
    (∫ ω, unequalDampedCanonicalBIntegrand13_17 θ (P ω) ∂Pmeasure)
        =
      ∫ p, unequalDampedCanonicalBIntegrand13_17 θ p
        ∂betaMeasure 6 8 := by
          simpa only [Function.comp_def] using
            hP.integral_comp
              (Measurable.aestronglyMeasurable
                (measurable_unequalDampedCanonicalBIntegrand13_17 θ))
    _ = unequalDampedCanonicalB13_17 θ := rfl

/--
Transport the direct canonical quadratic coefficient through the
`Beta(6,8)` law of `P`.
-/
theorem unequalDampedCanonicalC13_17_expectation_of_hasLaw
    (θ : ℝ) (P : Ω → ℝ) (Pmeasure : Measure Ω)
    (hP : HasLaw P (betaMeasure 6 8) Pmeasure) :
    (∫ ω, unequalDampedCanonicalCIntegrand13_17 θ (P ω) ∂Pmeasure)
      = unequalDampedCanonicalC13_17 θ := by
  calc
    (∫ ω, unequalDampedCanonicalCIntegrand13_17 θ (P ω) ∂Pmeasure)
        =
      ∫ p, unequalDampedCanonicalCIntegrand13_17 θ p
        ∂betaMeasure 6 8 := by
          simpa only [Function.comp_def] using
            hP.integral_comp
              (Measurable.aestronglyMeasurable
                (measurable_unequalDampedCanonicalCIntegrand13_17 θ))
    _ = unequalDampedCanonicalC13_17 θ := rfl

/--
The fixed unequal canonical two-moment bridge follows from the three
component laws and the two joint-independence statements.
-/
theorem unequalDampedCanonicalMomentBridge13_17_of_component_laws
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (P L V : Ω → ℝ) (Pmeasure : Measure Ω)
    (hP : HasLaw P (betaMeasure 6 8) Pmeasure)
    (hL : HasLaw L (gammaMeasure 14 (1 / 2)) Pmeasure)
    (hV : HasLaw V (gammaMeasure (1 / 2) (1 / 2)) Pmeasure)
    (hP_LV : IndepFun P (fun ω => (L ω, V ω)) Pmeasure)
    (hVL : IndepFun V L Pmeasure) :
    UnequalDampedMomentBridge θ
      (unequalDampedCanonicalB13_17 θ)
      (unequalDampedCanonicalC13_17 θ)
      (fun ω => unequalDampedCanonicalR13_17 θ (P ω))
      (fun ω =>
        unequalDampedCanonicalH13_17 θ (P ω) (L ω) (V ω))
      V Pmeasure := by
  exact
    unequalDampedCanonicalMomentBridge13_17_of_canonical_expectations
      θ P L V Pmeasure hP_LV hVL
      (generalCanonicalFiveMoments_of_gamma_laws
        14 (by norm_num) L V Pmeasure hL hV)
      (unequalDampedCanonicalPFactorIntegrability13_17_of_beta_law
        hθ0 hθ1 P Pmeasure hP)
      (unequalDampedCanonicalB13_17_expectation_of_hasLaw
        θ P Pmeasure hP)
      (unequalDampedCanonicalC13_17_expectation_of_hasLaw
        θ P Pmeasure hP)

end

end GraybillDeal
