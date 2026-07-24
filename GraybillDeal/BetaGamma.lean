import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw

/-!
# The beta--gamma ratio/sum transformation

This file formalizes the deterministic and differential part of the standard
beta--gamma change of variables.  The map

`(p, l) ↦ (p*l, (1-p)*l)`

is an open partial homeomorphism from `(0,1) × (0,∞)` to
`(0,∞) × (0,∞)`, with absolute Jacobian determinant `l`.  Its inverse is

`(u₁,u₂) ↦ (u₁/(u₁+u₂), u₁+u₂)`.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

/-- Convert a beta proportion and a positive total into its two components. -/
def betaGammaComponents (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 * z.2, (1 - z.1) * z.2)

/-- Convert two positive components into their ratio and sum. -/
def betaGammaRatioSum (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 / (z.1 + z.2), z.1 + z.2)

@[fun_prop]
theorem measurable_betaGammaComponents : Measurable betaGammaComponents := by
  unfold betaGammaComponents
  fun_prop

@[fun_prop]
theorem measurable_betaGammaRatioSum : Measurable betaGammaRatioSum := by
  unfold betaGammaRatioSum
  fun_prop

/--
The beta--gamma coordinate transformation, as a homeomorphism between the
two natural open supports.
-/
@[simps]
def betaGammaPartialHomeomorph :
    OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) where
  toFun := betaGammaComponents
  invFun := betaGammaRatioSum
  source := Ioo (0 : ℝ) 1 ×ˢ Ioi 0
  target := Ioi (0 : ℝ) ×ˢ Ioi 0
  map_target' := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    dsimp at hu hv
    change
      (0 < u / (u + v) ∧ u / (u + v) < 1) ∧
        0 < u + v
    have huv : 0 < u + v := add_pos hu hv
    have hv' : 0 < v := hv
    exact
      ⟨⟨div_pos hu huv, (div_lt_one huv).2 (by
        linarith only [hv'])⟩, huv⟩
  map_source' := by
    rintro ⟨p, l⟩ ⟨hp, hl⟩
    change 0 < p * l ∧ 0 < (1 - p) * l
    exact ⟨mul_pos hp.1 hl, mul_pos (sub_pos.mpr hp.2) hl⟩
  right_inv' := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have huv : u + v ≠ 0 := (add_pos hu hv).ne'
    apply Prod.ext <;>
      simp only [betaGammaRatioSum, betaGammaComponents]
    · field_simp
    · field_simp
      ring
  left_inv' := by
    rintro ⟨p, l⟩ ⟨hp, hl⟩
    have hlne : l ≠ 0 := hl.ne'
    apply Prod.ext <;>
      simp only [betaGammaRatioSum, betaGammaComponents]
    · field_simp
      ring
    · ring
  open_source := isOpen_Ioo.prod isOpen_Ioi
  open_target := isOpen_Ioi.prod isOpen_Ioi
  continuousOn_toFun := by
    unfold betaGammaComponents
    fun_prop
  continuousOn_invFun := by
    intro z hz
    unfold betaGammaRatioSum
    apply ContinuousWithinAt.prodMk
    · apply ContinuousWithinAt.div
      · fun_prop
      · fun_prop
      · exact (add_pos hz.1 hz.2).ne'
    · fun_prop

/-- The derivative of `betaGammaComponents`. -/
def betaGammaComponentsFDeriv (z : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![z.2, z.1; -z.2, 1 - z.1]).toContinuousLinearMap

theorem hasFDerivAt_betaGammaComponents (z : ℝ × ℝ) :
    HasFDerivAt betaGammaComponents (betaGammaComponentsFDeriv z) z := by
  unfold betaGammaComponentsFDeriv betaGammaComponents
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  have hfirst :=
    (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := z)).mul
      (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := z))
  have hsecond :=
    ((hasFDerivAt_const (x := z) (c := (1 : ℝ))).sub
      (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := z))).mul
        (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := z))
  convert!
    HasFDerivAt.prodMk (𝕜 := ℝ) hfirst hsecond using 2
  · exact add_comm _ _
  · simp only [Pi.sub_apply, zero_sub, smul_neg]
    module

/-- The Jacobian determinant of the component map is the total `l`. -/
theorem det_betaGammaComponentsFDeriv (z : ℝ × ℝ) :
    (betaGammaComponentsFDeriv z).det = z.2 := by
  unfold betaGammaComponentsFDeriv
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  ring

theorem beta_six_six_value :
    beta 6 6 = (1 / 2772 : ℝ) := by
  unfold beta
  norm_num [Real.Gamma_ofNat_eq_factorial]

/--
Pointwise factorization of the real beta/gamma densities under the
ratio--sum transformation.  This is the analytic identity behind the
independence theorem.
-/
theorem betaGamma_density_identity_real
    {p l : ℝ} (hp : 0 < p ∧ p < 1) (hl : 0 < l) :
    betaPDFReal 6 6 p * gammaPDFReal 12 (1 / 2) l
      =
    l * (gammaPDFReal 6 (1 / 2) (p * l)
      * gammaPDFReal 6 (1 / 2) ((1 - p) * l)) := by
  have hpl : 0 ≤ p * l := (mul_pos hp.1 hl).le
  have hql : 0 ≤ (1 - p) * l :=
    (mul_pos (sub_pos.mpr hp.2) hl).le
  rw [betaPDFReal, if_pos hp, gammaPDFReal, if_pos hl.le,
    gammaPDFReal, if_pos hpl, gammaPDFReal, if_pos hql,
    beta_six_six_value]
  norm_num [Real.Gamma_ofNat_eq_factorial, Real.rpow_natCast]
  have hexp :
      Real.exp (-(1 / 2 * (p * l)))
          * Real.exp (-(1 / 2 * ((1 - p) * l)))
        =
      Real.exp (-(1 / 2 * l)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    2772 * p ^ 5 * (1 - p) ^ 5
          * (1 / 163499212800 * l ^ 11 * Real.exp (-(1 / 2 * l)))
        =
      (1 / 58982400) * p ^ 5 * (1 - p) ^ 5 * l ^ 11
        * Real.exp (-(1 / 2 * l)) := by ring
    _ =
      (1 / 58982400) * p ^ 5 * (1 - p) ^ 5 * l ^ 11
        * (Real.exp (-(1 / 2 * (p * l)))
          * Real.exp (-(1 / 2 * ((1 - p) * l)))) := by rw [hexp]
    _ =
      l *
        (1 / 7680 * (p * l) ^ 5 * Real.exp (-(1 / 2 * (p * l)))
          *
        (1 / 7680 * ((1 - p) * l) ^ 5
          * Real.exp (-(1 / 2 * ((1 - p) * l))))) := by ring

/-- The same density factorization in `ℝ≥0∞`. -/
theorem betaGamma_density_identity
    {p l : ℝ} (hp : 0 < p ∧ p < 1) (hl : 0 < l) :
    betaPDF 6 6 p * gammaPDF 12 (1 / 2) l
      =
    ENNReal.ofReal l * (gammaPDF 6 (1 / 2) (p * l)
      * gammaPDF 6 (1 / 2) ((1 - p) * l)) := by
  unfold betaPDF gammaPDF
  rw [← ENNReal.ofReal_mul
      (le_of_lt (betaPDFReal_pos hp.1 hp.2 (by norm_num) (by norm_num))),
    betaGamma_density_identity_real hp hl,
    ENNReal.ofReal_mul hl.le]
  congr 1
  rw [ENNReal.ofReal_mul
      (gammaPDFReal_nonneg (by norm_num) (by norm_num) (p * l))]

/--
The two-dimensional change-of-variables formula on the natural supports.
-/
theorem lintegral_betaGammaComponents
    (g : (ℝ × ℝ) → ℝ≥0∞) :
    (∫⁻ z in Ioi (0 : ℝ) ×ˢ Ioi 0, g z)
      =
    ∫⁻ z in Ioo (0 : ℝ) 1 ×ˢ Ioi 0,
      ENNReal.ofReal z.2 * g (betaGammaComponents z) := by
  have h :=
    lintegral_image_eq_lintegral_abs_det_fderiv_mul
      (μ := volume) (f := betaGammaComponents)
      (f' := betaGammaComponentsFDeriv)
      (measurableSet_Ioo.prod measurableSet_Ioi)
      (fun z _ => (hasFDerivAt_betaGammaComponents z).hasFDerivWithinAt)
      betaGammaPartialHomeomorph.injOn g
  have himage :
      betaGammaComponents '' (Ioo (0 : ℝ) 1 ×ˢ Ioi 0)
        = Ioi (0 : ℝ) ×ˢ Ioi 0 := by
    simpa [betaGammaPartialHomeomorph] using
      betaGammaPartialHomeomorph.image_source_eq_target
  rw [himage] at h
  calc
    (∫⁻ z in Ioi (0 : ℝ) ×ˢ Ioi 0, g z)
        =
      ∫⁻ z in Ioo (0 : ℝ) 1 ×ˢ Ioi 0,
        ENNReal.ofReal |(betaGammaComponentsFDeriv z).det|
          * g (betaGammaComponents z) := h
    _ =
      ∫⁻ z in Ioo (0 : ℝ) 1 ×ˢ Ioi 0,
        ENNReal.ofReal z.2 * g (betaGammaComponents z) := by
          apply setLIntegral_congr_fun
            (measurableSet_Ioo.prod measurableSet_Ioi)
          intro z hz
          dsimp only
          rw [det_betaGammaComponentsFDeriv, abs_of_pos hz.2]

private theorem gammaPDF_six_half_eq_zero_of_nonpos
    {x : ℝ} (hx : x ≤ 0) :
    gammaPDF 6 (1 / 2) x = 0 := by
  rcases hx.eq_or_lt with rfl | hxneg
  · norm_num [gammaPDF_eq, Real.rpow_natCast]
  · exact gammaPDF_of_neg hxneg

private theorem gammaPDF_twelve_half_eq_zero_of_nonpos
    {x : ℝ} (hx : x ≤ 0) :
    gammaPDF 12 (1 / 2) x = 0 := by
  rcases hx.eq_or_lt with rfl | hxneg
  · norm_num [gammaPDF_eq, Real.rpow_natCast]
  · exact gammaPDF_of_neg hxneg

/--
Pushing `Beta(6,6) × Gamma(12,1/2)` through the component map gives two
independent `Gamma(6,1/2)` variables.
-/
theorem map_betaGammaComponents :
    Measure.map betaGammaComponents
        ((betaMeasure 6 6).prod (gammaMeasure 12 (1 / 2)))
      =
    (gammaMeasure 6 (1 / 2)).prod (gammaMeasure 6 (1 / 2)) := by
  let betaDensity : (ℝ × ℝ) → ℝ≥0∞ :=
    fun z => betaPDF 6 6 z.1 * gammaPDF 12 (1 / 2) z.2
  let gammaDensity : (ℝ × ℝ) → ℝ≥0∞ :=
    fun z => gammaPDF 6 (1 / 2) z.1 * gammaPDF 6 (1 / 2) z.2
  have hbetaPDF : Measurable (betaPDF 6 6) := by
    exact (measurable_betaPDFReal 6 6).ennreal_ofReal
  have hgammaPDF12 : Measurable (gammaPDF 12 (1 / 2)) := by
    exact (measurable_gammaPDFReal 12 (1 / 2)).ennreal_ofReal
  have hgammaPDF6 : Measurable (gammaPDF 6 (1 / 2)) := by
    exact (measurable_gammaPDFReal 6 (1 / 2)).ennreal_ofReal
  have hbetaDensity : Measurable betaDensity := by
    unfold betaDensity
    exact (hbetaPDF.comp measurable_fst).mul
      (hgammaPDF12.comp measurable_snd)
  have hgammaDensity : Measurable gammaDensity := by
    unfold gammaDensity
    exact (hgammaPDF6.comp measurable_fst).mul
      (hgammaPDF6.comp measurable_snd)
  simp only [betaMeasure, gammaMeasure]
  rw [prod_withDensity hbetaPDF hgammaPDF12,
    prod_withDensity hgammaPDF6 hgammaPDF6]
  change
    Measure.map betaGammaComponents (volume.withDensity betaDensity)
      = volume.withDensity gammaDensity
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf measurable_betaGammaComponents]
  change
    (∫⁻ z, (f ∘ betaGammaComponents) z ∂volume.withDensity betaDensity)
      =
    ∫⁻ z, f z ∂volume.withDensity gammaDensity
  rw [lintegral_withDensity_eq_lintegral_mul volume hbetaDensity
      (hf.comp measurable_betaGammaComponents),
    lintegral_withDensity_eq_lintegral_mul volume hgammaDensity hf]
  simp only [Pi.mul_apply, Function.comp_apply]
  have hsource :
      (∫⁻ z : ℝ × ℝ, betaDensity z * f (betaGammaComponents z))
        =
      ∫⁻ z in Ioo (0 : ℝ) 1 ×ˢ Ioi 0,
        betaDensity z * f (betaGammaComponents z) := by
    rw [← lintegral_indicator
      (measurableSet_Ioo.prod measurableSet_Ioi)]
    apply lintegral_congr
    intro z
    by_cases hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioi 0
    · simp [hz]
    · have hz' :
          ¬(0 < z.1 ∧ z.1 < 1) ∨ ¬0 < z.2 := by
        simpa only [mem_prod, mem_Ioo, mem_Ioi, not_and_or] using hz
      rcases hz' with hp | hl
      · have hpdf : betaPDF 6 6 z.1 = 0 := by
          rcases not_and_or.mp hp with hp0 | hp1
          · exact betaPDF_eq_zero_of_nonpos (le_of_not_gt hp0)
          · exact betaPDF_eq_zero_of_one_le (le_of_not_gt hp1)
        simp [betaDensity, hpdf, hz]
      · have hpdf :
            gammaPDF 12 (2⁻¹ : ℝ) z.2 = 0 := by
          simpa only [one_div] using
            gammaPDF_twelve_half_eq_zero_of_nonpos (le_of_not_gt hl)
        simp [betaDensity, hpdf, hz]
  have htarget :
      (∫⁻ z : ℝ × ℝ, gammaDensity z * f z)
        =
      ∫⁻ z in Ioi (0 : ℝ) ×ˢ Ioi 0,
        gammaDensity z * f z := by
    rw [← lintegral_indicator
      (measurableSet_Ioi.prod measurableSet_Ioi)]
    apply lintegral_congr
    intro z
    by_cases hz : z ∈ Ioi (0 : ℝ) ×ˢ Ioi 0
    · simp [hz]
    · have hz' : ¬0 < z.1 ∨ ¬0 < z.2 := by
        simp only [mem_prod, mem_Ioi, not_and_or] at hz
        exact hz
      rcases hz' with hleft | hright
      · have hpdf :
            gammaPDF 6 (2⁻¹ : ℝ) z.1 = 0 := by
          simpa only [one_div] using
            gammaPDF_six_half_eq_zero_of_nonpos (le_of_not_gt hleft)
        simp [gammaDensity, hpdf, hz]
      · have hpdf :
            gammaPDF 6 (2⁻¹ : ℝ) z.2 = 0 := by
          simpa only [one_div] using
            gammaPDF_six_half_eq_zero_of_nonpos (le_of_not_gt hright)
        simp [gammaDensity, hpdf, hz]
  rw [hsource, htarget]
  calc
    (∫⁻ z in Ioo (0 : ℝ) 1 ×ˢ Ioi 0,
      betaDensity z * f (betaGammaComponents z))
        =
      ∫⁻ z in Ioo (0 : ℝ) 1 ×ˢ Ioi 0,
        ENNReal.ofReal z.2
          * (gammaDensity (betaGammaComponents z)
            * f (betaGammaComponents z)) := by
              apply setLIntegral_congr_fun
                (measurableSet_Ioo.prod measurableSet_Ioi)
              intro z hz
              dsimp only [betaDensity, gammaDensity]
              rw [betaGamma_density_identity hz.1 hz.2]
              simp only [betaGammaComponents]
              ac_rfl
    _ =
      ∫⁻ z in Ioi (0 : ℝ) ×ˢ Ioi 0,
        gammaDensity z * f z := by
          symm
          exact lintegral_betaGammaComponents
            (fun z => gammaDensity z * f z)

private theorem betaMeasure_six_six_ae_mem_Ioo :
    ∀ᵐ p : ℝ ∂betaMeasure 6 6, p ∈ Ioo (0 : ℝ) 1 := by
  unfold betaMeasure betaPDF
  rw [ae_withDensity_iff
    ((measurable_betaPDFReal 6 6).ennreal_ofReal)]
  filter_upwards [] with p hp
  by_contra hmem
  have hzero : betaPDF 6 6 p = 0 := by
    rcases not_and_or.mp (by simpa only [mem_Ioo] using hmem) with hp0 | hp1
    · exact betaPDF_eq_zero_of_nonpos (le_of_not_gt hp0)
    · exact betaPDF_eq_zero_of_one_le (le_of_not_gt hp1)
  exact hp hzero

private theorem gammaMeasure_twelve_half_ae_pos :
    ∀ᵐ l : ℝ ∂gammaMeasure 12 (1 / 2), 0 < l := by
  unfold gammaMeasure gammaPDF
  rw [ae_withDensity_iff
    ((measurable_gammaPDFReal 12 (1 / 2)).ennreal_ofReal)]
  filter_upwards [] with l hl
  by_contra hpos
  exact hl (gammaPDF_twelve_half_eq_zero_of_nonpos (le_of_not_gt hpos))

/--
The inverse ratio--sum map sends the two independent gamma measures to the
product `Beta(6,6) × Gamma(12,1/2)` measure.
-/
theorem map_betaGammaRatioSum :
    Measure.map betaGammaRatioSum
        ((gammaMeasure 6 (1 / 2)).prod (gammaMeasure 6 (1 / 2)))
      =
    (betaMeasure 6 6).prod (gammaMeasure 12 (1 / 2)) := by
  let mu :=
    (betaMeasure 6 6).prod (gammaMeasure 12 (1 / 2))
  rw [← map_betaGammaComponents]
  rw [Measure.map_map measurable_betaGammaRatioSum
    measurable_betaGammaComponents]
  have hmu :
      ∀ᵐ z ∂mu, z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioi 0 := by
    letI : IsProbabilityMeasure (gammaMeasure 12 (1 / 2)) :=
      isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
    dsimp only [mu]
    rw [Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioo.prod measurableSet_Ioi)]
    filter_upwards [betaMeasure_six_six_ae_mem_Ioo] with p hp
    filter_upwards [gammaMeasure_twelve_half_ae_pos] with l hl
    exact ⟨hp, hl⟩
  have hinverse :
      (betaGammaRatioSum ∘ betaGammaComponents)
        =ᵐ[mu] id := by
    filter_upwards [hmu] with z hz
    simpa [Function.comp_apply, betaGammaPartialHomeomorph] using
      betaGammaPartialHomeomorph.left_inv hz
  rw [Measure.map_congr hinverse]
  exact Measure.map_id

variable {Ω : Type*} [MeasurableSpace Ω]

/--
If `U₁,U₂` are independent `Gamma(6,1/2)` random variables, their
ratio--sum pair has the product law
`Beta(6,6) × Gamma(12,1/2)`.
-/
theorem hasLaw_betaGammaRatioSum_of_indep
    (U₁ U₂ : Ω → ℝ) (mu : Measure Ω)
    [IsFiniteMeasure mu]
    (hU₁ : HasLaw U₁ (gammaMeasure 6 (1 / 2)) mu)
    (hU₂ : HasLaw U₂ (gammaMeasure 6 (1 / 2)) mu)
    (hinde : IndepFun U₁ U₂ mu) :
    HasLaw
      (fun ω =>
        (U₁ ω / (U₁ ω + U₂ ω), U₁ ω + U₂ ω))
      ((betaMeasure 6 6).prod (gammaMeasure 12 (1 / 2))) mu := by
  have hpair :
      HasLaw (fun ω => (U₁ ω, U₂ ω))
        ((gammaMeasure 6 (1 / 2)).prod
          (gammaMeasure 6 (1 / 2))) mu :=
    IndepFun.hasLaw_prod hU₁ hU₂ hinde
  have htransform :
      HasLaw betaGammaRatioSum
        ((betaMeasure 6 6).prod (gammaMeasure 12 (1 / 2)))
        ((gammaMeasure 6 (1 / 2)).prod
          (gammaMeasure 6 (1 / 2))) :=
    { aemeasurable := measurable_betaGammaRatioSum.aemeasurable
      map_eq := map_betaGammaRatioSum }
  simpa only [Function.comp_apply, betaGammaRatioSum] using
    htransform.fun_comp hpair

/--
The component laws and the independence conclusion extracted from the joint
ratio--sum law.
-/
theorem betaGamma_component_laws_and_indep
    (U₁ U₂ : Ω → ℝ) (mu : Measure Ω)
    [IsFiniteMeasure mu]
    (hU₁ : HasLaw U₁ (gammaMeasure 6 (1 / 2)) mu)
    (hU₂ : HasLaw U₂ (gammaMeasure 6 (1 / 2)) mu)
    (hinde : IndepFun U₁ U₂ mu) :
    HasLaw
        (fun ω => U₁ ω / (U₁ ω + U₂ ω))
        (betaMeasure 6 6) mu
      ∧
    HasLaw
        (fun ω => U₁ ω + U₂ ω)
        (gammaMeasure 12 (1 / 2)) mu
      ∧
    IndepFun
        (fun ω => U₁ ω / (U₁ ω + U₂ ω))
        (fun ω => U₁ ω + U₂ ω) mu := by
  letI : IsProbabilityMeasure (betaMeasure 6 6) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (gammaMeasure 12 (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  have hpair :=
    hasLaw_betaGammaRatioSum_of_indep U₁ U₂ mu hU₁ hU₂ hinde
  have hratio :
      HasLaw
        (fun ω => U₁ ω / (U₁ ω + U₂ ω))
        (betaMeasure 6 6) mu := by
    have hfst :
        HasLaw (fun z : ℝ × ℝ => z.1)
          (betaMeasure 6 6)
          ((betaMeasure 6 6).prod (gammaMeasure 12 (1 / 2))) :=
      measurePreserving_fst.hasLaw
    simpa only [Function.comp_apply] using hfst.fun_comp hpair
  have hsum :
      HasLaw
        (fun ω => U₁ ω + U₂ ω)
        (gammaMeasure 12 (1 / 2)) mu := by
    have hsnd :
        HasLaw (fun z : ℝ × ℝ => z.2)
          (gammaMeasure 12 (1 / 2))
          ((betaMeasure 6 6).prod (gammaMeasure 12 (1 / 2))) :=
      measurePreserving_snd.hasLaw
    simpa only [Function.comp_apply] using hsnd.fun_comp hpair
  refine ⟨hratio, hsum, ?_⟩
  apply
    (indepFun_iff_map_prod_eq_prod_map_map
      hratio.aemeasurable hsum.aemeasurable).2
  rw [hpair.map_eq, hratio.map_eq, hsum.map_eq]

end

end GraybillDeal
