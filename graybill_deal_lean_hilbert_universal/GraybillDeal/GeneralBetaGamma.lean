import GraybillDeal.BetaGamma

/-!
# Parameter-generic beta--gamma ratio/sum laws

The original `GraybillDeal.BetaGamma` file proves the ratio/sum law at the
single shape needed for the `n = 13` development.  This file separates the
probability-law argument from that numerical specialization.

For the all-equal-sample-size application the residual gamma shape is
`a = (n - 1) / 2`, so `n ≥ 10` gives `a > 1`.  The slightly stronger
assumption `1 < a` used below makes the gamma density vanish pointwise at
zero, which keeps the support bookkeeping elementary.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

/-- The beta/gamma density factorization for an arbitrary common shape and
rate.  This is the parameter-generic analytic core of the ratio/sum law. -/
theorem betaGamma_density_identity_real_general
    {a r p l : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hp : 0 < p ∧ p < 1) (hl : 0 < l) :
    betaPDFReal a a p * gammaPDFReal (2 * a) r l
      =
    l * (gammaPDFReal a r (p * l)
      * gammaPDFReal a r ((1 - p) * l)) := by
  have hpl : 0 ≤ p * l := (mul_pos hp.1 hl).le
  have hql : 0 ≤ (1 - p) * l :=
    (mul_pos (sub_pos.mpr hp.2) hl).le
  have hGa : Real.Gamma a ≠ 0 :=
    (Real.Gamma_pos_of_pos ha).ne'
  have hG2a : Real.Gamma (2 * a) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hrpow : r ^ (2 * a) = r ^ a * r ^ a := by
    rw [show 2 * a = a + a by ring, Real.rpow_add hr]
  have hplpow :
      (p * l) ^ (a - 1) = p ^ (a - 1) * l ^ (a - 1) := by
    exact Real.mul_rpow hp.1.le hl.le
  have hqlpow :
      ((1 - p) * l) ^ (a - 1) =
        (1 - p) ^ (a - 1) * l ^ (a - 1) := by
    exact Real.mul_rpow (sub_nonneg.mpr hp.2.le) hl.le
  have hlpow :
      l ^ (2 * a - 1) =
        l * (l ^ (a - 1) * l ^ (a - 1)) := by
    rw [show 2 * a - 1 = 1 + ((a - 1) + (a - 1)) by ring,
      Real.rpow_add hl, Real.rpow_one, Real.rpow_add hl]
  have hexp :
      Real.exp (-(r * (p * l)))
          * Real.exp (-(r * ((1 - p) * l)))
        =
      Real.exp (-(r * l)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [betaPDFReal, if_pos hp, gammaPDFReal, if_pos hl.le,
    gammaPDFReal, if_pos hpl, gammaPDFReal, if_pos hql]
  unfold beta
  rw [hrpow, hplpow, hqlpow, hlpow, ← hexp]
  field_simp [hGa, hG2a]
  ring

/-- The parameter-generic density factorization in `ℝ≥0∞`. -/
theorem betaGamma_density_identity_general
    {a r p l : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hp : 0 < p ∧ p < 1) (hl : 0 < l) :
    betaPDF a a p * gammaPDF (2 * a) r l
      =
    ENNReal.ofReal l * (gammaPDF a r (p * l)
      * gammaPDF a r ((1 - p) * l)) := by
  unfold betaPDF gammaPDF
  rw [← ENNReal.ofReal_mul
      (le_of_lt (betaPDFReal_pos hp.1 hp.2 ha ha)),
    betaGamma_density_identity_real_general ha hr hp hl,
    ENNReal.ofReal_mul hl.le]
  congr 1
  rw [ENNReal.ofReal_mul
      (gammaPDFReal_nonneg ha hr (p * l))]

private theorem gammaPDF_general_eq_zero_of_nonpos
    {a r x : ℝ} (ha : 1 < a) (hx : x ≤ 0) :
    gammaPDF a r x = 0 := by
  rcases hx.eq_or_lt with rfl | hxneg
  · rw [gammaPDF_eq, if_pos le_rfl]
    rw [Real.zero_rpow (sub_pos.mpr ha).ne']
    simp
  · exact gammaPDF_of_neg hxneg

/-- Pushing `Beta(a,a) × Gamma(2a,r)` through the component map gives two
independent `Gamma(a,r)` coordinates. -/
theorem map_betaGammaComponents_general
    {a r : ℝ} (ha : 1 < a) (hr : 0 < r) :
    Measure.map betaGammaComponents
        ((betaMeasure a a).prod (gammaMeasure (2 * a) r))
      =
    (gammaMeasure a r).prod (gammaMeasure a r) := by
  let betaDensity : (ℝ × ℝ) → ℝ≥0∞ :=
    fun z => betaPDF a a z.1 * gammaPDF (2 * a) r z.2
  let gammaDensity : (ℝ × ℝ) → ℝ≥0∞ :=
    fun z => gammaPDF a r z.1 * gammaPDF a r z.2
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  have h2a0 : 0 < 2 * a := by positivity
  have hbetaPDF : Measurable (betaPDF a a) :=
    (measurable_betaPDFReal a a).ennreal_ofReal
  have hgammaPDF2a : Measurable (gammaPDF (2 * a) r) :=
    (measurable_gammaPDFReal (2 * a) r).ennreal_ofReal
  have hgammaPDFa : Measurable (gammaPDF a r) :=
    (measurable_gammaPDFReal a r).ennreal_ofReal
  have hbetaDensity : Measurable betaDensity := by
    unfold betaDensity
    exact (hbetaPDF.comp measurable_fst).mul
      (hgammaPDF2a.comp measurable_snd)
  have hgammaDensity : Measurable gammaDensity := by
    unfold gammaDensity
    exact (hgammaPDFa.comp measurable_fst).mul
      (hgammaPDFa.comp measurable_snd)
  simp only [betaMeasure, gammaMeasure]
  rw [prod_withDensity hbetaPDF hgammaPDF2a,
    prod_withDensity hgammaPDFa hgammaPDFa]
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
      rcases hz' with hp' | hl'
      · have hpdf : betaPDF a a z.1 = 0 := by
          rcases not_and_or.mp hp' with hp0 | hp1
          · exact betaPDF_eq_zero_of_nonpos (le_of_not_gt hp0)
          · exact betaPDF_eq_zero_of_one_le (le_of_not_gt hp1)
        simp [betaDensity, hpdf, hz]
      · have hpdf : gammaPDF (2 * a) r z.2 = 0 :=
          gammaPDF_general_eq_zero_of_nonpos (by linarith) (le_of_not_gt hl')
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
      · have hpdf : gammaPDF a r z.1 = 0 :=
          gammaPDF_general_eq_zero_of_nonpos ha (le_of_not_gt hleft)
        simp [gammaDensity, hpdf, hz]
      · have hpdf : gammaPDF a r z.2 = 0 :=
          gammaPDF_general_eq_zero_of_nonpos ha (le_of_not_gt hright)
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
              rw [betaGamma_density_identity_general ha0 hr hz.1 hz.2]
              simp only [betaGammaComponents]
              ac_rfl
    _ =
      ∫⁻ z in Ioi (0 : ℝ) ×ˢ Ioi 0,
        gammaDensity z * f z := by
          symm
          exact lintegral_betaGammaComponents
            (fun z => gammaDensity z * f z)

private theorem betaMeasure_general_ae_mem_Ioo
    {a : ℝ} :
    ∀ᵐ p : ℝ ∂betaMeasure a a, p ∈ Ioo (0 : ℝ) 1 := by
  unfold betaMeasure betaPDF
  rw [ae_withDensity_iff
    ((measurable_betaPDFReal a a).ennreal_ofReal)]
  filter_upwards [] with p hp
  by_contra hmem
  have hzero : betaPDF a a p = 0 := by
    rcases not_and_or.mp (by simpa only [mem_Ioo] using hmem) with hp0 | hp1
    · exact betaPDF_eq_zero_of_nonpos (le_of_not_gt hp0)
    · exact betaPDF_eq_zero_of_one_le (le_of_not_gt hp1)
  exact hp hzero

private theorem gammaMeasure_general_ae_pos
    {a r : ℝ} (ha : 1 < a) :
    ∀ᵐ l : ℝ ∂gammaMeasure a r, 0 < l := by
  unfold gammaMeasure gammaPDF
  rw [ae_withDensity_iff
    ((measurable_gammaPDFReal a r).ennreal_ofReal)]
  filter_upwards [] with l hl
  by_contra hpos
  exact hl (gammaPDF_general_eq_zero_of_nonpos ha (le_of_not_gt hpos))

/-- The inverse ratio--sum map sends two independent gamma measures to
`Beta(a,a) × Gamma(2a,r)`. -/
theorem map_betaGammaRatioSum_general
    {a r : ℝ} (ha : 1 < a) (hr : 0 < r) :
    Measure.map betaGammaRatioSum
        ((gammaMeasure a r).prod (gammaMeasure a r))
      =
    (betaMeasure a a).prod (gammaMeasure (2 * a) r) := by
  let mu := (betaMeasure a a).prod (gammaMeasure (2 * a) r)
  rw [← map_betaGammaComponents_general ha hr]
  rw [Measure.map_map measurable_betaGammaRatioSum
    measurable_betaGammaComponents]
  have hmu :
      ∀ᵐ z ∂mu, z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioi 0 := by
    letI : IsProbabilityMeasure (gammaMeasure (2 * a) r) :=
      isProbabilityMeasure_gammaMeasure (by linarith) hr
    dsimp only [mu]
    rw [Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioo.prod measurableSet_Ioi)]
    filter_upwards [betaMeasure_general_ae_mem_Ioo] with p hp
    filter_upwards [gammaMeasure_general_ae_pos (a := 2 * a)
      (r := r) (by linarith)] with l hl
    exact ⟨hp, hl⟩
  have hinverse :
      (betaGammaRatioSum ∘ betaGammaComponents) =ᵐ[mu] id := by
    filter_upwards [hmu] with z hz
    simpa [Function.comp_apply, betaGammaPartialHomeomorph] using
      betaGammaPartialHomeomorph.left_inv hz
  rw [Measure.map_congr hinverse]
  exact Measure.map_id

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Independent `Gamma(a,r)` variables have the joint ratio/sum law
`Beta(a,a) × Gamma(2a,r)`. -/
theorem hasLaw_betaGammaRatioSum_of_indep_general
    {a r : ℝ} (ha : 1 < a) (hr : 0 < r)
    (U₁ U₂ : Ω → ℝ) (mu : Measure Ω) [IsFiniteMeasure mu]
    (hU₁ : HasLaw U₁ (gammaMeasure a r) mu)
    (hU₂ : HasLaw U₂ (gammaMeasure a r) mu)
    (hinde : IndepFun U₁ U₂ mu) :
    HasLaw
      (fun ω => (U₁ ω / (U₁ ω + U₂ ω), U₁ ω + U₂ ω))
      ((betaMeasure a a).prod (gammaMeasure (2 * a) r)) mu := by
  have hpair :
      HasLaw (fun ω => (U₁ ω, U₂ ω))
        ((gammaMeasure a r).prod (gammaMeasure a r)) mu :=
    IndepFun.hasLaw_prod hU₁ hU₂ hinde
  have htransform :
      HasLaw betaGammaRatioSum
        ((betaMeasure a a).prod (gammaMeasure (2 * a) r))
        ((gammaMeasure a r).prod (gammaMeasure a r)) :=
    { aemeasurable := measurable_betaGammaRatioSum.aemeasurable
      map_eq := map_betaGammaRatioSum_general ha hr }
  simpa only [Function.comp_apply, betaGammaRatioSum] using
    htransform.fun_comp hpair

/-- Component laws and independence extracted from the generic joint
ratio/sum law. -/
theorem betaGamma_component_laws_and_indep_general
    {a r : ℝ} (ha : 1 < a) (hr : 0 < r)
    (U₁ U₂ : Ω → ℝ) (mu : Measure Ω) [IsFiniteMeasure mu]
    (hU₁ : HasLaw U₁ (gammaMeasure a r) mu)
    (hU₂ : HasLaw U₂ (gammaMeasure a r) mu)
    (hinde : IndepFun U₁ U₂ mu) :
    HasLaw (fun ω => U₁ ω / (U₁ ω + U₂ ω))
        (betaMeasure a a) mu
      ∧
    HasLaw (fun ω => U₁ ω + U₂ ω)
        (gammaMeasure (2 * a) r) mu
      ∧
    IndepFun
        (fun ω => U₁ ω / (U₁ ω + U₂ ω))
        (fun ω => U₁ ω + U₂ ω) mu := by
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  letI : IsProbabilityMeasure (betaMeasure a a) :=
    isProbabilityMeasureBeta ha0 ha0
  letI : IsProbabilityMeasure (gammaMeasure (2 * a) r) :=
    isProbabilityMeasure_gammaMeasure (by linarith) hr
  have hpair :=
    hasLaw_betaGammaRatioSum_of_indep_general ha hr
      U₁ U₂ mu hU₁ hU₂ hinde
  have hratio :
      HasLaw (fun ω => U₁ ω / (U₁ ω + U₂ ω))
        (betaMeasure a a) mu := by
    have hfst :
        HasLaw (fun z : ℝ × ℝ => z.1)
          (betaMeasure a a)
          ((betaMeasure a a).prod (gammaMeasure (2 * a) r)) :=
      measurePreserving_fst.hasLaw
    simpa only [Function.comp_apply] using hfst.fun_comp hpair
  have hsum :
      HasLaw (fun ω => U₁ ω + U₂ ω)
        (gammaMeasure (2 * a) r) mu := by
    have hsnd :
        HasLaw (fun z : ℝ × ℝ => z.2)
          (gammaMeasure (2 * a) r)
          ((betaMeasure a a).prod (gammaMeasure (2 * a) r)) :=
      measurePreserving_snd.hasLaw
    simpa only [Function.comp_apply] using hsnd.fun_comp hpair
  refine ⟨hratio, hsum, ?_⟩
  apply
    (indepFun_iff_map_prod_eq_prod_map_map
      hratio.aemeasurable hsum.aemeasurable).2
  rw [hpair.map_eq, hratio.map_eq, hsum.map_eq]

end

end GraybillDeal
