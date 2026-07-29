import GraybillDeal.BetaGamma

/-!
# Unequal-shape beta--gamma ratio/sum laws

This module proves the beta--gamma algebra for two possibly different
positive shapes.  If `U₁ ~ Gamma(a,r)` and `U₂ ~ Gamma(b,r)` are
independent, then

* `U₁ / (U₁ + U₂) ~ Beta(a,b)`;
* `U₁ + U₂ ~ Gamma(a+b,r)`; and
* the ratio and sum are independent.

The assumptions `1 < a` and `1 < b` make all gamma densities vanish
pointwise at zero.  This is slightly stronger than the distributional
result requires, but it keeps the support bookkeeping in the
change-of-variables argument elementary.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

/--
The unequal-shape beta/gamma density factorization over the reals.
-/
theorem betaGamma_density_identity_real_unequal
    {a b r p l : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hp : 0 < p ∧ p < 1) (hl : 0 < l) :
    betaPDFReal a b p * gammaPDFReal (a + b) r l
      =
    l * (gammaPDFReal a r (p * l)
      * gammaPDFReal b r ((1 - p) * l)) := by
  have hpl : 0 ≤ p * l := (mul_pos hp.1 hl).le
  have hql : 0 ≤ (1 - p) * l :=
    (mul_pos (sub_pos.mpr hp.2) hl).le
  have hGa : Real.Gamma a ≠ 0 :=
    (Real.Gamma_pos_of_pos ha).ne'
  have hGb : Real.Gamma b ≠ 0 :=
    (Real.Gamma_pos_of_pos hb).ne'
  have hGab : Real.Gamma (a + b) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos ha hb)).ne'
  have hrpow : r ^ (a + b) = r ^ a * r ^ b := by
    rw [Real.rpow_add hr]
  have hplpow :
      (p * l) ^ (a - 1) = p ^ (a - 1) * l ^ (a - 1) := by
    exact Real.mul_rpow hp.1.le hl.le
  have hqlpow :
      ((1 - p) * l) ^ (b - 1) =
        (1 - p) ^ (b - 1) * l ^ (b - 1) := by
    exact Real.mul_rpow (sub_nonneg.mpr hp.2.le) hl.le
  have hlpow :
      l ^ (a + b - 1) =
        l * (l ^ (a - 1) * l ^ (b - 1)) := by
    rw [show a + b - 1 = 1 + ((a - 1) + (b - 1)) by ring,
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
  field_simp [hGa, hGb, hGab]

/--
The unequal-shape density factorization in `ℝ≥0∞`.
-/
theorem betaGamma_density_identity_unequal
    {a b r p l : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hp : 0 < p ∧ p < 1) (hl : 0 < l) :
    betaPDF a b p * gammaPDF (a + b) r l
      =
    ENNReal.ofReal l * (gammaPDF a r (p * l)
      * gammaPDF b r ((1 - p) * l)) := by
  unfold betaPDF gammaPDF
  rw [← ENNReal.ofReal_mul
      (le_of_lt (betaPDFReal_pos hp.1 hp.2 ha hb)),
    betaGamma_density_identity_real_unequal ha hb hr hp hl,
    ENNReal.ofReal_mul hl.le]
  congr 1
  rw [ENNReal.ofReal_mul
      (gammaPDFReal_nonneg ha hr (p * l))]

private theorem gammaPDF_unequal_eq_zero_of_nonpos
    {a r x : ℝ} (ha : 1 < a) (hx : x ≤ 0) :
    gammaPDF a r x = 0 := by
  rcases hx.eq_or_lt with rfl | hxneg
  · rw [gammaPDF_eq, if_pos le_rfl]
    rw [Real.zero_rpow (sub_pos.mpr ha).ne']
    simp
  · exact gammaPDF_of_neg hxneg

/--
Pushing `Beta(a,b) × Gamma(a+b,r)` through the component map gives the
product of `Gamma(a,r)` and `Gamma(b,r)`.
-/
theorem map_betaGammaComponents_unequal
    {a b r : ℝ} (ha : 1 < a) (hb : 1 < b) (hr : 0 < r) :
    Measure.map betaGammaComponents
        ((betaMeasure a b).prod (gammaMeasure (a + b) r))
      =
    (gammaMeasure a r).prod (gammaMeasure b r) := by
  let betaDensity : (ℝ × ℝ) → ℝ≥0∞ :=
    fun z => betaPDF a b z.1 * gammaPDF (a + b) r z.2
  let gammaDensity : (ℝ × ℝ) → ℝ≥0∞ :=
    fun z => gammaPDF a r z.1 * gammaPDF b r z.2
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  have hab1 : 1 < a + b := by linarith
  have hbetaPDF : Measurable (betaPDF a b) :=
    (measurable_betaPDFReal a b).ennreal_ofReal
  have hgammaPDFab : Measurable (gammaPDF (a + b) r) :=
    (measurable_gammaPDFReal (a + b) r).ennreal_ofReal
  have hgammaPDFa : Measurable (gammaPDF a r) :=
    (measurable_gammaPDFReal a r).ennreal_ofReal
  have hgammaPDFb : Measurable (gammaPDF b r) :=
    (measurable_gammaPDFReal b r).ennreal_ofReal
  have hbetaDensity : Measurable betaDensity := by
    unfold betaDensity
    exact (hbetaPDF.comp measurable_fst).mul
      (hgammaPDFab.comp measurable_snd)
  have hgammaDensity : Measurable gammaDensity := by
    unfold gammaDensity
    exact (hgammaPDFa.comp measurable_fst).mul
      (hgammaPDFb.comp measurable_snd)
  simp only [betaMeasure, gammaMeasure]
  rw [prod_withDensity hbetaPDF hgammaPDFab,
    prod_withDensity hgammaPDFa hgammaPDFb]
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
      · have hpdf : betaPDF a b z.1 = 0 := by
          rcases not_and_or.mp hp' with hp0 | hp1
          · exact betaPDF_eq_zero_of_nonpos (le_of_not_gt hp0)
          · exact betaPDF_eq_zero_of_one_le (le_of_not_gt hp1)
        simp [betaDensity, hpdf, hz]
      · have hpdf : gammaPDF (a + b) r z.2 = 0 :=
          gammaPDF_unequal_eq_zero_of_nonpos hab1 (le_of_not_gt hl')
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
          gammaPDF_unequal_eq_zero_of_nonpos ha (le_of_not_gt hleft)
        simp [gammaDensity, hpdf, hz]
      · have hpdf : gammaPDF b r z.2 = 0 :=
          gammaPDF_unequal_eq_zero_of_nonpos hb (le_of_not_gt hright)
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
              rw [betaGamma_density_identity_unequal
                ha0 hb0 hr hz.1 hz.2]
              simp only [betaGammaComponents]
              ac_rfl
    _ =
      ∫⁻ z in Ioi (0 : ℝ) ×ˢ Ioi 0,
        gammaDensity z * f z := by
          symm
          exact lintegral_betaGammaComponents
            (fun z => gammaDensity z * f z)

private theorem betaMeasure_unequal_ae_mem_Ioo
    {a b : ℝ} :
    ∀ᵐ p : ℝ ∂betaMeasure a b, p ∈ Ioo (0 : ℝ) 1 := by
  unfold betaMeasure betaPDF
  rw [ae_withDensity_iff
    ((measurable_betaPDFReal a b).ennreal_ofReal)]
  filter_upwards [] with p hp
  by_contra hmem
  have hzero : betaPDF a b p = 0 := by
    rcases not_and_or.mp (by simpa only [mem_Ioo] using hmem) with hp0 | hp1
    · exact betaPDF_eq_zero_of_nonpos (le_of_not_gt hp0)
    · exact betaPDF_eq_zero_of_one_le (le_of_not_gt hp1)
  exact hp hzero

private theorem gammaMeasure_unequal_ae_pos
    {a r : ℝ} (ha : 1 < a) :
    ∀ᵐ l : ℝ ∂gammaMeasure a r, 0 < l := by
  unfold gammaMeasure gammaPDF
  rw [ae_withDensity_iff
    ((measurable_gammaPDFReal a r).ennreal_ofReal)]
  filter_upwards [] with l hl
  by_contra hpos
  exact hl
    (gammaPDF_unequal_eq_zero_of_nonpos ha (le_of_not_gt hpos))

/--
The ratio--sum map sends independent gamma measures of shapes `a` and
`b` to `Beta(a,b) × Gamma(a+b,r)`.
-/
theorem map_betaGammaRatioSum_unequal
    {a b r : ℝ} (ha : 1 < a) (hb : 1 < b) (hr : 0 < r) :
    Measure.map betaGammaRatioSum
        ((gammaMeasure a r).prod (gammaMeasure b r))
      =
    (betaMeasure a b).prod (gammaMeasure (a + b) r) := by
  let mu := (betaMeasure a b).prod (gammaMeasure (a + b) r)
  rw [← map_betaGammaComponents_unequal ha hb hr]
  rw [Measure.map_map measurable_betaGammaRatioSum
    measurable_betaGammaComponents]
  have hmu :
      ∀ᵐ z ∂mu, z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioi 0 := by
    letI : IsProbabilityMeasure (gammaMeasure (a + b) r) :=
      isProbabilityMeasure_gammaMeasure (by linarith) hr
    dsimp only [mu]
    rw [Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioo.prod measurableSet_Ioi)]
    filter_upwards [betaMeasure_unequal_ae_mem_Ioo] with p hp
    filter_upwards [gammaMeasure_unequal_ae_pos (a := a + b)
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

/--
Independent `Gamma(a,r)` and `Gamma(b,r)` variables have the joint
ratio/sum law `Beta(a,b) × Gamma(a+b,r)`.
-/
theorem hasLaw_betaGammaRatioSum_of_indep_unequal
    {a b r : ℝ} (ha : 1 < a) (hb : 1 < b) (hr : 0 < r)
    (U₁ U₂ : Ω → ℝ) (mu : Measure Ω) [IsFiniteMeasure mu]
    (hU₁ : HasLaw U₁ (gammaMeasure a r) mu)
    (hU₂ : HasLaw U₂ (gammaMeasure b r) mu)
    (hinde : IndepFun U₁ U₂ mu) :
    HasLaw
      (fun ω => (U₁ ω / (U₁ ω + U₂ ω), U₁ ω + U₂ ω))
      ((betaMeasure a b).prod (gammaMeasure (a + b) r)) mu := by
  have hpair :
      HasLaw (fun ω => (U₁ ω, U₂ ω))
        ((gammaMeasure a r).prod (gammaMeasure b r)) mu :=
    IndepFun.hasLaw_prod hU₁ hU₂ hinde
  have htransform :
      HasLaw betaGammaRatioSum
        ((betaMeasure a b).prod (gammaMeasure (a + b) r))
        ((gammaMeasure a r).prod (gammaMeasure b r)) :=
    { aemeasurable := measurable_betaGammaRatioSum.aemeasurable
      map_eq := map_betaGammaRatioSum_unequal ha hb hr }
  simpa only [Function.comp_apply, betaGammaRatioSum] using
    htransform.fun_comp hpair

/--
The ratio law, sum law, and their independence, extracted from the
unequal-shape joint law.
-/
theorem betaGamma_component_laws_and_indep_unequal
    {a b r : ℝ} (ha : 1 < a) (hb : 1 < b) (hr : 0 < r)
    (U₁ U₂ : Ω → ℝ) (mu : Measure Ω) [IsFiniteMeasure mu]
    (hU₁ : HasLaw U₁ (gammaMeasure a r) mu)
    (hU₂ : HasLaw U₂ (gammaMeasure b r) mu)
    (hinde : IndepFun U₁ U₂ mu) :
    HasLaw (fun ω => U₁ ω / (U₁ ω + U₂ ω))
        (betaMeasure a b) mu
      ∧
    HasLaw (fun ω => U₁ ω + U₂ ω)
        (gammaMeasure (a + b) r) mu
      ∧
    IndepFun
        (fun ω => U₁ ω / (U₁ ω + U₂ ω))
        (fun ω => U₁ ω + U₂ ω) mu := by
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  letI : IsProbabilityMeasure (betaMeasure a b) :=
    isProbabilityMeasureBeta ha0 hb0
  letI : IsProbabilityMeasure (gammaMeasure (a + b) r) :=
    isProbabilityMeasure_gammaMeasure (add_pos ha0 hb0) hr
  have hpair :=
    hasLaw_betaGammaRatioSum_of_indep_unequal ha hb hr
      U₁ U₂ mu hU₁ hU₂ hinde
  have hratio :
      HasLaw (fun ω => U₁ ω / (U₁ ω + U₂ ω))
        (betaMeasure a b) mu := by
    have hfst :
        HasLaw (fun z : ℝ × ℝ => z.1)
          (betaMeasure a b)
          ((betaMeasure a b).prod (gammaMeasure (a + b) r)) :=
      measurePreserving_fst.hasLaw
    simpa only [Function.comp_apply] using hfst.fun_comp hpair
  have hsum :
      HasLaw (fun ω => U₁ ω + U₂ ω)
        (gammaMeasure (a + b) r) mu := by
    have hsnd :
        HasLaw (fun z : ℝ × ℝ => z.2)
          (gammaMeasure (a + b) r)
          ((betaMeasure a b).prod (gammaMeasure (a + b) r)) :=
      measurePreserving_snd.hasLaw
    simpa only [Function.comp_apply] using hsnd.fun_comp hpair
  refine ⟨hratio, hsum, ?_⟩
  apply
    (indepFun_iff_map_prod_eq_prod_map_map
      hratio.aemeasurable hsum.aemeasurable).2
  rw [hpair.map_eq, hratio.map_eq, hsum.map_eq]

end

end GraybillDeal
