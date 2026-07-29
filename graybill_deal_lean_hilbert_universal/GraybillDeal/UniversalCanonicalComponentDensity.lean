import GraybillDeal.UniversalRawReducedDensityLaw
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Density of the canonical risk-tilted component triple

This file proves the deterministic probability calculation which lies
between the tilted product-Gamma law and the three-dimensional reduced
change of variables.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

/-! ## A positive scaling of a Gamma density -/

/-- Real density obtained by sending `x` to `c*x`, for `c > 0`. -/
def gammaPositiveScaleDensity
    (a rate c x : ℝ) : ℝ :=
  c⁻¹ * gammaPDFReal a rate (x / c)

@[measurability, fun_prop]
theorem measurable_gammaPositiveScaleDensity
    (a rate c : ℝ) :
    Measurable (gammaPositiveScaleDensity a rate c) := by
  unfold gammaPositiveScaleDensity
  fun_prop

theorem gammaPositiveScaleDensity_nonneg
    {a rate c : ℝ}
    (ha : 0 < a) (hrate : 0 < rate) (hc : 0 < c)
    (x : ℝ) :
    0 ≤ gammaPositiveScaleDensity a rate c x := by
  unfold gammaPositiveScaleDensity
  exact mul_nonneg (inv_nonneg.mpr hc.le)
    (gammaPDFReal_nonneg ha hrate _)

/-- Exact pushforward density under positive scalar multiplication. -/
theorem gammaMeasure_map_positiveScale
    {a rate c : ℝ} (hc : 0 < c) :
    Measure.map (fun x : ℝ => c * x) (gammaMeasure a rate)
      =
    volume.withDensity
      (fun y => ENNReal.ofReal
        (gammaPositiveScaleDensity a rate c y)) := by
  let Z : ℝ → ℝ := fun x => c * x
  let w : ℝ → ℝ≥0∞ := fun y => gammaPDF a rate (y / c)
  have hZ : Measurable Z := by
    unfold Z
    fun_prop
  have hw : Measurable w := by
    unfold w gammaPDF
    fun_prop
  have hlaw :
      HasLaw Z (ENNReal.ofReal c⁻¹ • volume) volume := by
    refine ⟨hZ.aemeasurable, ?_⟩
    unfold Z
    rw [Real.map_volume_mul_left hc.ne']
    rw [abs_of_pos (inv_pos.mpr hc)]
  have hwcomp :
      (fun x : ℝ => gammaPDF a rate x) = fun x => w (Z x) := by
    funext x
    unfold w Z
    congr 1
    field_simp
  unfold gammaMeasure
  change Measure.map Z
      (volume.withDensity (fun x => gammaPDF a rate x)) = _
  rw [hwcomp]
  calc
    Measure.map Z
        (volume.withDensity (fun x => w (Z x)))
        =
      (ENNReal.ofReal c⁻¹ • volume).withDensity w :=
        GraybillDeal.HasLaw.map_withDensity_comp hlaw w hw
    _ = ENNReal.ofReal c⁻¹ • volume.withDensity w := by
      rw [withDensity_smul_measure]
    _ = volume.withDensity (ENNReal.ofReal c⁻¹ • w) := by
      rw [withDensity_smul (ENNReal.ofReal c⁻¹) hw]
    _ =
      volume.withDensity
        (fun y => ENNReal.ofReal
          (gammaPositiveScaleDensity a rate c y)) := by
      congr 1
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]
      dsimp [w]
      unfold gammaPositiveScaleDensity gammaPDF
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]

/-! ## The three canonical components -/

/-- General shape-parameter version of the component scaling. -/
def universalCanonicalGammaScaling
    (a b : ℝ) (θ : UniversalInteriorTheta)
    (z : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  ((θ : ℝ) * z.2.1 / (2 * a),
    ((1 - (θ : ℝ)) * z.2.2 / (2 * b), z.1))

@[measurability, fun_prop]
theorem measurable_universalCanonicalGammaScaling
    (a b : ℝ) (θ : UniversalInteriorTheta) :
    Measurable (universalCanonicalGammaScaling a b θ) := by
  unfold universalCanonicalGammaScaling
  fun_prop

/-- Product of the three one-dimensional transformed real densities. -/
def universalCanonicalScaledProductDensity
    (a b : ℝ) (θ : UniversalInteriorTheta)
    (z : ℝ × ℝ × ℝ) : ℝ :=
  gammaPositiveScaleDensity a (1 / 2)
      ((θ : ℝ) / (2 * a)) z.1
    * gammaPositiveScaleDensity b (1 / 2)
      ((1 - (θ : ℝ)) / (2 * b)) z.2.1
    * gammaPDFReal (3 / 2) (1 / 2) z.2.2

theorem measurable_universalCanonicalScaledProductDensity
    (a b : ℝ) (θ : UniversalInteriorTheta) :
    Measurable (universalCanonicalScaledProductDensity a b θ) := by
  unfold universalCanonicalScaledProductDensity
  fun_prop

theorem universalCanonicalScaledProductDensity_nonneg
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (z : ℝ × ℝ × ℝ) :
    0 ≤ universalCanonicalScaledProductDensity a b θ z := by
  unfold universalCanonicalScaledProductDensity
  have hc₁ : 0 < (θ : ℝ) / (2 * a) :=
    div_pos θ.property.1 (mul_pos (by norm_num) ha)
  have hc₂ : 0 < (1 - (θ : ℝ)) / (2 * b) := by
    exact div_pos (sub_pos.mpr θ.property.2) (mul_pos (by norm_num) hb)
  exact mul_nonneg
    (mul_nonneg
      (gammaPositiveScaleDensity_nonneg ha (by norm_num) hc₁ _)
      (gammaPositiveScaleDensity_nonneg hb (by norm_num) hc₂ _))
    (gammaPDFReal_nonneg (by norm_num) (by norm_num) _)

/-- Mapping the tilted Gamma product through the canonical scaling gives
the product of its three scalar pushforwards. -/
theorem map_universalCanonicalGammaScaling_riskTiltedMeasure
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta) :
    Measure.map (universalCanonicalGammaScaling a b θ)
      ((gammaMeasure (3 / 2) (1 / 2)).prod
        ((gammaMeasure a (1 / 2)).prod
          (gammaMeasure b (1 / 2))))
      =
    (Measure.map
        (fun u : ℝ => (θ : ℝ) / (2 * a) * u)
        (gammaMeasure a (1 / 2))).prod
      ((Measure.map
          (fun u : ℝ => (1 - (θ : ℝ)) / (2 * b) * u)
          (gammaMeasure b (1 / 2))).prod
        (gammaMeasure (3 / 2) (1 / 2))) := by
  let c₁ : ℝ := (θ : ℝ) / (2 * a)
  let c₂ : ℝ := (1 - (θ : ℝ)) / (2 * b)
  let Mv := gammaMeasure (3 / 2) (1 / 2)
  let M₁ := gammaMeasure a (1 / 2)
  let M₂ := gammaMeasure b (1 / 2)
  letI : SFinite Mv := by
    dsimp [Mv, gammaMeasure]
    infer_instance
  letI : SFinite M₁ := by
    dsimp [M₁, gammaMeasure]
    infer_instance
  letI : SFinite M₂ := by
    dsimp [M₂, gammaMeasure]
    infer_instance
  have hm₁ : Measurable (fun u : ℝ => c₁ * u) := by fun_prop
  have hm₂ : Measurable (fun u : ℝ => c₂ * u) := by fun_prop
  have hid : Measurable (fun x : ℝ => x) := measurable_id
  have hswap :
      Measure.map Prod.swap (Mv.prod (M₁.prod M₂))
        =
      (M₁.prod M₂).prod Mv := by
    exact Measure.prod_swap
  have hscale :
      Measure.map
          (Prod.map (Prod.map (fun u : ℝ => c₁ * u)
            (fun u : ℝ => c₂ * u)) (fun x : ℝ => x))
          ((M₁.prod M₂).prod Mv)
        =
      ((Measure.map (fun u : ℝ => c₁ * u) M₁).prod
        (Measure.map (fun u : ℝ => c₂ * u) M₂)).prod Mv := by
    rw [← Measure.map_prod_map (M₁.prod M₂) Mv
      (hm₁.prodMap hm₂) hid]
    rw [Measure.map_id']
    congr 1
    rw [← Measure.map_prod_map M₁ M₂ hm₁ hm₂]
  have hassoc :
      Measure.map MeasurableEquiv.prodAssoc
          (((Measure.map (fun u : ℝ => c₁ * u) M₁).prod
            (Measure.map (fun u : ℝ => c₂ * u) M₂)).prod Mv)
        =
      (Measure.map (fun u : ℝ => c₁ * u) M₁).prod
        ((Measure.map (fun u : ℝ => c₂ * u) M₂).prod Mv) := by
    exact Measure.prodAssoc_prod
  let G : ((ℝ × ℝ) × ℝ) → (ℝ × (ℝ × ℝ)) :=
    MeasurableEquiv.prodAssoc ∘
      Prod.map (Prod.map (fun u : ℝ => c₁ * u)
        (fun u : ℝ => c₂ * u)) (fun x : ℝ => x)
  have hG : Measurable G := by
    exact MeasurableEquiv.prodAssoc.measurable.comp
      ((hm₁.prodMap hm₂).prodMap hid)
  have hFG :
      universalCanonicalGammaScaling a b θ
        = G ∘ Prod.swap := by
    funext z
    rcases z with ⟨v, u₁, u₂⟩
    apply Prod.ext
    · change (θ : ℝ) * u₁ / (2 * a) = c₁ * u₁
      dsimp [c₁]
      ring
    · apply Prod.ext
      · change (1 - (θ : ℝ)) * u₂ / (2 * b) = c₂ * u₂
        dsimp [c₂]
        ring
      · rfl
  calc
    Measure.map (universalCanonicalGammaScaling a b θ)
        (Mv.prod (M₁.prod M₂))
        =
      Measure.map G
        (Measure.map Prod.swap (Mv.prod (M₁.prod M₂))) := by
          rw [hFG]
          exact (Measure.map_map hG measurable_swap).symm
    _ =
      Measure.map G ((M₁.prod M₂).prod Mv) := by rw [hswap]
    _ =
      Measure.map MeasurableEquiv.prodAssoc
        (Measure.map
          (Prod.map (Prod.map (fun u : ℝ => c₁ * u)
            (fun u : ℝ => c₂ * u)) (fun x : ℝ => x))
          ((M₁.prod M₂).prod Mv)) := by
            exact (Measure.map_map
              MeasurableEquiv.prodAssoc.measurable
              ((hm₁.prodMap hm₂).prodMap hid)).symm
    _ =
      Measure.map MeasurableEquiv.prodAssoc
        (((Measure.map (fun u : ℝ => c₁ * u) M₁).prod
          (Measure.map (fun u : ℝ => c₂ * u) M₂)).prod Mv) := by
            rw [hscale]
    _ =
      (Measure.map (fun u : ℝ => c₁ * u) M₁).prod
        ((Measure.map (fun u : ℝ => c₂ * u) M₂).prod Mv) := hassoc
    _ = _ := by rfl

/-- The canonical triple has the explicit product density obtained by
positive one-dimensional scaling. -/
theorem map_universalCanonicalGammaScaling_eq_scaledProductDensity
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta) :
    Measure.map (universalCanonicalGammaScaling a b θ)
      ((gammaMeasure (3 / 2) (1 / 2)).prod
        ((gammaMeasure a (1 / 2)).prod
          (gammaMeasure b (1 / 2))))
      =
    volume.withDensity
      (fun z => ENNReal.ofReal
        (universalCanonicalScaledProductDensity a b θ z)) := by
  have hc₁ : 0 < (θ : ℝ) / (2 * a) :=
    div_pos θ.property.1 (mul_pos (by norm_num) ha)
  have hc₂ : 0 < (1 - (θ : ℝ)) / (2 * b) := by
    exact div_pos (sub_pos.mpr θ.property.2) (mul_pos (by norm_num) hb)
  rw [map_universalCanonicalGammaScaling_riskTiltedMeasure ha hb θ]
  rw [gammaMeasure_map_positiveScale hc₁,
    gammaMeasure_map_positiveScale hc₂]
  unfold gammaMeasure
  change
    (volume.withDensity
        (fun y => ENNReal.ofReal
          (gammaPositiveScaleDensity a (1 / 2)
            ((θ : ℝ) / (2 * a)) y))).prod
      ((volume.withDensity
          (fun y => ENNReal.ofReal
            (gammaPositiveScaleDensity b (1 / 2)
              ((1 - (θ : ℝ)) / (2 * b)) y))).prod
        (volume.withDensity
          (fun y => ENNReal.ofReal
            (gammaPDFReal (3 / 2) (1 / 2) y))))
      =
    volume.withDensity
      (fun z => ENNReal.ofReal
        (universalCanonicalScaledProductDensity a b θ z))
  rw [prod_withDensity
      (measurable_gammaPositiveScaleDensity _ _ _).ennreal_ofReal
      (measurable_gammaPDFReal _ _).ennreal_ofReal]
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ)]
  have hf₁ :
      Measurable
        (fun y : ℝ => ENNReal.ofReal
          (gammaPositiveScaleDensity a (1 / 2)
            ((θ : ℝ) / (2 * a)) y)) :=
    (measurable_gammaPositiveScaleDensity _ _ _).ennreal_ofReal
  have hf₂₃ :
      Measurable
        (fun z : ℝ × ℝ =>
          ENNReal.ofReal
              (gammaPositiveScaleDensity b (1 / 2)
                ((1 - (θ : ℝ)) / (2 * b)) z.1)
            * ENNReal.ofReal
              (gammaPDFReal (3 / 2) (1 / 2) z.2)) := by
    fun_prop
  rw [prod_withDensity
      (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ).prod (volume : Measure ℝ))
      (f := fun y : ℝ => ENNReal.ofReal
        (gammaPositiveScaleDensity a (1 / 2)
          ((θ : ℝ) / (2 * a)) y))
      (g := fun z : ℝ × ℝ =>
        ENNReal.ofReal
            (gammaPositiveScaleDensity b (1 / 2)
              ((1 - (θ : ℝ)) / (2 * b)) z.1)
          * ENNReal.ofReal
            (gammaPDFReal (3 / 2) (1 / 2) z.2))
      hf₁ hf₂₃]
  congr 1
  funext z
  unfold universalCanonicalScaledProductDensity
  rw [ENNReal.ofReal_mul
    (mul_nonneg
      (gammaPositiveScaleDensity_nonneg ha (by norm_num) hc₁ z.1)
      (gammaPositiveScaleDensity_nonneg hb (by norm_num) hc₂ z.2.1))]
  rw [ENNReal.ofReal_mul
    (gammaPositiveScaleDensity_nonneg ha (by norm_num) hc₁ z.1)]
  simp only [mul_assoc]

end

end GraybillDeal
