import GraybillDeal.UniversalCanonicalComponentDensity
import GraybillDeal.UniversalGammaPositiveSupport
import GraybillDeal.UniversalNestedDensityBridge

/-!
# Unconditional raw component density identity

This module closes the deterministic assembly point left by
`UniversalRawReducedDensityLaw`.  It identifies the scaled product-Gamma
density with the canonical positive-orthant density, transports the raw
component map to the canonical scaling, and then applies the nested
change-of-variables theorem.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

/-! ## Explicit scalar densities -/

/-- A positive rescaling of a `Gamma(a,1/2)` density in the exact form used
by the canonical weighted density. -/
theorem gammaPositiveScaleDensity_half_eq
    {a t x : ℝ} (ha : 0 < a) (ht : 0 < t) (hx : 0 < x) :
    gammaPositiveScaleDensity a (1 / 2) (t / (2 * a)) x
      =
    a ^ a / Real.Gamma a * t ^ (-a) * x ^ (a - 1)
      * Real.exp (-(a * x / t)) := by
  have hc : 0 < t / (2 * a) := by positivity
  unfold gammaPositiveScaleDensity gammaPDFReal
  rw [if_pos (div_nonneg hx.le hc.le)]
  rw [Real.div_rpow hx.le hc.le]
  have hcombine :
      (t / (2 * a))⁻¹ * (x ^ (a - 1) / (t / (2 * a)) ^ (a - 1))
        =
      x ^ (a - 1) * (t / (2 * a)) ^ (-a) := by
    calc
      (t / (2 * a))⁻¹
          * (x ^ (a - 1) / (t / (2 * a)) ^ (a - 1))
          =
        x ^ (a - 1) *
          ((t / (2 * a))⁻¹
            * ((t / (2 * a)) ^ (a - 1))⁻¹) := by
              rw [div_eq_mul_inv]
              ring
      _ =
        x ^ (a - 1) *
          ((t / (2 * a)) ^ (-1 : ℝ)
            * (t / (2 * a)) ^ (-(a - 1))) := by
              rw [Real.rpow_neg_one]
              rw [Real.rpow_neg hc.le]
      _ = x ^ (a - 1) * (t / (2 * a)) ^ (-a) := by
              congr 1
              rw [← Real.rpow_add hc]
              congr 1
              ring
  rw [show
    (t / (2 * a))⁻¹ *
        ((1 / 2) ^ a / Real.Gamma a *
          (x ^ (a - 1) / (t / (2 * a)) ^ (a - 1)) *
          Real.exp (-((1 / 2) * (x / (t / (2 * a))))))
      =
    ((1 / 2) ^ a / Real.Gamma a)
      * ((t / (2 * a))⁻¹ *
        (x ^ (a - 1) / (t / (2 * a)) ^ (a - 1)))
      * Real.exp (-((1 / 2) * (x / (t / (2 * a))))) by ring]
  rw [hcombine]
  have hscale :
      (1 / 2 : ℝ) ^ a * (t / (2 * a)) ^ (-a)
        = a ^ a * t ^ (-a) := by
    rw [Real.rpow_neg (div_nonneg ht.le (by positivity)) a]
    rw [Real.div_rpow ht.le (by positivity) a]
    rw [inv_div]
    have hprod :
        (1 / 2 : ℝ) ^ a * (2 * a) ^ a = a ^ a := by
      rw [← Real.mul_rpow (by norm_num : 0 ≤ (1 / 2 : ℝ))
        (by positivity : 0 ≤ 2 * a)]
      congr 1
      ring
    rw [Real.rpow_neg ht.le]
    rw [div_eq_mul_inv]
    calc
      (1 / 2 : ℝ) ^ a * ((2 * a) ^ a * (t ^ a)⁻¹)
          =
        ((1 / 2 : ℝ) ^ a * (2 * a) ^ a) * (t ^ a)⁻¹ := by
            ring
      _ = a ^ a * (t ^ a)⁻¹ := by rw [hprod]
  rw [show
    (1 / 2 : ℝ) ^ a / Real.Gamma a
        * (x ^ (a - 1) * (t / (2 * a)) ^ (-a))
      =
    ((1 / 2 : ℝ) ^ a * (t / (2 * a)) ^ (-a))
      / Real.Gamma a * x ^ (a - 1) by ring]
  rw [hscale]
  have hexp :
      (1 / 2 : ℝ) * (x / (t / (2 * a))) = a * x / t := by
    field_simp [ha.ne', ht.ne']
  rw [hexp]
  ring

/-- The risk-tilted standardized squared difference has the elementary
`Gamma(3/2,1/2)` density constant `1/sqrt(2π)`. -/
theorem gammaPDFReal_three_half_half_eq
    {x : ℝ} (hx : 0 < x) :
    gammaPDFReal (3 / 2) (1 / 2) x
      =
    1 / Real.sqrt (2 * Real.pi)
      * x ^ (1 / 2 : ℝ) * Real.exp (-(x / 2)) := by
  rw [gammaPDFReal, if_pos hx.le]
  have hΓ :
      Real.Gamma (3 / 2 : ℝ)
        = (1 / 2 : ℝ) * Real.sqrt Real.pi := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num]
    rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    rw [Real.Gamma_one_half_eq]
  rw [hΓ]
  have hcoef :
      (1 / 2 : ℝ) ^ (3 / 2 : ℝ)
          / ((1 / 2 : ℝ) * Real.sqrt Real.pi)
        =
      1 / Real.sqrt (2 * Real.pi) := by
    have hπ : 0 < Real.pi := Real.pi_pos
    have hsqrtπ : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 hπ).ne'
    have hsqrt2 : Real.sqrt (2 : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 (by norm_num)).ne'
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
    rw [Real.rpow_add (by norm_num : 0 < (1 / 2 : ℝ))]
    rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [Real.sqrt_div (by norm_num : 0 ≤ (1 : ℝ))]
    rw [Real.sqrt_one]
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
    field_simp [hsqrtπ, hsqrt2]
  rw [hcoef]
  ring_nf

/-- On the positive canonical orthant, the product of the three transformed
Gamma densities is exactly the analytic density used by the radial bridge. -/
theorem universalCanonicalScaledProductDensity_eq_weighted
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    {z : ℝ × ℝ × ℝ}
    (hz : z ∈ universalCanonicalPositiveTarget) :
    universalCanonicalScaledProductDensity a b θ z
      =
    universalCanonicalWeightedTripleDensity a b θ z := by
  rcases hz with ⟨hg₁, hg₂, hw⟩
  change 0 < z.1 at hg₁
  change 0 < z.2.1 at hg₂
  change 0 < z.2.2 at hw
  unfold universalCanonicalScaledProductDensity
  rw [gammaPositiveScaleDensity_half_eq ha θ.property.1 hg₁]
  rw [gammaPositiveScaleDensity_half_eq
    hb (sub_pos.mpr θ.property.2) hg₂]
  rw [gammaPDFReal_three_half_half_eq hw]
  unfold universalCanonicalWeightedTripleDensity
  have hexp :
      Real.exp (-(a * z.1 / (θ : ℝ)))
          * Real.exp (-(b * z.2.1 / (1 - (θ : ℝ))))
          * Real.exp (-(z.2.2 / 2))
        =
      Real.exp
        (-(a * z.1 / (θ : ℝ)
          + b * z.2.1 / (1 - (θ : ℝ))
          + z.2.2 / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    a ^ a / Real.Gamma a * (θ : ℝ) ^ (-a)
          * z.1 ^ (a - 1) * Real.exp (-(a * z.1 / (θ : ℝ)))
        * (b ^ b / Real.Gamma b * (1 - (θ : ℝ)) ^ (-b)
          * z.2.1 ^ (b - 1)
          * Real.exp (-(b * z.2.1 / (1 - (θ : ℝ)))))
        * (1 / Real.sqrt (2 * Real.pi) * z.2.2 ^ (1 / 2 : ℝ)
          * Real.exp (-(z.2.2 / 2)))
        =
      (a ^ a * b ^ b
          / (Real.sqrt (2 * Real.pi) * Real.Gamma a * Real.Gamma b)
        * (θ : ℝ) ^ (-a)
        * (1 - (θ : ℝ)) ^ (-b)
        * z.1 ^ (a - 1)
        * z.2.1 ^ (b - 1)
        * z.2.2 ^ (1 / 2 : ℝ))
        *
      (Real.exp (-(a * z.1 / (θ : ℝ)))
        * Real.exp (-(b * z.2.1 / (1 - (θ : ℝ))))
        * Real.exp (-(z.2.2 / 2))) := by ring
    _ = _ := by rw [hexp]

theorem universalRawComponentsToCanonical_eq_gammaScaling
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    {v₁ v₂ : NNReal} (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) :
    universalRawComponentsToCanonical ν₁ ν₂ v₁ v₂
      =
    universalCanonicalGammaScaling
      ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2)
      (universalRawOracleInteriorTheta
        ν₁ ν₂ v₁ v₂ hv₁ hv₂) := by
  funext z
  unfold universalRawComponentsToCanonical
    universalCanonicalGammaScaling
  simp only [universalRawOracleInteriorTheta_coe]
  have hν₁r : (ν₁ : ℝ) ≠ 0 := by exact_mod_cast hν₁.ne'
  have hν₂r : (ν₂ : ℝ) ≠ 0 := by exact_mod_cast hν₂.ne'
  apply Prod.ext
  · dsimp only
    field_simp
  · apply Prod.ext
    · dsimp only
      field_simp
    · rfl

theorem universalCanonicalReducedPair_eq_nested
    (z : ℝ × ℝ × ℝ) :
    universalCanonicalReducedPair z
      = universalCanonicalReducedPairNested z := by
  rfl

theorem universalRawSafeObservation_eq_nested_on_positive
    (z : ℝ × ℝ × ℝ)
    (hz : z ∈ universalCanonicalPositiveTarget) :
    (⟨universalSafeReducedCoordinates
        (universalCanonicalReducedPair z),
      universalSafeReducedCoordinates_property _⟩ :
        UniversalReducedObservation)
      =
    universalCanonicalToReducedObservationNested z := by
  apply Subtype.ext
  change
    universalSafeReducedCoordinates (universalCanonicalReducedPair z)
      =
    (universalSafeReducedObservation
      (universalCanonicalReducedPairNested z) : ℝ × ℝ)
  rw [universalSafeReducedObservation_of_mem
    (universalCanonicalReducedPairNested_mem hz)]
  rw [universalCanonicalReducedPair_eq_nested]
  unfold universalSafeReducedCoordinates
  rw [if_pos]
  have hm := universalCanonicalReducedPairNested_mem hz
  exact ⟨hm.1.1, hm.1.2, hm.2⟩

/-! ## Support and measure identities -/

theorem universalRawComponentsToCanonical_mem_positive
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    {v₁ v₂ : NNReal} (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    {z : ℝ × ℝ × ℝ}
    (hz : 0 < z.1 ∧ 0 < z.2.1 ∧ 0 < z.2.2) :
    universalRawComponentsToCanonical ν₁ ν₂ v₁ v₂ z
      ∈ universalCanonicalPositiveTarget := by
  unfold universalRawComponentsToCanonical
    universalCanonicalPositiveTarget
  change
    0 < universalRawOracleTheta ν₁ ν₂ v₁ v₂ * z.2.1 / (ν₁ : ℝ) ∧
      0 < (1 - universalRawOracleTheta ν₁ ν₂ v₁ v₂)
          * z.2.2 / (ν₂ : ℝ) ∧
      0 < z.1
  exact
    ⟨div_pos
        (mul_pos (universalRawOracleTheta_pos ν₁ ν₂ hv₁ hv₂) hz.2.1)
        (Nat.cast_pos.mpr hν₁),
      div_pos
        (mul_pos
          (sub_pos.mpr
            (universalRawOracleTheta_lt_one ν₁ ν₂ hv₁ hv₂))
          hz.2.2)
        (Nat.cast_pos.mpr hν₂),
      hz.1⟩

theorem universalRawComponentsReducedObservation_eq_nested_on_positive
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    {v₁ v₂ : NNReal} (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    {z : ℝ × ℝ × ℝ}
    (hz : 0 < z.1 ∧ 0 < z.2.1 ∧ 0 < z.2.2) :
    universalRawComponentsReducedObservation ν₁ ν₂ v₁ v₂ z
      =
    universalCanonicalToReducedObservationNested
      (universalRawComponentsToCanonical ν₁ ν₂ v₁ v₂ z) := by
  unfold universalRawComponentsReducedObservation
  exact universalRawSafeObservation_eq_nested_on_positive _
    (universalRawComponentsToCanonical_mem_positive
      hν₁ hν₂ hv₁ hv₂ hz)

/-- The restriction of the scaled product density to its open support is
the canonical weighted-density measure used by the radial bridge. -/
theorem
    universalCanonicalScaledProductDensity_restrict_eq_weightedMeasure
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta) :
    (volume.withDensity
        (fun z : ℝ × ℝ × ℝ =>
          ENNReal.ofReal
            (universalCanonicalScaledProductDensity a b θ z))).restrict
        universalCanonicalPositiveTarget
      =
    ((volume : Measure (ℝ × ℝ × ℝ)).restrict
        universalCanonicalPositiveTarget).withDensity
      (fun z =>
        ENNReal.ofReal
          (universalCanonicalWeightedTripleDensity a b θ z)) := by
  rw [restrict_withDensity
    measurableSet_universalCanonicalPositiveTarget]
  apply withDensity_congr_ae
  filter_upwards
    [self_mem_ae_restrict
      measurableSet_universalCanonicalPositiveTarget] with z hz
  rw [universalCanonicalScaledProductDensity_eq_weighted ha hb θ hz]

/-- The exact density of the oracle-scaled risk-tilted component triple. -/
theorem
    map_universalRawComponentsToCanonical_eq_scaledProductDensity
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    {v₁ v₂ : NNReal} (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) :
    Measure.map
        (universalRawComponentsToCanonical ν₁ ν₂ v₁ v₂)
        (universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂)
      =
    volume.withDensity
      (fun z =>
        ENNReal.ofReal
          (universalCanonicalScaledProductDensity
            ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2)
            (universalRawOracleInteriorTheta
              ν₁ ν₂ v₁ v₂ hv₁ hv₂) z)) := by
  have ha : 0 < (ν₁ : ℝ) / 2 := by positivity
  have hb : 0 < (ν₂ : ℝ) / 2 := by positivity
  rw [universalRawComponentsToCanonical_eq_gammaScaling
    hν₁ hν₂ hv₁ hv₂]
  unfold universalRawRiskTiltedIndependentComponentMeasure
  exact
    map_universalCanonicalGammaScaling_eq_scaledProductDensity
      ha hb
      (universalRawOracleInteriorTheta
        ν₁ ν₂ v₁ v₂ hv₁ hv₂)

/-! ## Final component-to-reduced law -/

/-- For every pair of positive residual degrees of freedom and positive
population variances, the risk-tilted component image has the universal
reduced density.  This discharges the deterministic hypothesis in
`UniversalRawReducedDensityLaw`. -/
theorem universalRiskTiltedComponentReducedDensityIdentity
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    {v₁ v₂ : NNReal} (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) :
    UniversalRiskTiltedComponentReducedDensityIdentity
      ν₁ ν₂ v₁ v₂ hv₁ hv₂ := by
  let a : ℝ := (ν₁ : ℝ) / 2
  let b : ℝ := (ν₂ : ℝ) / 2
  let θ : UniversalInteriorTheta :=
    universalRawOracleInteriorTheta
      ν₁ ν₂ v₁ v₂ hv₁ hv₂
  let μ : Measure (ℝ × ℝ × ℝ) :=
    universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂
  let C : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) :=
    universalRawComponentsToCanonical ν₁ ν₂ v₁ v₂
  let F : (ℝ × ℝ × ℝ) → UniversalReducedObservation :=
    universalCanonicalToReducedObservationNested
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hμpos :
      ∀ᵐ z ∂μ, 0 < z.1 ∧ 0 < z.2.1 ∧ 0 < z.2.2 := by
    exact
      universalRawRiskTiltedIndependentComponentMeasure_ae_pos
        hν₁ hν₂
  have hobs :
      universalRawComponentsReducedObservation ν₁ ν₂ v₁ v₂
        =ᵐ[μ]
      F ∘ C := by
    filter_upwards [hμpos] with z hz
    exact
      universalRawComponentsReducedObservation_eq_nested_on_positive
        hν₁ hν₂ hv₁ hv₂ hz
  have hC : Measurable C :=
    measurable_universalRawComponentsToCanonical ν₁ ν₂ v₁ v₂
  have hF : Measurable F :=
    measurable_universalCanonicalToReducedObservationNested
  have hClaw :
      Measure.map C μ
        =
      volume.withDensity
        (fun z =>
          ENNReal.ofReal
            (universalCanonicalScaledProductDensity a b θ z)) := by
    exact
      map_universalRawComponentsToCanonical_eq_scaledProductDensity
        hν₁ hν₂ hv₁ hv₂
  have hCpos :
      ∀ᵐ y ∂Measure.map C μ,
        y ∈ universalCanonicalPositiveTarget := by
    apply
      (ae_map_iff hC.aemeasurable
        measurableSet_universalCanonicalPositiveTarget).2
    exact hμpos.mono (fun _ hz =>
      universalRawComponentsToCanonical_mem_positive
        hν₁ hν₂ hv₁ hv₂ hz)
  have hsupp :
      (volume.withDensity
          (fun z : ℝ × ℝ × ℝ =>
            ENNReal.ofReal
              (universalCanonicalScaledProductDensity a b θ z))).restrict
          universalCanonicalPositiveTarget
        =
      volume.withDensity
        (fun z =>
          ENNReal.ofReal
            (universalCanonicalScaledProductDensity a b θ z)) := by
    have hrestrict :
        (Measure.map C μ).restrict universalCanonicalPositiveTarget
          =
        Measure.map C μ :=
      Measure.restrict_eq_self_of_ae_mem hCpos
    rwa [hClaw] at hrestrict
  have hcanonicalMeasure :
      volume.withDensity
          (fun z : ℝ × ℝ × ℝ =>
            ENNReal.ofReal
              (universalCanonicalScaledProductDensity a b θ z))
        =
      ((volume : Measure (ℝ × ℝ × ℝ)).restrict
          universalCanonicalPositiveTarget).withDensity
        (fun z =>
          ENNReal.ofReal
            (universalCanonicalWeightedTripleDensity a b θ z)) := by
    calc
      volume.withDensity
          (fun z : ℝ × ℝ × ℝ =>
            ENNReal.ofReal
              (universalCanonicalScaledProductDensity a b θ z))
          =
        (volume.withDensity
            (fun z : ℝ × ℝ × ℝ =>
              ENNReal.ofReal
                (universalCanonicalScaledProductDensity a b θ z))).restrict
            universalCanonicalPositiveTarget := hsupp.symm
      _ =
        ((volume : Measure (ℝ × ℝ × ℝ)).restrict
            universalCanonicalPositiveTarget).withDensity
          (fun z =>
            ENNReal.ofReal
              (universalCanonicalWeightedTripleDensity a b θ z)) :=
        universalCanonicalScaledProductDensity_restrict_eq_weightedMeasure
          ha hb θ
  unfold UniversalRiskTiltedComponentReducedDensityIdentity
  rw [Measure.map_congr hobs]
  rw [← Measure.map_map hF hC]
  rw [hClaw]
  rw [hcanonicalMeasure]
  exact map_canonicalWeightedTripleDensity_eq_reducedDensity ha hb θ

end

end GraybillDeal
