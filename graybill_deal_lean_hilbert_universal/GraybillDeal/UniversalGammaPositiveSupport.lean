import GraybillDeal.UniversalRawComponentLaws
import GraybillDeal.UniversalReducedChangeOfVariables

/-!
# Positive support of the universal Gamma components

Gamma densities with positive shape and rate are concentrated on the
strictly positive half-line.  This remains true for shapes at or below
one: although the usual real density formula is singular at zero, the
singleton `{0}` is Lebesgue-null.

This file packages that fact as reusable restriction identities, lifts it
to right-associated products of three Gamma measures, and transports it
through the positive coordinate scalings used by the universal raw
reduction.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

/-! ## One-dimensional Gamma support -/

/-- A Gamma law with arbitrary positive shape and rate is concentrated on
`(0,∞)`.  The separate Lebesgue-a.e. exclusion of zero is the step which
makes this valid for shape `1/2`. -/
theorem gammaMeasure_ae_mem_Ioi_of_pos
    {a rate : ℝ} (_ha : 0 < a) (_hrate : 0 < rate) :
    ∀ᵐ x : ℝ ∂gammaMeasure a rate, x ∈ Ioi 0 := by
  unfold gammaMeasure gammaPDF
  rw [ae_withDensity_iff
    ((measurable_gammaPDFReal a rate).ennreal_ofReal)]
  have hzero : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hzero] with x hx0 hpdf
  by_contra hx
  have hxneg : x < 0 :=
    lt_of_le_of_ne (le_of_not_gt hx) hx0
  exact hpdf (gammaPDF_of_neg hxneg)

/-- Restricting a positive-parameter Gamma law to `(0,∞)` does not change
the measure. -/
theorem gammaMeasure_restrict_Ioi_eq_self
    {a rate : ℝ} (ha : 0 < a) (hrate : 0 < rate) :
    (gammaMeasure a rate).restrict (Ioi 0)
      =
    gammaMeasure a rate :=
  Measure.restrict_eq_self_of_ae_mem
    (gammaMeasure_ae_mem_Ioi_of_pos ha hrate)

/-- Equivalent orientation of `gammaMeasure_restrict_Ioi_eq_self`. -/
theorem gammaMeasure_eq_restrict_Ioi
    {a rate : ℝ} (ha : 0 < a) (hrate : 0 < rate) :
    gammaMeasure a rate
      =
    (gammaMeasure a rate).restrict (Ioi 0) :=
  (gammaMeasure_restrict_Ioi_eq_self ha hrate).symm

/-- The nonpositive half-line is Gamma-null. -/
theorem gammaMeasure_Iic_zero
    {a rate : ℝ} (ha : 0 < a) (hrate : 0 < rate) :
    gammaMeasure a rate (Iic 0) = 0 := by
  have hpos := gammaMeasure_ae_mem_Ioi_of_pos ha hrate
  rw [ae_iff] at hpos
  have hcompl : {x : ℝ | x ∉ Ioi 0} = Iic 0 := by
    ext x
    simp
  rw [hcompl] at hpos
  exact hpos

/-! ## Nested products -/

/-- Right-associated product of three Gamma measures. -/
def universalGammaTripleMeasure
    (a₀ rate₀ a₁ rate₁ a₂ rate₂ : ℝ) :
    Measure (ℝ × ℝ × ℝ) :=
  (gammaMeasure a₀ rate₀).prod
    ((gammaMeasure a₁ rate₁).prod
      (gammaMeasure a₂ rate₂))

/-- A product of three positive-parameter Gamma laws is concentrated on
the positive orthant. -/
theorem universalGammaTripleMeasure_ae_mem_positiveTarget
    {a₀ rate₀ a₁ rate₁ a₂ rate₂ : ℝ}
    (ha₀ : 0 < a₀) (hrate₀ : 0 < rate₀)
    (ha₁ : 0 < a₁) (hrate₁ : 0 < rate₁)
    (ha₂ : 0 < a₂) (hrate₂ : 0 < rate₂) :
    ∀ᵐ z ∂universalGammaTripleMeasure
        a₀ rate₀ a₁ rate₁ a₂ rate₂,
      z ∈ universalCanonicalPositiveTarget := by
  letI : IsProbabilityMeasure (gammaMeasure a₀ rate₀) :=
    isProbabilityMeasure_gammaMeasure ha₀ hrate₀
  letI : IsProbabilityMeasure (gammaMeasure a₁ rate₁) :=
    isProbabilityMeasure_gammaMeasure ha₁ hrate₁
  letI : IsProbabilityMeasure (gammaMeasure a₂ rate₂) :=
    isProbabilityMeasure_gammaMeasure ha₂ hrate₂
  have hpair :
      ∀ᵐ yz
        ∂(gammaMeasure a₁ rate₁).prod
          (gammaMeasure a₂ rate₂),
        yz ∈ Ioi (0 : ℝ) ×ˢ Ioi 0 := by
    rw [Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioi.prod measurableSet_Ioi)]
    filter_upwards
      [gammaMeasure_ae_mem_Ioi_of_pos ha₁ hrate₁] with y hy
    filter_upwards
      [gammaMeasure_ae_mem_Ioi_of_pos ha₂ hrate₂] with z hz
    exact ⟨hy, hz⟩
  unfold universalGammaTripleMeasure
    universalCanonicalPositiveTarget
  rw [Measure.ae_prod_mem_iff_ae_ae_mem
    (measurableSet_Ioi.prod
      (measurableSet_Ioi.prod measurableSet_Ioi))]
  filter_upwards
    [gammaMeasure_ae_mem_Ioi_of_pos ha₀ hrate₀] with x hx
  exact hpair.mono (fun _ hyz => ⟨hx, hyz⟩)

/-- Restricting a three-Gamma product to the positive orthant does not
change it. -/
theorem universalGammaTripleMeasure_restrict_positiveTarget_eq_self
    {a₀ rate₀ a₁ rate₁ a₂ rate₂ : ℝ}
    (ha₀ : 0 < a₀) (hrate₀ : 0 < rate₀)
    (ha₁ : 0 < a₁) (hrate₁ : 0 < rate₁)
    (ha₂ : 0 < a₂) (hrate₂ : 0 < rate₂) :
    (universalGammaTripleMeasure
        a₀ rate₀ a₁ rate₁ a₂ rate₂).restrict
          universalCanonicalPositiveTarget
      =
    universalGammaTripleMeasure
      a₀ rate₀ a₁ rate₁ a₂ rate₂ :=
  Measure.restrict_eq_self_of_ae_mem
    (universalGammaTripleMeasure_ae_mem_positiveTarget
      ha₀ hrate₀ ha₁ hrate₁ ha₂ hrate₂)

/-! ## The risk-tilted component law -/

/-- The exact risk-tilted component product `(V,U₁,U₂)` is positive
almost everywhere for every pair of positive residual degrees of freedom.
In particular the first shape `3/2` and the un-tilted half-shape appearing
upstream present no endpoint problem. -/
theorem universalRawRiskTiltedIndependentComponentMeasure_ae_pos
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂) :
    ∀ᵐ z ∂universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂,
      0 < z.1 ∧ 0 < z.2.1 ∧ 0 < z.2.2 := by
  change
    ∀ᵐ z
      ∂universalGammaTripleMeasure
        (3 / 2) (1 / 2)
        ((ν₁ : ℝ) / 2) (1 / 2)
        ((ν₂ : ℝ) / 2) (1 / 2),
      z ∈ universalCanonicalPositiveTarget
  apply universalGammaTripleMeasure_ae_mem_positiveTarget
  · norm_num
  · norm_num
  · positivity
  · norm_num
  · positivity
  · norm_num

theorem
    universalRawRiskTiltedIndependentComponentMeasure_restrict_positiveTarget_eq_self
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂) :
    (universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂).restrict
        universalCanonicalPositiveTarget
      =
    universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂ :=
  Measure.restrict_eq_self_of_ae_mem
    (universalRawRiskTiltedIndependentComponentMeasure_ae_pos hν₁ hν₂)

/-! ## Positive scaled pushforwards -/

/-- Reorder `(V,U₁,U₂)` to `(c₁U₁,c₂U₂,c₀V)`. -/
def universalGammaComponentsToCanonical
    (c₁ c₂ c₀ : ℝ) (z : ℝ × ℝ × ℝ) :
    ℝ × ℝ × ℝ :=
  (c₁ * z.2.1, (c₂ * z.2.2, c₀ * z.1))

@[measurability, fun_prop]
theorem measurable_universalGammaComponentsToCanonical
    (c₁ c₂ c₀ : ℝ) :
    Measurable (universalGammaComponentsToCanonical c₁ c₂ c₀) := by
  unfold universalGammaComponentsToCanonical
  fun_prop

/-- Positive coordinate scaling and reordering preserves concentration on
the positive orthant. -/
theorem map_universalGammaComponentsToCanonical_ae_mem_positiveTarget
    {μ : Measure (ℝ × ℝ × ℝ)}
    {c₁ c₂ c₀ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₀ : 0 < c₀)
    (hμ :
      ∀ᵐ z ∂μ, 0 < z.1 ∧ 0 < z.2.1 ∧ 0 < z.2.2) :
    ∀ᵐ y
      ∂Measure.map
        (universalGammaComponentsToCanonical c₁ c₂ c₀) μ,
      y ∈ universalCanonicalPositiveTarget := by
  unfold universalCanonicalPositiveTarget
  apply
    (ae_map_iff
      (measurable_universalGammaComponentsToCanonical
        c₁ c₂ c₀).aemeasurable
      (measurableSet_Ioi.prod
        (measurableSet_Ioi.prod measurableSet_Ioi))).2
  filter_upwards [hμ] with z hz
  exact
    ⟨mul_pos hc₁ hz.2.1,
      mul_pos hc₂ hz.2.2,
      mul_pos hc₀ hz.1⟩

/-- Restriction form of the preceding scaled-pushforward support lemma. -/
theorem
    map_universalGammaComponentsToCanonical_restrict_positiveTarget_eq_self
    {μ : Measure (ℝ × ℝ × ℝ)}
    {c₁ c₂ c₀ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₀ : 0 < c₀)
    (hμ :
      ∀ᵐ z ∂μ, 0 < z.1 ∧ 0 < z.2.1 ∧ 0 < z.2.2) :
    (Measure.map
        (universalGammaComponentsToCanonical c₁ c₂ c₀) μ).restrict
          universalCanonicalPositiveTarget
      =
    Measure.map
      (universalGammaComponentsToCanonical c₁ c₂ c₀) μ :=
  Measure.restrict_eq_self_of_ae_mem
    (map_universalGammaComponentsToCanonical_ae_mem_positiveTarget
      hc₁ hc₂ hc₀ hμ)

/-- Concrete concentration statement for the risk-tilted component law
after arbitrary positive canonical scalings. -/
theorem
    map_universalRawRiskTiltedComponents_ae_mem_positiveTarget
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    {c₁ c₂ c₀ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₀ : 0 < c₀) :
    ∀ᵐ y
      ∂Measure.map
        (universalGammaComponentsToCanonical c₁ c₂ c₀)
        (universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂),
      y ∈ universalCanonicalPositiveTarget :=
  map_universalGammaComponentsToCanonical_ae_mem_positiveTarget
    hc₁ hc₂ hc₀
    (universalRawRiskTiltedIndependentComponentMeasure_ae_pos
      hν₁ hν₂)

theorem
    map_universalRawRiskTiltedComponents_restrict_positiveTarget_eq_self
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    {c₁ c₂ c₀ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₀ : 0 < c₀) :
    (Measure.map
        (universalGammaComponentsToCanonical c₁ c₂ c₀)
        (universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂)).restrict
          universalCanonicalPositiveTarget
      =
    Measure.map
      (universalGammaComponentsToCanonical c₁ c₂ c₀)
      (universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂) :=
  Measure.restrict_eq_self_of_ae_mem
    (map_universalRawRiskTiltedComponents_ae_mem_positiveTarget
      hν₁ hν₂ hc₁ hc₂ hc₀)

/-! ## Exact oracle scaling used by the raw reduction -/

/-- Exact canonical scaling
`(V,U₁,U₂) ↦ (θ U₁/ν₁, (1-θ) U₂/ν₂, V)`. -/
def universalGammaOracleComponentsToCanonical
    (ν₁ ν₂ : ℕ) (θ : ℝ)
    (z : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (θ * z.2.1 / ν₁,
    ((1 - θ) * z.2.2 / ν₂, z.1))

@[measurability, fun_prop]
theorem measurable_universalGammaOracleComponentsToCanonical
    (ν₁ ν₂ : ℕ) (θ : ℝ) :
    Measurable
      (universalGammaOracleComponentsToCanonical ν₁ ν₂ θ) := by
  unfold universalGammaOracleComponentsToCanonical
  fun_prop

/-- The exact oracle-scaled risk-tilted law is concentrated on the
canonical positive target. -/
theorem
    map_universalGammaOracleComponentsToCanonical_ae_mem_positiveTarget
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (θ : UniversalInteriorTheta) :
    ∀ᵐ y
      ∂Measure.map
        (universalGammaOracleComponentsToCanonical
          ν₁ ν₂ (θ : ℝ))
        (universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂),
      y ∈ universalCanonicalPositiveTarget := by
  apply
    (ae_map_iff
      (measurable_universalGammaOracleComponentsToCanonical
        ν₁ ν₂ (θ : ℝ)).aemeasurable
      (measurableSet_Ioi.prod
        (measurableSet_Ioi.prod measurableSet_Ioi))).2
  filter_upwards
    [universalRawRiskTiltedIndependentComponentMeasure_ae_pos
      hν₁ hν₂] with z hz
  change
    0 < (θ : ℝ) * z.2.1 / (ν₁ : ℝ) ∧
      0 < (1 - (θ : ℝ)) * z.2.2 / (ν₂ : ℝ) ∧
      0 < z.1
  exact
    ⟨div_pos (mul_pos θ.property.1 hz.2.1)
        (Nat.cast_pos.mpr hν₁),
      div_pos (mul_pos (sub_pos.mpr θ.property.2) hz.2.2)
        (Nat.cast_pos.mpr hν₂),
      hz.1⟩

theorem
    map_universalGammaOracleComponentsToCanonical_restrict_positiveTarget_eq_self
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (θ : UniversalInteriorTheta) :
    (Measure.map
        (universalGammaOracleComponentsToCanonical
          ν₁ ν₂ (θ : ℝ))
        (universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂)).restrict
          universalCanonicalPositiveTarget
      =
    Measure.map
      (universalGammaOracleComponentsToCanonical
        ν₁ ν₂ (θ : ℝ))
      (universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂) :=
  Measure.restrict_eq_self_of_ae_mem
    (map_universalGammaOracleComponentsToCanonical_ae_mem_positiveTarget
      hν₁ hν₂ θ)

end

end GraybillDeal
