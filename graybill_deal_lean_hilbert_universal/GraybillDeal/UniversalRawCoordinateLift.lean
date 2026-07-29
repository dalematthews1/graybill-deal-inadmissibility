import GraybillDeal.UniversalRawRiskTransport
import GraybillDeal.UnequalCochran
import GraybillDeal.UniversalReducedExperiment

/-!
# Almost-everywhere lift of the universal raw coordinates

For arbitrary residual degrees of freedom `ν₁, ν₂ > 0` and positive
population variances, the two estimated sample-mean variances are strictly
positive almost surely.  The mean difference is a nondegenerate Gaussian,
so it is nonzero almost surely.  Consequently the literal raw coordinates

`r = A₁ / (A₁ + A₂)`, `q = D² / (A₁ + A₂)`

belong to the open reduced observation space almost surely.

The final construction replaces the coordinates by `(1/2,1)` on the
exceptional set.  It is measurable everywhere and agrees almost everywhere
with the literal raw coordinates.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory Set

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Every Gamma density is concentrated on the strictly positive half-line.
No restriction such as `1 < a` is needed: the possibly singular value at
zero is irrelevant because `{0}` is Lebesgue-null. -/
theorem gammaMeasure_ae_pos
    (a rate : ℝ) :
    ∀ᵐ x : ℝ ∂gammaMeasure a rate, 0 < x := by
  unfold gammaMeasure gammaPDF
  rw [ae_withDensity_iff
    ((measurable_gammaPDFReal a rate).ennreal_ofReal)]
  have hzero : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hzero] with x hx0 hpdf
  by_contra hx
  have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
  exact hpdf (gammaPDF_of_neg hxneg)

/-- Transport strict positivity through a Gamma distributional identity. -/
theorem ae_pos_of_hasLaw_gammaMeasure
    {P : Measure Ω} {Z : Ω → ℝ} {a rate : ℝ}
    (hZ : HasLaw Z (gammaMeasure a rate) P) :
    ∀ᵐ ω ∂P, 0 < Z ω := by
  rw [hZ.ae_iff (by fun_prop)]
  exact gammaMeasure_ae_pos a rate

namespace TwoNormalSamplesU

variable {ν₁ ν₂ : ℕ}
  {X : Fin (ν₁ + 1) → Ω → ℝ}
  {Y : Fin (ν₂ + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}

/-- The first residual sum of squares is positive almost surely for every
sample size at least two. -/
theorem ae_pos_residualSumSquaresX
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hν₁ : 0 < ν₁) (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P, 0 < residualSumSquaresN ν₁ X ω := by
  have hscaled :
      ∀ᵐ ω ∂P,
        0 < scaledResidualSumSquaresN ν₁ (v₁ : ℝ) X ω :=
    ae_pos_of_hasLaw_gammaMeasure
      (h.hasLaw_scaledResidualSumSquaresX hν₁ hv₁)
  filter_upwards [hscaled] with ω hpos
  have := mul_pos hpos hv₁
  simpa [scaledResidualSumSquaresN, hv₁.ne'] using this

/-- The second residual sum of squares is positive almost surely for every
sample size at least two. -/
theorem ae_pos_residualSumSquaresY
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hν₂ : 0 < ν₂) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P, 0 < residualSumSquaresN ν₂ Y ω := by
  have hscaled :
      ∀ᵐ ω ∂P,
        0 < scaledResidualSumSquaresN ν₂ (v₂ : ℝ) Y ω :=
    ae_pos_of_hasLaw_gammaMeasure
      (h.hasLaw_scaledResidualSumSquaresY hν₂ hv₂)
  filter_upwards [hscaled] with ω hpos
  have := mul_pos hpos hv₂
  simpa [scaledResidualSumSquaresN, hv₂.ne'] using this

theorem ae_pos_universalRawMeanVariance1
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hν₁ : 0 < ν₁) (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P, 0 < universalRawMeanVariance1 ν₁ X ω := by
  filter_upwards [h.ae_pos_residualSumSquaresX hν₁ hv₁] with ω hRSS
  unfold universalRawMeanVariance1 sampleVarianceN
  positivity

theorem ae_pos_universalRawMeanVariance2
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hν₂ : 0 < ν₂) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P, 0 < universalRawMeanVariance2 ν₂ Y ω := by
  filter_upwards [h.ae_pos_residualSumSquaresY hν₂ hv₂] with ω hRSS
  unfold universalRawMeanVariance2 sampleVarianceN
  positivity

theorem ae_pos_universalRawMeanVarianceSum
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P, 0 < universalRawMeanVarianceSum ν₁ ν₂ X Y ω := by
  filter_upwards
    [h.ae_pos_universalRawMeanVariance1 hν₁ hv₁,
      h.ae_pos_universalRawMeanVariance2 hν₂ hv₂] with ω hA₁ hA₂
  exact add_pos hA₁ hA₂

/-- The mean difference is nonzero almost surely because its Gaussian
variance is strictly positive. -/
theorem ae_ne_meanDifferenceU
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P, meanDifferenceU ν₁ ν₂ X Y ω ≠ 0 := by
  let varianceD : NNReal :=
    v₁ / (ν₁ + 1) + v₂ / (ν₂ + 1)
  have hvarianceD : varianceD ≠ 0 := by
    apply ne_of_gt
    exact add_pos
      (div_pos hv₁ (by positivity))
      (div_pos hv₂ (by positivity))
  have hlaw :
      HasLaw (meanDifferenceU ν₁ ν₂ X Y)
        (gaussianReal 0 varianceD) P := by
    simpa [varianceD] using h.hasLaw_meanDifference
  letI : NullSingletonClass (gaussianReal 0 varianceD) :=
    nullSingletonClass_gaussianReal hvarianceD
  apply
    (hlaw.ae_iff (p := fun x : ℝ => x ≠ 0) (by fun_prop)).2
  rw [ae_iff]
  simp

/-- Almost surely, the literal raw coordinates lie in
`(0,1) × (0,∞)`. -/
theorem ae_mem_universalRawReducedCoordinates
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 < (universalRawReducedCoordinates ν₁ ν₂ X Y ω).1 ∧
      (universalRawReducedCoordinates ν₁ ν₂ X Y ω).1 < 1 ∧
      0 < (universalRawReducedCoordinates ν₁ ν₂ X Y ω).2 := by
  filter_upwards
    [h.ae_pos_universalRawMeanVariance1 hν₁ hv₁,
      h.ae_pos_universalRawMeanVariance2 hν₂ hv₂,
      h.ae_ne_meanDifferenceU hv₁ hv₂] with ω hA₁ hA₂ hD
  have hsum : 0 < universalRawMeanVarianceSum ν₁ ν₂ X Y ω := by
    exact add_pos hA₁ hA₂
  constructor
  · exact div_pos hA₁ hsum
  constructor
  · change
      universalRawMeanVariance1 ν₁ X ω
          / universalRawMeanVarianceSum ν₁ ν₂ X Y ω < 1
    rw [div_lt_one hsum]
    unfold universalRawMeanVarianceSum
    linarith
  · exact div_pos (sq_pos_of_ne_zero hD) hsum

end TwoNormalSamplesU

/-! ## An everywhere-defined measurable lift -/

/-- Replace an invalid raw coordinate by the fixed interior point `(1/2,1)`. -/
def universalSafeReducedCoordinates (z : ℝ × ℝ) : ℝ × ℝ :=
  if 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 then z else (1 / 2, 1)

theorem universalSafeReducedCoordinates_property (z : ℝ × ℝ) :
    0 < (universalSafeReducedCoordinates z).1 ∧
      (universalSafeReducedCoordinates z).1 < 1 ∧
      0 < (universalSafeReducedCoordinates z).2 := by
  unfold universalSafeReducedCoordinates
  split_ifs with hz
  · exact hz
  · norm_num

@[measurability, fun_prop]
theorem measurable_universalSafeReducedCoordinates :
    Measurable universalSafeReducedCoordinates := by
  unfold universalSafeReducedCoordinates
  apply Measurable.ite
  · measurability
  · exact measurable_id
  · exact measurable_const

/-- The measurable, everywhere-interior version of the raw reduced
coordinates. -/
def universalRawReducedObservation
    (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) :
    Ω → UniversalReducedObservation :=
  fun ω =>
    ⟨universalSafeReducedCoordinates
        (universalRawReducedCoordinates ν₁ ν₂ X Y ω),
      universalSafeReducedCoordinates_property _⟩

@[measurability, fun_prop]
theorem measurable_universalRawReducedObservation
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j)) :
    Measurable (universalRawReducedObservation ν₁ ν₂ X Y) := by
  apply Measurable.subtype_mk
  exact measurable_universalSafeReducedCoordinates.comp
    (measurable_universalRawReducedCoordinates hX hY)

namespace TwoNormalSamplesU

variable {ν₁ ν₂ : ℕ}
  {X : Fin (ν₁ + 1) → Ω → ℝ}
  {Y : Fin (ν₂ + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}

/-- The measurable lift agrees almost everywhere with the literal pair. -/
theorem ae_coe_universalRawReducedObservation_eq
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    (fun ω => ((universalRawReducedObservation ν₁ ν₂ X Y ω :
      UniversalReducedObservation) : ℝ × ℝ))
      =ᵐ[P] universalRawReducedCoordinates ν₁ ν₂ X Y := by
  filter_upwards
    [h.ae_mem_universalRawReducedCoordinates hν₁ hν₂ hv₁ hv₂] with ω hmem
  simp [universalRawReducedObservation, universalSafeReducedCoordinates, hmem]

end TwoNormalSamplesU

end

end GraybillDeal
