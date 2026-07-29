import GraybillDeal.RawNormalSummary

/-!
# Almost-sure positivity of the raw variance coordinates

This file discharges the nonvanishing assumptions in `RawCoordinates.lean`
from the fixed-size Cochran laws.  A `Gamma(6, 1 / 2)` variable is strictly
positive almost surely, so both raw sample variances, their sum, and the
standardized residual sum coordinate are nonzero almost surely.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory Set

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `Gamma(6, 1 / 2)` law is concentrated on the strictly positive reals. -/
theorem gammaMeasure_six_half_ae_pos :
    ∀ᵐ x ∂gammaMeasure 6 (1 / 2), 0 < x := by
  rw [ae_iff]
  rw [show {x : ℝ | ¬ 0 < x} = Iic 0 by ext x; simp]
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iic]
  rw [setLIntegral_congr_fun (g := fun _ => 0) measurableSet_Iic]
  · simp
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      norm_num [gammaPDF, gammaPDFReal]
    · exact gammaPDF_of_neg (lt_of_le_of_ne hx hx0)

/-- Any random variable with the `Gamma(6, 1 / 2)` law is positive a.s. -/
theorem ae_pos_of_hasLaw_gammaMeasure_six_half
    {P : Measure Ω} {Y : Ω → ℝ}
    (hY : HasLaw Y (gammaMeasure 6 (1 / 2)) P) :
    ∀ᵐ ω ∂P, 0 < Y ω := by
  rw [hY.ae_iff (by fun_prop)]
  exact gammaMeasure_six_half_ae_pos

namespace TwoNormalSamples13

variable {X : Fin 2 → Fin 13 → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}

/-- Each standardized residual sum of squares is strictly positive a.s. -/
theorem ae_pos_scaledResidualSumSquares13
    (h : TwoNormalSamples13 X P μ variance)
    (g : Fin 2) (hv : 0 < (variance g : ℝ)) :
    ∀ᵐ ω ∂P,
      0 < scaledResidualSumSquares13 (variance g) (X g) ω :=
  ae_pos_of_hasLaw_gammaMeasure_six_half
    (h.hasLaw_scaledResidualSumSquares13 g hv)

/-- Each raw residual sum of squares is strictly positive a.s. -/
theorem ae_pos_residualSumSquares13
    (h : TwoNormalSamples13 X P μ variance)
    (g : Fin 2) (hv : 0 < (variance g : ℝ)) :
    ∀ᵐ ω ∂P, 0 < residualSumSquares13 (X g) ω := by
  filter_upwards [h.ae_pos_scaledResidualSumSquares13 g hv] with ω hU
  have hmul :
      0 <
        scaledResidualSumSquares13 (variance g) (X g) ω
          * (variance g : ℝ) :=
    mul_pos hU hv
  simpa [scaledResidualSumSquares13, hv.ne'] using hmul

/-- Each unbiased raw sample variance is strictly positive a.s. -/
theorem ae_pos_sampleVariance13
    (h : TwoNormalSamples13 X P μ variance)
    (g : Fin 2) (hv : 0 < (variance g : ℝ)) :
    ∀ᵐ ω ∂P, 0 < sampleVariance13 (X g) ω := by
  filter_upwards [h.ae_pos_residualSumSquares13 g hv] with ω hRSS
  exact div_pos hRSS (by norm_num)

/-- The sum of the two unbiased sample variances is strictly positive a.s. -/
theorem ae_pos_sampleVarianceSum13
    (h : TwoNormalSamples13 X P μ variance)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    ∀ᵐ ω ∂P,
      0 < sampleVariance13 (X 0) ω + sampleVariance13 (X 1) ω := by
  filter_upwards
    [h.ae_pos_sampleVariance13 0 hvariance₀,
      h.ae_pos_sampleVariance13 1 hvariance₁] with ω hS₀ hS₁
  exact add_pos hS₀ hS₁

/-- The denominator in the ordinary Graybill--Deal sample weight is nonzero a.s. -/
theorem ae_ne_sampleVarianceSum13
    (h : TwoNormalSamples13 X P μ variance)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    ∀ᵐ ω ∂P,
      sampleVariance13 (X 0) ω + sampleVariance13 (X 1) ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_sampleVarianceSum13 hvariance₀ hvariance₁] with ω hS
  exact hS.ne'

/-- Each raw standardized residual coordinate `U_g` is strictly positive a.s. -/
theorem ae_pos_normalRawU13
    (h : TwoNormalSamples13 X P μ variance)
    (g : Fin 2) (hv : 0 < (variance g : ℝ)) :
    ∀ᵐ ω ∂P, 0 < normalRawU13 variance X g ω :=
  h.ae_pos_scaledResidualSumSquares13 g hv

/-- The raw gamma sum coordinate `L = U₀ + U₁` is strictly positive a.s. -/
theorem ae_pos_normalRawL13
    (h : TwoNormalSamples13 X P μ variance)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    ∀ᵐ ω ∂P, 0 < normalRawL13 variance X ω := by
  filter_upwards
    [h.ae_pos_normalRawU13 0 hvariance₀,
      h.ae_pos_normalRawU13 1 hvariance₁] with ω hU₀ hU₁
  exact add_pos hU₀ hU₁

/-- The raw gamma sum coordinate `L` is nonzero a.s. -/
theorem ae_ne_normalRawL13
    (h : TwoNormalSamples13 X P μ variance)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    ∀ᵐ ω ∂P, normalRawL13 variance X ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_normalRawL13 hvariance₀ hvariance₁] with ω hL
  exact hL.ne'

end TwoNormalSamples13

/--
The probabilistic `normalRawL13` coordinate is pointwise the deterministic
`rawResidualL13` coordinate evaluated at the two raw sample variances.
-/
theorem normalRawL13_eq_rawResidualL13_sampleVariances
    {Ω' : Type*}
    (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin 13 → Ω' → ℝ) (ω : Ω') :
    normalRawL13 variance X ω =
      rawResidualL13
        (variance 0 : ℝ) (variance 1 : ℝ)
        (sampleVariance13 (X 0) ω) (sampleVariance13 (X 1) ω) := by
  unfold normalRawL13 normalRawU13
  unfold scaledResidualSumSquares13
  unfold rawResidualL13 rawResidualScale13 sampleVariance13
  ring

namespace TwoNormalSamples13

variable {X : Fin 2 → Fin 13 → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}

/-- The deterministic raw residual sum coordinate is strictly positive a.s. -/
theorem ae_pos_rawResidualL13_sampleVariances
    (h : TwoNormalSamples13 X P μ variance)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    ∀ᵐ ω ∂P,
      0 <
        rawResidualL13
          (variance 0 : ℝ) (variance 1 : ℝ)
          (sampleVariance13 (X 0) ω)
          (sampleVariance13 (X 1) ω) := by
  filter_upwards
    [h.ae_pos_normalRawL13 hvariance₀ hvariance₁] with ω hL
  rwa [normalRawL13_eq_rawResidualL13_sampleVariances] at hL

/-- The `rawResidualL13` denominator used by `RawCoordinates` is nonzero a.s. -/
theorem ae_ne_rawResidualL13_sampleVariances
    (h : TwoNormalSamples13 X P μ variance)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    ∀ᵐ ω ∂P,
      rawResidualL13
          (variance 0 : ℝ) (variance 1 : ℝ)
          (sampleVariance13 (X 0) ω)
          (sampleVariance13 (X 1) ω) ≠ 0 := by
  filter_upwards
    [h.ae_pos_rawResidualL13_sampleVariances
      hvariance₀ hvariance₁] with ω hL
  exact hL.ne'

end TwoNormalSamples13

end

end GraybillDeal
