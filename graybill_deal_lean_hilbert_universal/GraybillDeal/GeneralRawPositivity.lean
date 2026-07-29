import GraybillDeal.GeneralRawCoordinates
import GraybillDeal.GeneralRawNormalSummary

/-!
# Almost-sure positivity of the generic raw variance coordinates

For residual degrees of freedom `ν ≥ 9`, each standardized residual sum of
squares has law `Gamma(ν/2, 1/2)`.  Since `ν/2 > 1`, that law is concentrated
on the strictly positive reals.  Consequently each sample variance, their
sum, and the canonical sum coordinate `L` are strictly positive almost
surely.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory Set

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem gammaPDF_eq_zero_of_nonpos_of_one_lt_shape
    {a r x : ℝ} (ha : 1 < a) (hx : x ≤ 0) :
    gammaPDF a r x = 0 := by
  rcases hx.eq_or_lt with rfl | hxneg
  · rw [gammaPDF_eq, if_pos le_rfl]
    rw [Real.zero_rpow (sub_pos.mpr ha).ne']
    simp
  · exact gammaPDF_of_neg hxneg

/-- A gamma law of shape greater than one is concentrated on `(0,∞)`. -/
theorem gammaMeasure_ae_pos_of_one_lt_shape
    {a r : ℝ} (ha : 1 < a) :
    ∀ᵐ x : ℝ ∂gammaMeasure a r, 0 < x := by
  unfold gammaMeasure gammaPDF
  rw [ae_withDensity_iff
    ((measurable_gammaPDFReal a r).ennreal_ofReal)]
  filter_upwards [] with x hx
  by_contra hpos
  exact hx
    (gammaPDF_eq_zero_of_nonpos_of_one_lt_shape
      ha (le_of_not_gt hpos))

/-- Law transport of strict positivity from a gamma distribution. -/
theorem ae_pos_of_hasLaw_gammaMeasure_of_one_lt_shape
    {P : Measure Ω} {Y : Ω → ℝ} {a r : ℝ}
    (ha : 1 < a)
    (hY : HasLaw Y (gammaMeasure a r) P) :
    ∀ᵐ ω ∂P, 0 < Y ω := by
  rw [hY.ae_iff (by fun_prop)]
  exact gammaMeasure_ae_pos_of_one_lt_shape ha

namespace TwoNormalSamplesN

variable {ν : ℕ}
  {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}

/-- Each standardized residual sum of squares is strictly positive a.s. -/
theorem ae_pos_scaledResidualSumSquaresN
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (g : Fin 2) (hv : 0 < (variance g : ℝ)) :
    ∀ᵐ ω ∂P,
      0 < scaledResidualSumSquaresN ν (variance g) (X g) ω := by
  have hshape : 1 < (ν : ℝ) / 2 := by
    have hνR : (9 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
    linarith
  exact
    ae_pos_of_hasLaw_gammaMeasure_of_one_lt_shape hshape
      (h.hasLaw_scaledResidualSumSquares (by omega) g hv)

/-- Each raw residual sum of squares is strictly positive a.s. -/
theorem ae_pos_residualSumSquaresN
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (g : Fin 2) (hv : 0 < (variance g : ℝ)) :
    ∀ᵐ ω ∂P, 0 < residualSumSquaresN ν (X g) ω := by
  filter_upwards
    [h.ae_pos_scaledResidualSumSquaresN hν g hv] with ω hU
  have hmul :
      0 <
        scaledResidualSumSquaresN ν (variance g) (X g) ω
          * (variance g : ℝ) :=
    mul_pos hU hv
  simpa [scaledResidualSumSquaresN, hv.ne'] using hmul

/-- Each unbiased raw sample variance is strictly positive a.s. -/
theorem ae_pos_sampleVarianceN
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (g : Fin 2) (hv : 0 < (variance g : ℝ)) :
    ∀ᵐ ω ∂P, 0 < sampleVarianceN ν (X g) ω := by
  filter_upwards
    [h.ae_pos_residualSumSquaresN hν g hv] with ω hRSS
  exact div_pos hRSS (by positivity)

/-- The sum `S₀²+S₁²` of the two unbiased sample variances is positive a.s. -/
theorem ae_pos_sampleVarianceSumN
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    ∀ᵐ ω ∂P,
      0 <
        sampleVarianceN ν (X 0) ω
          + sampleVarianceN ν (X 1) ω := by
  filter_upwards
    [h.ae_pos_sampleVarianceN hν 0 hvariance₀,
      h.ae_pos_sampleVarianceN hν 1 hvariance₁] with ω hS₀ hS₁
  exact add_pos hS₀ hS₁

/-- The denominator in the ordinary Graybill--Deal weight is nonzero a.s. -/
theorem ae_ne_sampleVarianceSumN
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    ∀ᵐ ω ∂P,
      sampleVarianceN ν (X 0) ω
          + sampleVarianceN ν (X 1) ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_sampleVarianceSumN
      hν hvariance₀ hvariance₁] with ω hS
  exact hS.ne'

/-- Each raw standardized residual coordinate `U_g` is positive a.s. -/
theorem ae_pos_normalRawUN
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (g : Fin 2) (hv : 0 < (variance g : ℝ)) :
    ∀ᵐ ω ∂P, 0 < normalRawUN ν variance X g ω :=
  h.ae_pos_scaledResidualSumSquaresN hν g hv

/-- The raw gamma sum coordinate `L=U₀+U₁` is positive a.s. -/
theorem ae_pos_normalRawLN
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    ∀ᵐ ω ∂P, 0 < normalRawLN ν variance X ω := by
  filter_upwards
    [h.ae_pos_normalRawUN hν 0 hvariance₀,
      h.ae_pos_normalRawUN hν 1 hvariance₁] with ω hU₀ hU₁
  exact add_pos hU₀ hU₁

/-- The raw gamma sum coordinate `L` is nonzero a.s. -/
theorem ae_ne_normalRawLN
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    ∀ᵐ ω ∂P, normalRawLN ν variance X ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_normalRawLN
      hν hvariance₀ hvariance₁] with ω hL
  exact hL.ne'

end TwoNormalSamplesN

/--
The probabilistic `normalRawLN` coordinate is pointwise the deterministic
`rawResidualLN` coordinate evaluated at the two raw sample variances.
-/
theorem normalRawLN_eq_rawResidualLN_sampleVariances
    {ν : ℕ} (hν : 0 < ν)
    {Ω' : Type*} [MeasurableSpace Ω']
    (variance : Fin 2 → NNReal)
    (X : Fin 2 → Fin (ν + 1) → Ω' → ℝ) (ω : Ω') :
    normalRawLN ν variance X ω =
      rawResidualLN ν
        (variance 0 : ℝ) (variance 1 : ℝ)
        (sampleVarianceN ν (X 0) ω)
        (sampleVarianceN ν (X 1) ω) := by
  unfold normalRawLN normalRawUN
  unfold scaledResidualSumSquaresN
  unfold rawResidualLN rawResidualScaleN
  rw [residualDF_mul_sampleVarianceN hν (X 0) ω,
    residualDF_mul_sampleVarianceN hν (X 1) ω]

namespace TwoNormalSamplesN

variable {ν : ℕ}
  {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}

/-- The deterministic residual sum coordinate is strictly positive a.s. -/
theorem ae_pos_rawResidualLN_sampleVariances
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    ∀ᵐ ω ∂P,
      0 <
        rawResidualLN ν
          (variance 0 : ℝ) (variance 1 : ℝ)
          (sampleVarianceN ν (X 0) ω)
          (sampleVarianceN ν (X 1) ω) := by
  filter_upwards
    [h.ae_pos_normalRawLN
      hν hvariance₀ hvariance₁] with ω hL
  rwa [normalRawLN_eq_rawResidualLN_sampleVariances
    (by omega)] at hL

/-- The deterministic residual sum coordinate is nonzero a.s. -/
theorem ae_ne_rawResidualLN_sampleVariances
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    ∀ᵐ ω ∂P,
      rawResidualLN ν
          (variance 0 : ℝ) (variance 1 : ℝ)
          (sampleVarianceN ν (X 0) ω)
          (sampleVarianceN ν (X 1) ω) ≠ 0 := by
  filter_upwards
    [h.ae_pos_rawResidualLN_sampleVariances
      hν hvariance₀ hvariance₁] with ω hL
  exact hL.ne'

end TwoNormalSamplesN

end

end GraybillDeal
