import GraybillDeal.GeneralRawPositivity
import GraybillDeal.UnequalFixedDifferenceFourRawEstimator

/-!
# Almost-sure positivity for the fixed-difference-four raw coordinates

For every `m ≥ 7`, both standardized residual sums have gamma laws supported
on `(0,∞)`.  Consequently the residual sums of squares, unbiased sample
variances, estimated sample-mean variances, their sum, and the canonical
gamma coordinate `L` are positive almost surely.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

namespace TwoNormalSamplesU

variable
  {m : ℕ}
  {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
  {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}

private theorem unequalFD4RawPositivity_shape_one
    (hm : 7 ≤ m) :
    ((unequalFixedDifferenceFourResidualDF1 m : ℕ) : ℝ) / 2
      = (m : ℝ) - 1 := by
  have hm1 : 1 ≤ m := by omega
  unfold unequalFixedDifferenceFourResidualDF1
  rw [Nat.cast_mul, Nat.cast_sub hm1]
  push_cast
  ring

private theorem unequalFD4RawPositivity_shape_two :
    ((unequalFixedDifferenceFourResidualDF2 m : ℕ) : ℝ) / 2
      = (m : ℝ) + 1 := by
  unfold unequalFixedDifferenceFourResidualDF2
  push_cast
  ring

private theorem unequalFD4RawPositivity_df_one_pos
    (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourResidualDF1 m := by
  unfold unequalFixedDifferenceFourResidualDF1
  omega

private theorem unequalFD4RawPositivity_df_two_pos :
    0 < unequalFixedDifferenceFourResidualDF2 m := by
  unfold unequalFixedDifferenceFourResidualDF2
  omega

/-- The first standardized residual sum is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourNormalRawU1
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m) (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 < unequalFixedDifferenceFourNormalRawU1 m v₁ X ω := by
  have hU₁ :
      HasLaw (unequalFixedDifferenceFourNormalRawU1 m v₁ X)
        (gammaMeasure ((m : ℝ) - 1) (1 / 2)) P := by
    simpa only [unequalFixedDifferenceFourNormalRawU1,
      unequalFD4RawPositivity_shape_one hm] using
      h.hasLaw_scaledResidualSumSquaresX
        (unequalFD4RawPositivity_df_one_pos hm) hv₁
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  exact
    ae_pos_of_hasLaw_gammaMeasure_of_one_lt_shape
      (by linarith : (1 : ℝ) < (m : ℝ) - 1)
      hU₁

/-- The second standardized residual sum is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourNormalRawU2
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 < unequalFixedDifferenceFourNormalRawU2 m v₂ Y ω := by
  have hU₂ :
      HasLaw (unequalFixedDifferenceFourNormalRawU2 m v₂ Y)
        (gammaMeasure ((m : ℝ) + 1) (1 / 2)) P := by
    simpa only [unequalFixedDifferenceFourNormalRawU2,
      unequalFD4RawPositivity_shape_two] using
      h.hasLaw_scaledResidualSumSquaresY
        unequalFD4RawPositivity_df_two_pos hv₂
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  exact
    ae_pos_of_hasLaw_gammaMeasure_of_one_lt_shape
      (by linarith : (1 : ℝ) < (m : ℝ) + 1)
      hU₂

theorem ae_ne_unequalFixedDifferenceFourNormalRawU1
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m) (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P,
      unequalFixedDifferenceFourNormalRawU1 m v₁ X ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourNormalRawU1 hm hv₁] with ω hU
  exact hU.ne'

theorem ae_ne_unequalFixedDifferenceFourNormalRawU2
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      unequalFixedDifferenceFourNormalRawU2 m v₂ Y ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourNormalRawU2 hm hv₂] with ω hU
  exact hU.ne'

/-- The first residual sum of squares is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourResidualSumSquares1
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m) (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 <
        residualSumSquaresN
          (unequalFixedDifferenceFourResidualDF1 m) X ω := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourNormalRawU1 hm hv₁] with ω hU
  have hmul :
      0 <
        unequalFixedDifferenceFourNormalRawU1 m v₁ X ω
          * (v₁ : ℝ) :=
    mul_pos hU hv₁
  simpa [unequalFixedDifferenceFourNormalRawU1,
    scaledResidualSumSquaresN, hv₁.ne'] using hmul

/-- The second residual sum of squares is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourResidualSumSquares2
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 <
        residualSumSquaresN
          (unequalFixedDifferenceFourResidualDF2 m) Y ω := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourNormalRawU2 hm hv₂] with ω hU
  have hmul :
      0 <
        unequalFixedDifferenceFourNormalRawU2 m v₂ Y ω
          * (v₂ : ℝ) :=
    mul_pos hU hv₂
  simpa [unequalFixedDifferenceFourNormalRawU2,
    scaledResidualSumSquaresN, hv₂.ne'] using hmul

/-- The first unbiased sample variance is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourSampleVariance1
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m) (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 <
        sampleVarianceN
          (unequalFixedDifferenceFourResidualDF1 m) X ω := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourResidualSumSquares1 hm hv₁]
      with ω hRSS
  exact div_pos hRSS
    (by
      exact_mod_cast unequalFD4RawPositivity_df_one_pos hm)

/-- The second unbiased sample variance is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourSampleVariance2
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 <
        sampleVarianceN
          (unequalFixedDifferenceFourResidualDF2 m) Y ω := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourResidualSumSquares2 hm hv₂]
      with ω hRSS
  exact div_pos hRSS
    (by
      exact_mod_cast unequalFD4RawPositivity_df_two_pos (m := m))

theorem ae_ne_unequalFixedDifferenceFourSampleVariance1
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m) (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P,
      sampleVarianceN
        (unequalFixedDifferenceFourResidualDF1 m) X ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourSampleVariance1 hm hv₁]
      with ω hS
  exact hS.ne'

theorem ae_ne_unequalFixedDifferenceFourSampleVariance2
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      sampleVarianceN
        (unequalFixedDifferenceFourResidualDF2 m) Y ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourSampleVariance2 hm hv₂]
      with ω hS
  exact hS.ne'

/-- The first estimated sample-mean variance is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourRawMeanVariance1
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m) (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 < unequalFixedDifferenceFourRawMeanVariance1 m X ω := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourSampleVariance1 hm hv₁]
      with ω hS
  unfold unequalFixedDifferenceFourRawMeanVariance1
  exact div_pos hS (by positivity)

/-- The second estimated sample-mean variance is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourRawMeanVariance2
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 < unequalFixedDifferenceFourRawMeanVariance2 m Y ω := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourSampleVariance2 hm hv₂]
      with ω hS
  unfold unequalFixedDifferenceFourRawMeanVariance2
  exact div_pos hS (by positivity)

theorem ae_ne_unequalFixedDifferenceFourRawMeanVariance1
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m) (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P,
      unequalFixedDifferenceFourRawMeanVariance1 m X ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourRawMeanVariance1 hm hv₁]
      with ω hA
  exact hA.ne'

theorem ae_ne_unequalFixedDifferenceFourRawMeanVariance2
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      unequalFixedDifferenceFourRawMeanVariance2 m Y ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourRawMeanVariance2 hm hv₂]
      with ω hA
  exact hA.ne'

/-- The raw Graybill--Deal denominator is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourRawMeanVarianceSum
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 < unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourRawMeanVariance1 hm hv₁,
      h.ae_pos_unequalFixedDifferenceFourRawMeanVariance2 hm hv₂]
      with ω hA₁ hA₂
  exact add_pos hA₁ hA₂

theorem ae_ne_unequalFixedDifferenceFourRawMeanVarianceSum
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourRawMeanVarianceSum hm hv₁ hv₂]
      with ω hA
  exact hA.ne'

/-- The canonical gamma sum coordinate is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourNormalRawL
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 < unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourNormalRawU1 hm hv₁,
      h.ae_pos_unequalFixedDifferenceFourNormalRawU2 hm hv₂]
      with ω hU₁ hU₂
  exact add_pos hU₁ hU₂

theorem ae_ne_unequalFixedDifferenceFourNormalRawL
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourNormalRawL hm hv₁ hv₂]
      with ω hL
  exact hL.ne'

end TwoNormalSamplesU

end

end GraybillDeal
