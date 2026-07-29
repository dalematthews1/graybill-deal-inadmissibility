import GraybillDeal.GeneralRawPositivity
import GraybillDeal.UnequalFixedDifferenceFourAllNRawEstimator

/-!
# Almost-sure positivity for the fixed-difference-four raw coordinates

For every `n ≥ 13`, both standardized residual sums have gamma laws supported
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
  {n : ℕ}
  {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
  {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}

private theorem unequalFD4AllNRawPositivity_shape_one
    (hn : 13 ≤ n) :
    ((unequalFixedDifferenceFourAllNResidualDF1 n : ℕ) : ℝ) / 2
      = unequalFixedDifferenceFourSampleM n - 1 := by
  have hn1 : 1 ≤ n := by omega
  unfold unequalFixedDifferenceFourAllNResidualDF1
    unequalFixedDifferenceFourSampleM
  rw [Nat.cast_sub hn1]
  push_cast
  ring

private theorem unequalFD4AllNRawPositivity_shape_two :
    ((unequalFixedDifferenceFourAllNResidualDF2 n : ℕ) : ℝ) / 2
      = unequalFixedDifferenceFourSampleM n + 1 := by
  unfold unequalFixedDifferenceFourAllNResidualDF2
    unequalFixedDifferenceFourSampleM
  push_cast
  ring

private theorem unequalFD4AllNRawPositivity_df_one_pos
    (hn : 13 ≤ n) :
    0 < unequalFixedDifferenceFourAllNResidualDF1 n := by
  unfold unequalFixedDifferenceFourAllNResidualDF1
  omega

private theorem unequalFD4AllNRawPositivity_df_two_pos :
    0 < unequalFixedDifferenceFourAllNResidualDF2 n := by
  unfold unequalFixedDifferenceFourAllNResidualDF2
  omega

/-- The first standardized residual sum is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourAllNNormalRawU1
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n) (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 < unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X ω := by
  have hU₁ :
      HasLaw (unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X)
        (gammaMeasure
          (unequalFixedDifferenceFourSampleM n - 1) (1 / 2)) P := by
    simpa only [unequalFixedDifferenceFourAllNNormalRawU1,
      unequalFD4AllNRawPositivity_shape_one hn] using
      h.hasLaw_scaledResidualSumSquaresX
        (unequalFD4AllNRawPositivity_df_one_pos hn) hv₁
  have hmR :
      7 ≤ unequalFixedDifferenceFourSampleM n :=
    unequalFixedDifferenceFourSampleM_ge_seven hn
  exact
    ae_pos_of_hasLaw_gammaMeasure_of_one_lt_shape
      (by
        linarith :
        (1 : ℝ) < unequalFixedDifferenceFourSampleM n - 1)
      hU₁

/-- The second standardized residual sum is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourAllNNormalRawU2
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 < unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y ω := by
  have hU₂ :
      HasLaw (unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y)
        (gammaMeasure
          (unequalFixedDifferenceFourSampleM n + 1) (1 / 2)) P := by
    simpa only [unequalFixedDifferenceFourAllNNormalRawU2,
      unequalFD4AllNRawPositivity_shape_two] using
      h.hasLaw_scaledResidualSumSquaresY
        unequalFD4AllNRawPositivity_df_two_pos hv₂
  have hmR :
      7 ≤ unequalFixedDifferenceFourSampleM n :=
    unequalFixedDifferenceFourSampleM_ge_seven hn
  exact
    ae_pos_of_hasLaw_gammaMeasure_of_one_lt_shape
      (by
        linarith :
        (1 : ℝ) < unequalFixedDifferenceFourSampleM n + 1)
      hU₂

theorem ae_ne_unequalFixedDifferenceFourAllNNormalRawU1
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n) (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P,
      unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourAllNNormalRawU1 hn hv₁] with ω hU
  exact hU.ne'

theorem ae_ne_unequalFixedDifferenceFourAllNNormalRawU2
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourAllNNormalRawU2 hn hv₂] with ω hU
  exact hU.ne'

/-- The first residual sum of squares is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourAllNResidualSumSquares1
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n) (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 <
        residualSumSquaresN
          (unequalFixedDifferenceFourAllNResidualDF1 n) X ω := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourAllNNormalRawU1 hn hv₁] with ω hU
  have hmul :
      0 <
        unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X ω
          * (v₁ : ℝ) :=
    mul_pos hU hv₁
  simpa [unequalFixedDifferenceFourAllNNormalRawU1,
    scaledResidualSumSquaresN, hv₁.ne'] using hmul

/-- The second residual sum of squares is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourAllNResidualSumSquares2
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 <
        residualSumSquaresN
          (unequalFixedDifferenceFourAllNResidualDF2 n) Y ω := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourAllNNormalRawU2 hn hv₂] with ω hU
  have hmul :
      0 <
        unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y ω
          * (v₂ : ℝ) :=
    mul_pos hU hv₂
  simpa [unequalFixedDifferenceFourAllNNormalRawU2,
    scaledResidualSumSquaresN, hv₂.ne'] using hmul

/-- The first unbiased sample variance is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourAllNSampleVariance1
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n) (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 <
        sampleVarianceN
          (unequalFixedDifferenceFourAllNResidualDF1 n) X ω := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourAllNResidualSumSquares1 hn hv₁]
      with ω hRSS
  exact div_pos hRSS
    (by
      exact_mod_cast unequalFD4AllNRawPositivity_df_one_pos hn)

/-- The second unbiased sample variance is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourAllNSampleVariance2
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 <
        sampleVarianceN
          (unequalFixedDifferenceFourAllNResidualDF2 n) Y ω := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourAllNResidualSumSquares2 hn hv₂]
      with ω hRSS
  exact div_pos hRSS
    (by
      exact_mod_cast unequalFD4AllNRawPositivity_df_two_pos (n := n))

theorem ae_ne_unequalFixedDifferenceFourAllNSampleVariance1
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n) (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P,
      sampleVarianceN
        (unequalFixedDifferenceFourAllNResidualDF1 n) X ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourAllNSampleVariance1 hn hv₁]
      with ω hS
  exact hS.ne'

theorem ae_ne_unequalFixedDifferenceFourAllNSampleVariance2
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      sampleVarianceN
        (unequalFixedDifferenceFourAllNResidualDF2 n) Y ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourAllNSampleVariance2 hn hv₂]
      with ω hS
  exact hS.ne'

/-- The first estimated sample-mean variance is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourAllNRawMeanVariance1
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n) (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 < unequalFixedDifferenceFourAllNRawMeanVariance1 n X ω := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourAllNSampleVariance1 hn hv₁]
      with ω hS
  unfold unequalFixedDifferenceFourAllNRawMeanVariance1
  exact div_pos hS (by positivity)

/-- The second estimated sample-mean variance is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourAllNRawMeanVariance2
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 < unequalFixedDifferenceFourAllNRawMeanVariance2 n Y ω := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourAllNSampleVariance2 hn hv₂]
      with ω hS
  unfold unequalFixedDifferenceFourAllNRawMeanVariance2
  exact div_pos hS (by positivity)

theorem ae_ne_unequalFixedDifferenceFourAllNRawMeanVariance1
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n) (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P,
      unequalFixedDifferenceFourAllNRawMeanVariance1 n X ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourAllNRawMeanVariance1 hn hv₁]
      with ω hA
  exact hA.ne'

theorem ae_ne_unequalFixedDifferenceFourAllNRawMeanVariance2
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      unequalFixedDifferenceFourAllNRawMeanVariance2 n Y ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourAllNRawMeanVariance2 hn hv₂]
      with ω hA
  exact hA.ne'

/-- The raw Graybill--Deal denominator is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourAllNRawMeanVarianceSum
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 < unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourAllNRawMeanVariance1 hn hv₁,
      h.ae_pos_unequalFixedDifferenceFourAllNRawMeanVariance2 hn hv₂]
      with ω hA₁ hA₂
  exact add_pos hA₁ hA₂

theorem ae_ne_unequalFixedDifferenceFourAllNRawMeanVarianceSum
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourAllNRawMeanVarianceSum hn hv₁ hv₂]
      with ω hA
  exact hA.ne'

/-- The canonical gamma sum coordinate is positive almost surely. -/
theorem ae_pos_unequalFixedDifferenceFourAllNNormalRawL
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 < unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourAllNNormalRawU1 hn hv₁,
      h.ae_pos_unequalFixedDifferenceFourAllNNormalRawU2 hn hv₂]
      with ω hU₁ hU₂
  exact add_pos hU₁ hU₂

theorem ae_ne_unequalFixedDifferenceFourAllNNormalRawL
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω ≠ 0 := by
  filter_upwards
    [h.ae_pos_unequalFixedDifferenceFourAllNNormalRawL hn hv₁ hv₂]
      with ω hL
  exact hL.ne'

end TwoNormalSamplesU

end

end GraybillDeal
