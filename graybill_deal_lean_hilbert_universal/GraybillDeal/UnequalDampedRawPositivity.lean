import GraybillDeal.GeneralRawPositivity
import GraybillDeal.UnequalDampedRawSummary

/-!
# Almost-sure positivity for the `(13,17)` raw coordinates

Both standardized residual sums have gamma laws supported on `(0,∞)`.
Consequently the two sample variances, their Graybill--Deal variance-of-mean
sum, and the canonical sum coordinate `L` are positive almost surely.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

namespace TwoNormalSamplesU

variable
  {X : Fin 13 → Ω → ℝ} {Y : Fin 17 → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}

theorem ae_pos_normalRawU1_13_17
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P, 0 < normalRawU1_13_17 v₁ X ω := by
  have hU₁ :
      HasLaw (normalRawU1_13_17 v₁ X)
        (gammaMeasure 6 (1 / 2)) P := by
    convert h.hasLaw_scaledResidualSumSquaresX (by norm_num) hv₁ using 1 <;>
      norm_num [normalRawU1_13_17]
  exact
    ae_pos_of_hasLaw_gammaMeasure_of_one_lt_shape
      (by norm_num : (1 : ℝ) < 6)
      hU₁

theorem ae_pos_normalRawU2_13_17
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P, 0 < normalRawU2_13_17 v₂ Y ω := by
  have hU₂ :
      HasLaw (normalRawU2_13_17 v₂ Y)
        (gammaMeasure 8 (1 / 2)) P := by
    convert h.hasLaw_scaledResidualSumSquaresY (by norm_num) hv₂ using 1 <;>
      norm_num [normalRawU2_13_17]
  exact
    ae_pos_of_hasLaw_gammaMeasure_of_one_lt_shape
      (by norm_num : (1 : ℝ) < 8)
      hU₂

theorem ae_pos_residualSumSquaresX13
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P, 0 < residualSumSquaresN 12 X ω := by
  filter_upwards [h.ae_pos_normalRawU1_13_17 hv₁] with ω hU
  have hmul :
      0 < normalRawU1_13_17 v₁ X ω * (v₁ : ℝ) :=
    mul_pos hU hv₁
  simpa [normalRawU1_13_17, scaledResidualSumSquaresN, hv₁.ne'] using hmul

theorem ae_pos_residualSumSquaresY17
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P, 0 < residualSumSquaresN 16 Y ω := by
  filter_upwards [h.ae_pos_normalRawU2_13_17 hv₂] with ω hU
  have hmul :
      0 < normalRawU2_13_17 v₂ Y ω * (v₂ : ℝ) :=
    mul_pos hU hv₂
  simpa [normalRawU2_13_17, scaledResidualSumSquaresN, hv₂.ne'] using hmul

theorem ae_pos_sampleVarianceX13
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hv₁ : 0 < (v₁ : ℝ)) :
    ∀ᵐ ω ∂P, 0 < sampleVarianceN 12 X ω := by
  filter_upwards [h.ae_pos_residualSumSquaresX13 hv₁] with ω hRSS
  exact div_pos hRSS (by norm_num)

theorem ae_pos_sampleVarianceY17
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P, 0 < sampleVarianceN 16 Y ω := by
  filter_upwards [h.ae_pos_residualSumSquaresY17 hv₂] with ω hRSS
  exact div_pos hRSS (by norm_num)

/--
The denominator
`S₁²/13 + S₂²/17` in the unequal Graybill--Deal weight is positive a.s.
-/
theorem ae_pos_sampleMeanVarianceSum13_17
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      0 <
        sampleVarianceN 12 X ω / 13
          + sampleVarianceN 16 Y ω / 17 := by
  filter_upwards
    [h.ae_pos_sampleVarianceX13 hv₁,
      h.ae_pos_sampleVarianceY17 hv₂] with ω hS₁ hS₂
  exact add_pos (div_pos hS₁ (by norm_num)) (div_pos hS₂ (by norm_num))

theorem ae_ne_sampleMeanVarianceSum13_17
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P,
      sampleVarianceN 12 X ω / 13
          + sampleVarianceN 16 Y ω / 17 ≠ 0 := by
  filter_upwards
    [h.ae_pos_sampleMeanVarianceSum13_17 hv₁ hv₂] with ω hA
  exact hA.ne'

theorem ae_pos_normalRawL13_17
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P, 0 < normalRawL13_17 v₁ v₂ X Y ω := by
  filter_upwards
    [h.ae_pos_normalRawU1_13_17 hv₁,
      h.ae_pos_normalRawU2_13_17 hv₂] with ω hU₁ hU₂
  exact add_pos hU₁ hU₂

theorem ae_ne_normalRawL13_17
    (h : TwoNormalSamplesU 12 16 X Y P μ v₁ v₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    ∀ᵐ ω ∂P, normalRawL13_17 v₁ v₂ X Y ω ≠ 0 := by
  filter_upwards [h.ae_pos_normalRawL13_17 hv₁ hv₂] with ω hL
  exact hL.ne'

end TwoNormalSamplesU

end

end GraybillDeal
