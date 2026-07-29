import GraybillDeal.UniversalRawRiskTransport
import GraybillDeal.UniversalReducedExperiment
import GraybillDeal.UniversalSampleSizes

/-!
# Raw variance parameters and the universal interior coordinate

For positive population variances, the oracle variance weight belongs to
the genuine parameter interval `(0,1)`.  This small module records that
fact and the exact translation between residual degrees of freedom
`νᵢ` and the gamma shapes used by the universal reduced experiment.
-/

namespace GraybillDeal

noncomputable section

/-- The population variance of the first sample mean is positive. -/
theorem universalRawPopulationMeanVariance1_pos
    (ν₁ : ℕ) {v₁ : NNReal} (hv₁ : 0 < v₁) :
    0 < (v₁ : ℝ) / (ν₁ + 1) := by
  have hv₁r : 0 < (v₁ : ℝ) := by exact_mod_cast hv₁
  positivity

/-- The population variance of the second sample mean is positive. -/
theorem universalRawPopulationMeanVariance2_pos
    (ν₂ : ℕ) {v₂ : NNReal} (hv₂ : 0 < v₂) :
    0 < (v₂ : ℝ) / (ν₂ + 1) := by
  have hv₂r : 0 < (v₂ : ℝ) := by exact_mod_cast hv₂
  positivity

theorem universalRawPopulationMeanVarianceSum_pos
    (ν₁ ν₂ : ℕ) {v₁ v₂ : NNReal}
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) :
    0 <
      (v₁ : ℝ) / (ν₁ + 1)
        + (v₂ : ℝ) / (ν₂ + 1) :=
  add_pos
    (universalRawPopulationMeanVariance1_pos ν₁ hv₁)
    (universalRawPopulationMeanVariance2_pos ν₂ hv₂)

theorem universalRawOracleTheta_pos
    (ν₁ ν₂ : ℕ) {v₁ v₂ : NNReal}
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) :
    0 < universalRawOracleTheta ν₁ ν₂ v₁ v₂ := by
  unfold universalRawOracleTheta oracleVarianceWeightU
  exact div_pos
    (universalRawPopulationMeanVariance1_pos ν₁ hv₁)
    (universalRawPopulationMeanVarianceSum_pos ν₁ ν₂ hv₁ hv₂)

theorem universalRawOracleTheta_lt_one
    (ν₁ ν₂ : ℕ) {v₁ v₂ : NNReal}
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) :
    universalRawOracleTheta ν₁ ν₂ v₁ v₂ < 1 := by
  unfold universalRawOracleTheta oracleVarianceWeightU
  apply (div_lt_one
    (universalRawPopulationMeanVarianceSum_pos ν₁ ν₂ hv₁ hv₂)).2
  have h₂ :=
    universalRawPopulationMeanVariance2_pos ν₂ hv₂
  linarith

/-- The oracle weight as an element of the open universal parameter
space. -/
def universalRawOracleInteriorTheta
    (ν₁ ν₂ : ℕ) (v₁ v₂ : NNReal)
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) :
    UniversalInteriorTheta :=
  ⟨universalRawOracleTheta ν₁ ν₂ v₁ v₂,
    universalRawOracleTheta_pos ν₁ ν₂ hv₁ hv₂,
    universalRawOracleTheta_lt_one ν₁ ν₂ hv₁ hv₂⟩

@[simp]
theorem universalRawOracleInteriorTheta_coe
    (ν₁ ν₂ : ℕ) (v₁ v₂ : NNReal)
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) :
    (universalRawOracleInteriorTheta
      ν₁ ν₂ v₁ v₂ hv₁ hv₂ : ℝ)
      =
    universalRawOracleTheta ν₁ ν₂ v₁ v₂ :=
  rfl

/-- A sample with residual degrees of freedom `ν` has gamma shape
`ν/2`. -/
theorem universalShape_residualDegrees
    (ν : ℕ) :
    universalShape (ν + 1) = (ν : ℝ) / 2 := by
  unfold universalShape
  push_cast
  ring

theorem universalShape_residualDegrees_pos
    {ν : ℕ} (hν : 0 < ν) :
    0 < universalShape (ν + 1) := by
  rw [universalShape_residualDegrees]
  exact div_pos (by exact_mod_cast hν) (by norm_num)

end

end GraybillDeal
