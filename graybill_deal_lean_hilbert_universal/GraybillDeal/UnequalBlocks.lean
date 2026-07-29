import GraybillDeal.UnequalCochran

/-!
# Mean/residual block independence for unequal samples

This file packages the Gaussian mean/residual decomposition for two normal
samples whose sizes may differ.  The main result says that the pair of sample
means is independent of the pair of residual sums of squares.  Its corollaries
give the forms used by the unequal-size risk bridge: the mean difference is
independent of the residual sums of squares, and so is the pair consisting of
an oracle-centered error and the mean difference.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

namespace TwoNormalSamplesU

variable {ν₁ ν₂ : ℕ}
  {X : Fin (ν₁ + 1) → Ω → ℝ} {Y : Fin (ν₂ + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}

/--
The two sample means, represented as a two-coordinate function, are
independent of the complete residual vectors of both samples.

The proof is the Gaussian block argument: all four blocks are linear images
of the full observation vector, and each mean/residual cross-covariance
vanishes.
-/
theorem indepFun_allSampleMeans_allResiduals
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    IndepFun
      (fun ω b =>
        if b = true then sampleMeanN ν₂ Y ω else sampleMeanN ν₁ X ω)
      (fun ω k =>
        Sum.elim
          (fun i => sampleResidualN ν₁ X ω i)
          (fun j => sampleResidualN ν₂ Y ω j) k) P := by
  let allMeans :
      ((Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) →L[ℝ] (Bool → ℝ) :=
    ContinuousLinearMap.pi fun b =>
      if b then meanYLinearU ν₁ ν₂ else meanXLinearU ν₁ ν₂
  let allResiduals :
      ((Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) →L[ℝ]
        ((Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) :=
    ContinuousLinearMap.pi fun k => residLinearU ν₁ ν₂ k
  let split :
      ((Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) →L[ℝ]
        ((Bool → ℝ) ×
          ((Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ)) :=
    allMeans.prod allResiduals
  have hjoint :
      HasGaussianLaw
        (fun ω =>
          (fun b =>
            if b = true then sampleMeanN ν₂ Y ω else sampleMeanN ν₁ X ω,
            fun k =>
              Sum.elim
                (fun i => sampleResidualN ν₁ X ω i)
                (fun j => sampleResidualN ν₂ Y ω j) k)) P := by
    have hmap := h.hasGaussianLaw_all.map_fun split
    apply hmap.congr
    filter_upwards [] with ω
    refine Prod.ext ?_ ?_
    · funext b
      cases b <;>
        simp [split, allMeans, obsU, sampleMeanN,
          meanXLinearU, meanYLinearU, selectXLinearU, selectYLinearU]
    · funext k
      cases k with
      | inl i =>
          simp [split, allResiduals, obsU, sampleResidualN,
            sampleMeanN, residLinearU, selectXLinearU]
      | inr j =>
          simp [split, allResiduals, obsU, sampleResidualN,
            sampleMeanN, residLinearU, selectYLinearU]
  apply hjoint.indepFun_of_covariance_eval
  intro b k
  cases b with
  | false =>
      cases k with
      | inl i => exact h.covariance_sampleMeanX_residualX i
      | inr j => exact h.covariance_sampleMeanX_residualY j
  | true =>
      cases k with
      | inl i => exact h.covariance_sampleMeanY_residualX i
      | inr j => exact h.covariance_sampleMeanY_residualY j

/-- Both sample means are jointly independent of both residual sums of squares. -/
theorem indepFun_sampleMeans_residualSumSquares
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    IndepFun
      (fun ω => (sampleMeanN ν₁ X ω, sampleMeanN ν₂ Y ω))
      (fun ω =>
        (residualSumSquaresN ν₁ X ω,
          residualSumSquaresN ν₂ Y ω)) P := by
  let rssPair :
      ((Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) → ℝ × ℝ :=
    fun z =>
      (∑ i, z (Sum.inl i) ^ 2,
        ∑ j, z (Sum.inr j) ^ 2)
  have hcomp :=
    h.indepFun_allSampleMeans_allResiduals.comp
      (show Measurable (fun m : Bool → ℝ => (m false, m true)) by
        fun_prop)
      (show Measurable rssPair by
        dsimp only [rssPair]
        fun_prop)
  apply hcomp.congr
  · filter_upwards [] with ω
    rfl
  · filter_upwards [] with ω
    simp only [Function.comp_apply, rssPair, residualSumSquaresN,
      sampleResidualN, Sum.elim_inl, Sum.elim_inr]

/-- The mean difference is independent of the pair of residual sums of squares. -/
theorem indepFun_meanDifference_residualSumSquares
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    IndepFun
      (meanDifferenceU ν₁ ν₂ X Y)
      (fun ω =>
        (residualSumSquaresN ν₁ X ω,
          residualSumSquaresN ν₂ Y ω)) P := by
  have hcomp :=
    h.indepFun_sampleMeans_residualSumSquares.comp
      (show Measurable (fun m : ℝ × ℝ => m.2 - m.1) by fun_prop)
      measurable_id
  apply hcomp.congr
  · filter_upwards [] with ω
    rfl
  · filter_upwards [] with ω
    rfl

/--
For every fixed weight, the pair `(centered error, mean difference)` is
independent of both residual sums of squares.
-/
theorem indepFun_oracleCenteredError_meanDifference_residualSumSquaresPair
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) (θ : ℝ) :
    IndepFun
      (fun ω =>
        (oracleCenteredErrorU ν₁ ν₂ μ θ X Y ω,
          meanDifferenceU ν₁ ν₂ X Y ω))
      (fun ω =>
        (residualSumSquaresN ν₁ X ω,
          residualSumSquaresN ν₂ Y ω)) P := by
  have hcomp :=
    h.indepFun_sampleMeans_residualSumSquares.comp
      (show Measurable
          (fun m : ℝ × ℝ =>
            (m.1 + θ * (m.2 - m.1) - μ, m.2 - m.1)) by
        fun_prop)
      measurable_id
  apply hcomp.congr
  · filter_upwards [] with ω
    rfl
  · filter_upwards [] with ω
    rfl

/-- Every fixed-weight centered error is independent of both residual sums of squares. -/
theorem indepFun_oracleCenteredError_residualSumSquares
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) (θ : ℝ) :
    IndepFun
      (oracleCenteredErrorU ν₁ ν₂ μ θ X Y)
      (fun ω =>
        (residualSumSquaresN ν₁ X ω,
          residualSumSquaresN ν₂ Y ω)) P := by
  have hcomp :=
    (h.indepFun_oracleCenteredError_meanDifference_residualSumSquaresPair θ).comp
      (show Measurable (fun z : ℝ × ℝ => z.1) by fun_prop)
      measurable_id
  apply hcomp.congr
  · filter_upwards [] with ω
    rfl
  · filter_upwards [] with ω
    rfl

end TwoNormalSamplesU

end

end GraybillDeal
