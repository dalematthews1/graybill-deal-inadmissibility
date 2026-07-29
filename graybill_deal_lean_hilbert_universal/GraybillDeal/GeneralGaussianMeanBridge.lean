import GraybillDeal.GeneralCanonical
import GraybillDeal.GeneralNormalSample
import GraybillDeal.GammaMoments

/-!
# Generic Gaussian mean-difference bridge

For two samples with residual degrees of freedom `ν`, hence sample size
`ν + 1`, the difference of their means has variance

`varianceSum / (ν + 1)`.

This file standardizes and squares that difference, obtaining the canonical
`Gamma(1/2,1/2)` coordinate.  It also transports the existing independence
of the mean difference and the two residual sums of squares through the
standardized-square map.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

@[fun_prop]
theorem measurable_generalStandardizedDifference
    (ν varianceSum : ℝ) {D : Ω → ℝ} (hD : Measurable D) :
    Measurable
      (fun ω =>
        generalStandardizedDifference ν varianceSum (D ω)) := by
  unfold generalStandardizedDifference
  fun_prop

@[fun_prop]
theorem measurable_generalStandardizedMeanDifferenceN
    (ν : ℕ) {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
    (hX : ∀ g i, Measurable (X g i)) (varianceSum : ℝ) :
    Measurable
      (fun ω =>
        generalStandardizedDifference (ν : ℝ) varianceSum
          (meanDifferenceN ν X ω)) :=
  measurable_generalStandardizedDifference _ _
    (measurable_meanDifferenceN hX)

/--
If `D ~ N(0, varianceSum/(ν+1))`, then
`(ν+1)D²/varianceSum ~ Gamma(1/2,1/2)`.
-/
theorem hasLaw_generalStandardizedDifference_of_gaussian
    (ν : ℕ) (varianceSum : ℝ) (D : Ω → ℝ)
    (Pmeasure : Measure Ω)
    (hvarianceSum : 0 < varianceSum)
    (hD :
      HasLaw D
        (gaussianReal 0
          (varianceSum / ((ν : ℝ) + 1)).toNNReal) Pmeasure) :
    HasLaw
      (fun ω =>
        generalStandardizedDifference (ν : ℝ) varianceSum (D ω))
      (gammaMeasure (1 / 2) (1 / 2)) Pmeasure := by
  let c : ℝ := √(((ν : ℝ) + 1) / varianceSum)
  have hcarg : 0 ≤ ((ν : ℝ) + 1) / varianceSum := by positivity
  have hc_sq :
      c ^ 2 = ((ν : ℝ) + 1) / varianceSum := by
    dsimp only [c]
    exact Real.sq_sqrt hcarg
  have hscaled :=
    ProbabilityTheory.gaussianReal_const_mul hD c
  have hZ :
      HasLaw (fun ω => c * D ω) (gaussianReal 0 1) Pmeasure := by
    convert hscaled using 1
    congr 1
    · ring
    · apply NNReal.eq
      simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one]
      rw [Real.coe_toNNReal _ (by positivity), hc_sq]
      field_simp
  have hZsq := hasLaw_sq_standardGaussian hZ
  apply hZsq.congr
  filter_upwards [] with ω
  unfold generalStandardizedDifference
  rw [mul_pow, hc_sq]
  field_simp

private theorem integrable_comp_of_hasLaw_generalMeanBridge
    {Y : Ω → ℝ} {μ : Measure ℝ} {Pmeasure : Measure Ω}
    {f : ℝ → ℝ}
    (hY : HasLaw Y μ Pmeasure) (hf : Integrable f μ) :
    Integrable (fun ω => f (Y ω)) Pmeasure := by
  have hfmap : Integrable f (Pmeasure.map Y) := by
    rw [hY.map_eq]
    exact hf
  simpa only [Function.comp_def] using
    (integrable_map_measure hfmap.aestronglyMeasurable
      hY.aemeasurable).mp hfmap

/-- A variable with the canonical squared-normal law is integrable. -/
theorem integrable_of_hasLaw_gamma_half_half
    {V : Ω → ℝ} {Pmeasure : Measure Ω}
    (hV :
      HasLaw V (gammaMeasure (1 / 2) (1 / 2)) Pmeasure) :
    Integrable V Pmeasure := by
  have hv :
      Integrable (fun x : ℝ => x)
        (gammaMeasure (1 / 2) (1 / 2)) := by
    simpa only [Real.rpow_one] using
      (integrable_rpow_gammaMeasure
      (a := (1 / 2 : ℝ)) (r := (1 / 2 : ℝ)) (q := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num))
  simpa only using
    (integrable_comp_of_hasLaw_generalMeanBridge
      (f := fun x : ℝ => x) hV hv)

/-- The square of a variable with the canonical squared-normal law is integrable. -/
theorem integrable_sq_of_hasLaw_gamma_half_half
    {V : Ω → ℝ} {Pmeasure : Measure Ω}
    (hV :
      HasLaw V (gammaMeasure (1 / 2) (1 / 2)) Pmeasure) :
    Integrable (fun ω => V ω ^ 2) Pmeasure := by
  have hv :
      Integrable (fun x : ℝ => x ^ 2)
        (gammaMeasure (1 / 2) (1 / 2)) := by
    convert integrable_rpow_gammaMeasure
      (a := (1 / 2 : ℝ)) (r := (1 / 2 : ℝ)) (q := (2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) using 1
    funext x
    rw [Real.rpow_two]
  exact
    integrable_comp_of_hasLaw_generalMeanBridge
      (f := fun x : ℝ => x ^ 2) hV hv

/-- The cube of a variable with the canonical squared-normal law is integrable. -/
theorem integrable_cube_of_hasLaw_gamma_half_half
    {V : Ω → ℝ} {Pmeasure : Measure Ω}
    (hV :
      HasLaw V (gammaMeasure (1 / 2) (1 / 2)) Pmeasure) :
    Integrable (fun ω => V ω ^ 3) Pmeasure := by
  have hv :
      Integrable (fun x : ℝ => x ^ 3)
        (gammaMeasure (1 / 2) (1 / 2)) := by
    convert integrable_rpow_gammaMeasure
      (a := (1 / 2 : ℝ)) (r := (1 / 2 : ℝ)) (q := (3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) using 1
    funext x
    norm_num [Real.rpow_natCast]
  exact
    integrable_comp_of_hasLaw_generalMeanBridge
      (f := fun x : ℝ => x ^ 3) hV hv

namespace TwoNormalSamplesN

variable {ν : ℕ}
  {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}

/--
The standardized squared difference of the two raw sample means has the
canonical `Gamma(1/2,1/2)` law.
-/
theorem hasLaw_generalStandardizedMeanDifference
    (h : TwoNormalSamplesN ν X P μ variance)
    (hvarianceSum :
      0 < (variance 0 : ℝ) + (variance 1 : ℝ)) :
    HasLaw
      (fun ω =>
        generalStandardizedDifference (ν : ℝ)
          ((variance 0 : ℝ) + variance 1)
          (meanDifferenceN ν X ω))
      (gammaMeasure (1 / 2) (1 / 2)) P := by
  have hD :
      HasLaw (meanDifferenceN ν X)
        (gaussianReal 0
          ((((variance 0 : ℝ) + variance 1) /
            ((ν : ℝ) + 1))).toNNReal) P := by
    convert h.hasLaw_meanDifference using 1
    congr 1
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by positivity)]
    simp
  exact
    hasLaw_generalStandardizedDifference_of_gaussian
      ν ((variance 0 : ℝ) + variance 1)
        (meanDifferenceN ν X) P hvarianceSum hD

/-- The standardized squared mean difference is a.e. measurable. -/
theorem aemeasurable_generalStandardizedMeanDifference
    (h : TwoNormalSamplesN ν X P μ variance)
    (hvarianceSum :
      0 < (variance 0 : ℝ) + (variance 1 : ℝ)) :
    AEMeasurable
      (fun ω =>
        generalStandardizedDifference (ν : ℝ)
          ((variance 0 : ℝ) + variance 1)
          (meanDifferenceN ν X ω)) P :=
  (h.hasLaw_generalStandardizedMeanDifference hvarianceSum).aemeasurable

/-- The standardized squared mean difference is integrable. -/
theorem integrable_generalStandardizedMeanDifference
    (h : TwoNormalSamplesN ν X P μ variance)
    (hvarianceSum :
      0 < (variance 0 : ℝ) + (variance 1 : ℝ)) :
    Integrable
      (fun ω =>
        generalStandardizedDifference (ν : ℝ)
          ((variance 0 : ℝ) + variance 1)
          (meanDifferenceN ν X ω)) P :=
  integrable_of_hasLaw_gamma_half_half
    (h.hasLaw_generalStandardizedMeanDifference hvarianceSum)

/-- The square of the standardized squared mean difference is integrable. -/
theorem integrable_sq_generalStandardizedMeanDifference
    (h : TwoNormalSamplesN ν X P μ variance)
    (hvarianceSum :
      0 < (variance 0 : ℝ) + (variance 1 : ℝ)) :
    Integrable
      (fun ω =>
        (generalStandardizedDifference (ν : ℝ)
          ((variance 0 : ℝ) + variance 1)
          (meanDifferenceN ν X ω)) ^ 2) P :=
  integrable_sq_of_hasLaw_gamma_half_half
    (h.hasLaw_generalStandardizedMeanDifference hvarianceSum)

/-- The cube of the standardized squared mean difference is integrable. -/
theorem integrable_cube_generalStandardizedMeanDifference
    (h : TwoNormalSamplesN ν X P μ variance)
    (hvarianceSum :
      0 < (variance 0 : ℝ) + (variance 1 : ℝ)) :
    Integrable
      (fun ω =>
        (generalStandardizedDifference (ν : ℝ)
          ((variance 0 : ℝ) + variance 1)
          (meanDifferenceN ν X ω)) ^ 3) P :=
  integrable_cube_of_hasLaw_gamma_half_half
    (h.hasLaw_generalStandardizedMeanDifference hvarianceSum)

/--
The standardized squared mean difference is jointly independent of the two
raw residual sums of squares.
-/
theorem indepFun_generalStandardizedDifference_residualSumSquares
    (h : TwoNormalSamplesN ν X P μ variance)
    (varianceSum : ℝ) :
    IndepFun
      (fun ω =>
        generalStandardizedDifference (ν : ℝ) varianceSum
          (meanDifferenceN ν X ω))
      (fun ω =>
        (residualSumSquaresN ν (X 0) ω,
          residualSumSquaresN ν (X 1) ω)) P := by
  have hout :=
    h.indepFun_meanDifference_residualSumSquares.comp
      (show Measurable
          (fun d : ℝ =>
            generalStandardizedDifference (ν : ℝ) varianceSum d) by
        unfold generalStandardizedDifference
        fun_prop)
      measurable_id
  apply hout.congr
  · filter_upwards [] with ω
    rfl
  · filter_upwards [] with ω
    rfl

/--
The same independence after dividing each residual sum by its population
variance.
-/
theorem indepFun_generalStandardizedDifference_scaledResidualSumSquares
    (h : TwoNormalSamplesN ν X P μ variance)
    (varianceSum : ℝ) :
    IndepFun
      (fun ω =>
        generalStandardizedDifference (ν : ℝ) varianceSum
          (meanDifferenceN ν X ω))
      (fun ω =>
        (scaledResidualSumSquaresN ν (variance 0 : ℝ) (X 0) ω,
          scaledResidualSumSquaresN ν (variance 1 : ℝ) (X 1) ω)) P := by
  let scalePair : ℝ × ℝ → ℝ × ℝ := fun r =>
    (r.1 / (variance 0 : ℝ), r.2 / (variance 1 : ℝ))
  have hout :=
    (h.indepFun_generalStandardizedDifference_residualSumSquares
      varianceSum).comp measurable_id
        (show Measurable scalePair by
          dsimp only [scalePair]
          fun_prop)
  apply hout.congr
  · filter_upwards [] with ω
    rfl
  · filter_upwards [] with ω
    rfl

end TwoNormalSamplesN

end

end GraybillDeal
