import GraybillDeal.Canonical
import GraybillDeal.NormalSquare
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# From a Gaussian mean difference to the canonical gamma component

This file isolates the one-dimensional part of the raw-normal bridge.  Once
the difference of the two sample means is known to be Gaussian with variance
`varianceSum / 13`, standardization and squaring give exactly the canonical
`Gamma(1/2,1/2)` variable.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/--
The difference of two independent sample-mean Gaussians has variance equal
to the sum of their variances.  The `13` in the parameters records the raw
sample size.
-/
theorem hasLaw_difference_of_indep_gaussians13
    (μ : ℝ) (variance₁ variance₂ : NNReal)
    (Xbar Ybar : Ω → ℝ) (Pmeasure : Measure Ω)
    (hX :
      HasLaw Xbar (gaussianReal μ (variance₁ / 13)) Pmeasure)
    (hY :
      HasLaw Ybar (gaussianReal μ (variance₂ / 13)) Pmeasure)
    (hXY : IndepFun Xbar Ybar Pmeasure) :
    HasLaw (fun ω => Ybar ω - Xbar ω)
      (gaussianReal 0 ((variance₁ + variance₂) / 13)) Pmeasure := by
  have hYnegX :
      IndepFun Ybar (fun ω => -Xbar ω) Pmeasure := by
    have hout := hXY.symm.comp measurable_id measurable_neg
    simpa [Function.comp_def] using hout
  have hnegX :=
    ProbabilityTheory.gaussianReal_neg hX
  refine
    { aemeasurable := by fun_prop
      map_eq := ?_ }
  have hadd :=
    ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
      hYnegX hY.map_eq hnegX.map_eq
  rw [show (fun ω => Ybar ω - Xbar ω) =
      Ybar + (fun ω => -Xbar ω) by
    funext ω
    exact sub_eq_add_neg _ _]
  simpa only [neg_zero, add_neg_cancel, add_zero, add_comm, add_div] using hadd

/--
For two independent Gaussian sample means, the known-variance oracle error
is independent of their difference.  This is the two-dimensional Gaussian
orthogonality calculation used by the final risk decomposition.
-/
theorem indepFun_oracleCentered_meanDifference13
    (μ : ℝ) (variance₁ variance₂ : NNReal)
    (Xbar Ybar : Ω → ℝ) (Pmeasure : Measure Ω)
    (hvarianceSum :
      0 < (variance₁ : ℝ) + (variance₂ : ℝ))
    (hX :
      HasLaw Xbar (gaussianReal μ (variance₁ / 13)) Pmeasure)
    (hY :
      HasLaw Ybar (gaussianReal μ (variance₂ / 13)) Pmeasure)
    (hXY : IndepFun Xbar Ybar Pmeasure) :
    IndepFun
      (fun ω =>
        Xbar ω
          + ((variance₁ : ℝ) / ((variance₁ : ℝ) + (variance₂ : ℝ)))
            * (Ybar ω - Xbar ω) - μ)
      (fun ω => Ybar ω - Xbar ω) Pmeasure := by
  let θ : ℝ :=
    (variance₁ : ℝ) / ((variance₁ : ℝ) + (variance₂ : ℝ))
  let C0 : Ω → ℝ := fun ω =>
    (1 - θ) * Xbar ω + θ * Ybar ω
  let D : Ω → ℝ := fun ω => Ybar ω - Xbar ω
  have hGX := hX.hasGaussianLaw
  have hGY := hY.hasGaussianLaw
  have hjoint :=
    hXY.hasGaussianLaw hGX hGY
  let T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (((1 - θ) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + θ • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ
        - ContinuousLinearMap.fst ℝ ℝ ℝ))
  have hCD : HasGaussianLaw (fun ω => (C0 ω, D ω)) Pmeasure := by
    have hmap := hjoint.map_fun T
    apply hmap.congr
    filter_upwards [] with ω
    ext <;> simp [T, C0, D]
  letI : IsProbabilityMeasure Pmeasure := hX.isProbabilityMeasure
  have hX2 : MemLp Xbar 2 Pmeasure := hGX.memLp_two
  have hY2 : MemLp Ybar 2 Pmeasure := hGY.memLp_two
  have hcovXY :
      covariance Xbar Ybar Pmeasure = 0 :=
    hXY.covariance_eq_zero hX2 hY2
  have hcovYX :
      covariance Ybar Xbar Pmeasure = 0 := by
    rw [covariance_comm, hcovXY]
  have hvarX :
      variance Xbar Pmeasure = (variance₁ : ℝ) / 13 := by
    rw [hX.variance_eq, variance_id_gaussianReal]
    simp
  have hvarY :
      variance Ybar Pmeasure = (variance₂ : ℝ) / 13 := by
    rw [hY.variance_eq, variance_id_gaussianReal]
    simp
  have hC0D : covariance C0 D Pmeasure = 0 := by
    change
      covariance
          ((fun ω => (1 - θ) * Xbar ω)
            + (fun ω => θ * Ybar ω))
          (Ybar - Xbar) Pmeasure = 0
    rw [covariance_add_left
      (hX2.const_mul _) (hY2.const_mul _) (hY2.sub hX2)]
    rw [covariance_const_mul_left, covariance_const_mul_left]
    rw [covariance_sub_right hX2 hY2 hX2,
      covariance_sub_right hY2 hY2 hX2]
    rw [hcovXY, hcovYX,
      covariance_self hX.aemeasurable,
      covariance_self hY.aemeasurable,
      hvarX, hvarY]
    dsimp only [θ]
    field_simp [ne_of_gt hvarianceSum]
    ring
  have hC0_indep_D :=
    hCD.indepFun_of_covariance_eq_zero hC0D
  have hout := hC0_indep_D.comp
    (show Measurable (fun x : ℝ => x - μ) by fun_prop)
    measurable_id
  apply hout.congr
  · filter_upwards [] with ω
    dsimp only [Function.comp_apply, C0, θ]
    ring
  · filter_upwards [] with ω
    rfl

/--
The oracle-centered error from two Gaussian sample means is square
integrable and has expectation zero.
-/
theorem oracleCentered_integrable_sq_and_integral_zero13
    (μ : ℝ) (variance₁ variance₂ : NNReal)
    (Xbar Ybar : Ω → ℝ) (Pmeasure : Measure Ω)
    (hX :
      HasLaw Xbar (gaussianReal μ (variance₁ / 13)) Pmeasure)
    (hY :
      HasLaw Ybar (gaussianReal μ (variance₂ / 13)) Pmeasure) :
    Integrable
        (fun ω =>
          (Xbar ω
            + ((variance₁ : ℝ) / ((variance₁ : ℝ) + (variance₂ : ℝ)))
              * (Ybar ω - Xbar ω) - μ) ^ 2) Pmeasure
      ∧
    (∫ ω,
      Xbar ω
        + ((variance₁ : ℝ) / ((variance₁ : ℝ) + (variance₂ : ℝ)))
          * (Ybar ω - Xbar ω) - μ ∂Pmeasure) = 0 := by
  let θ : ℝ :=
    (variance₁ : ℝ) / ((variance₁ : ℝ) + (variance₂ : ℝ))
  let C : Ω → ℝ := fun ω =>
    Xbar ω + θ * (Ybar ω - Xbar ω) - μ
  have hGX := hX.hasGaussianLaw
  have hGY := hY.hasGaussianLaw
  letI : IsProbabilityMeasure Pmeasure := hX.isProbabilityMeasure
  have hX2 : MemLp Xbar 2 Pmeasure := hGX.memLp_two
  have hY2 : MemLp Ybar 2 Pmeasure := hGY.memLp_two
  have hC2 : MemLp C 2 Pmeasure := by
    have hraw :=
      (hX2.add ((hY2.sub hX2).const_mul θ)).sub
        (memLp_const (μ := Pmeasure) μ)
    apply hraw.ae_eq
    filter_upwards [] with ω
    simp [C]
  constructor
  · exact
      (memLp_two_iff_integrable_sq hC2.1).1 hC2
  · have hXint : Integrable Xbar Pmeasure := hGX.integrable
    have hYint : Integrable Ybar Pmeasure := hGY.integrable
    change ∫ ω, C ω ∂Pmeasure = 0
    have hCeq :
        C =
          (Xbar + (fun ω => θ * (Ybar ω - Xbar ω)))
            - (fun _ => μ) := by
      funext ω
      rfl
    rw [hCeq]
    simp only [Pi.sub_apply, Pi.add_apply]
    have hdiff :
        Integrable (fun ω => Ybar ω - Xbar ω) Pmeasure := by
      rw [show (fun ω => Ybar ω - Xbar ω) = Ybar - Xbar by
        funext ω
        rfl]
      exact hYint.sub hXint
    have hscaled :
        Integrable (fun ω => θ * (Ybar ω - Xbar ω)) Pmeasure :=
      hdiff.const_mul θ
    have hinner :
        Integrable
          (fun ω => Xbar ω + θ * (Ybar ω - Xbar ω)) Pmeasure :=
      hXint.add hscaled
    rw [integral_sub hinner (integrable_const μ)]
    rw [integral_add hXint hscaled,
      integral_const_mul, integral_sub hYint hXint,
      hX.integral_eq, hY.integral_eq]
    simp only [integral_id_gaussianReal]
    simp

/--
If `D ~ N(0, varianceSum/13)`, then `13 D² / varianceSum` has
`Gamma(1/2,1/2)` shape-rate law.
-/
theorem hasLaw_standardizedDifference13_of_gaussian
    (varianceSum : ℝ) (D : Ω → ℝ) (Pmeasure : Measure Ω)
    (hvarianceSum : 0 < varianceSum)
    (hD :
      HasLaw D
        (gaussianReal 0 (varianceSum / 13).toNNReal) Pmeasure) :
    HasLaw
      (fun ω => standardizedDifference13 varianceSum (D ω))
      (gammaMeasure (1 / 2) (1 / 2)) Pmeasure := by
  let c : ℝ := √(13 / varianceSum)
  have hcarg : 0 ≤ 13 / varianceSum := by positivity
  have hc_sq : c ^ 2 = 13 / varianceSum := by
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
  unfold standardizedDifference13
  rw [mul_pow, hc_sq]
  field_simp

end

end GraybillDeal
