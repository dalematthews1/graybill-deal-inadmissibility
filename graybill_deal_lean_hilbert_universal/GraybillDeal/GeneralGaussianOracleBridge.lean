import GraybillDeal.GeneralNormalSample
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Generic Gaussian oracle-error bridge

For two independent Gaussian sample means of samples of size `ν + 1`, this
file proves that the known-variance oracle error is independent of their
difference, is square integrable, and has mean zero.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/--
The known-variance oracle error from two independent Gaussian sample means
is independent of their difference.
-/
theorem indepFun_oracleCentered_meanDifferenceN
    (ν : ℕ) (μ : ℝ) (variance₁ variance₂ : NNReal)
    (Xbar Ybar : Ω → ℝ) (Pmeasure : Measure Ω)
    (hvarianceSum :
      0 < (variance₁ : ℝ) + (variance₂ : ℝ))
    (hX :
      HasLaw Xbar
        (gaussianReal μ (variance₁ / (ν + 1))) Pmeasure)
    (hY :
      HasLaw Ybar
        (gaussianReal μ (variance₂ / (ν + 1))) Pmeasure)
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
  have hjoint := hXY.hasGaussianLaw hGX hGY
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
  have hcovXY : covariance Xbar Ybar Pmeasure = 0 :=
    hXY.covariance_eq_zero hX2 hY2
  have hcovYX : covariance Ybar Xbar Pmeasure = 0 := by
    rw [covariance_comm, hcovXY]
  have hvarX :
      variance Xbar Pmeasure =
        (variance₁ : ℝ) / ((ν : ℝ) + 1) := by
    rw [hX.variance_eq, variance_id_gaussianReal]
    simp [Nat.cast_add, Nat.cast_one]
  have hvarY :
      variance Ybar Pmeasure =
        (variance₂ : ℝ) / ((ν : ℝ) + 1) := by
    rw [hY.variance_eq, variance_id_gaussianReal]
    simp [Nat.cast_add, Nat.cast_one]
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
The generic oracle-centered error is square integrable and has expectation
zero.
-/
theorem oracleCentered_integrable_sq_and_integral_zeroN
    (ν : ℕ) (μ : ℝ) (variance₁ variance₂ : NNReal)
    (Xbar Ybar : Ω → ℝ) (Pmeasure : Measure Ω)
    (hX :
      HasLaw Xbar
        (gaussianReal μ (variance₁ / (ν + 1))) Pmeasure)
    (hY :
      HasLaw Ybar
        (gaussianReal μ (variance₂ / (ν + 1))) Pmeasure) :
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
  · exact (memLp_two_iff_integrable_sq hC2.1).1 hC2
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

end

end GraybillDeal
