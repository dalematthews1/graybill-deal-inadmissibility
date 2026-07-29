import GraybillDeal.UnequalNormalSample

/-!
# Cochran's theorem for a single Gaussian sample, and for two samples of
unequal sizes

The equal-size development proves the Cochran law inside the two-sample
structure `TwoNormalSamplesN`, where both samples share one index type.
For unequal sizes the two samples have different index types, so this file
first isolates the *single-sample* statement:

if `X i ~ N(μ, v)` for `i : Fin (ν + 1)` are mutually independent and
`v > 0`, then

```
RSS(X) / v  ~  Gamma(ν / 2, 1 / 2),
```

i.e. the chi-square law on `ν` degrees of freedom (`GaussianSampleN`
below).  The result is then applied twice — once to each sample of a
`TwoNormalSamplesU` model — giving the two chi-square laws with *distinct*
shapes `ν₁ / 2` and `ν₂ / 2`, together with their independence.

The residual-contrast machinery (`residualContrastN`,
`standardizedResidualContrastN`, the orthonormal basis of the residual
hyperplane, and
`sum_sq_standardizedResidualContrastN_eq_scaledResidualSumSquaresN`) is
already index-generic in `GeneralNormalSample.lean` and is reused verbatim.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- One sample of `ν + 1` mutually independent `N(μ, v)` observations. -/
structure GaussianSampleN
    (ν : ℕ) (X : Fin (ν + 1) → Ω → ℝ)
    (P : Measure Ω) (μ : ℝ) (v : NNReal) : Prop where
  law : ∀ i, HasLaw (X i) (gaussianReal μ v) P
  indep : iIndepFun X P

namespace GaussianSampleN

variable {ν : ℕ} {X : Fin (ν + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {v : NNReal}

theorem hasGaussianLaw_coord
    (h : GaussianSampleN ν X P μ v) (i : Fin (ν + 1)) :
    HasGaussianLaw (X i) P :=
  (h.law i).hasGaussianLaw

theorem memLp_two_coord
    (h : GaussianSampleN ν X P μ v) (i : Fin (ν + 1)) :
    MemLp (X i) 2 P :=
  (h.hasGaussianLaw_coord i).memLp_two

theorem integral_coord
    (h : GaussianSampleN ν X P μ v) (i : Fin (ν + 1)) :
    ∫ ω, X i ω ∂P = μ := by
  rw [(h.law i).integral_eq, integral_id_gaussianReal]

theorem variance_coord
    (h : GaussianSampleN ν X P μ v) (i : Fin (ν + 1)) :
    ProbabilityTheory.variance (X i) P = v := by
  rw [(h.law i).variance_eq, variance_id_gaussianReal]

/-- The covariance matrix of the sample is `v` times the identity. -/
theorem covariance_coord
    (h : GaussianSampleN ν X P μ v) (i j : Fin (ν + 1)) :
    covariance (X i) (X j) P = if i = j then (v : ℝ) else 0 := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  by_cases heq : i = j
  · subst heq
    rw [if_pos rfl, covariance_self (h.law i).aemeasurable,
      h.variance_coord]
  · rw [if_neg heq]
    exact (h.indep.indepFun heq).covariance_eq_zero
      (h.memLp_two_coord i) (h.memLp_two_coord j)

/-- The whole sample is one jointly Gaussian vector. -/
theorem hasGaussianLaw_sample
    (h : GaussianSampleN ν X P μ v) :
    HasGaussianLaw (fun ω i => X i ω) P :=
  h.indep.hasGaussianLaw fun i => h.hasGaussianLaw_coord i

/-- The vector of orthonormal residual contrasts is jointly Gaussian. -/
theorem hasGaussianLaw_residualContrasts
    (h : GaussianSampleN ν X P μ v) :
    HasGaussianLaw (fun ω k => residualContrastN ν X k ω) P := by
  have hmap := h.hasGaussianLaw_sample.map_fun (residualContrastLinearN ν)
  apply hmap.congr
  filter_upwards [] with ω
  rfl

/-- Residual contrasts are centered: the contrast coefficients sum to zero,
so the common mean drops out. -/
theorem integral_residualContrast
    (h : GaussianSampleN ν X P μ v) (k : Fin ν) :
    ∫ ω, residualContrastN ν X k ω ∂P = 0 := by
  rw [show residualContrastN ν X k =
      fun ω => ∑ i, residualContrastCoefficientN ν k i * X i ω by
    ext ω
    simp]
  rw [integral_finsetSum Finset.univ]
  · simp_rw [integral_const_mul, h.integral_coord]
    rw [← Finset.sum_mul, sum_residualContrastCoefficientN]
    simp
  · intro i _
    exact (h.hasGaussianLaw_coord i).integrable.const_mul _

/-- Orthonormality of the contrast basis transports to the covariance
matrix: the contrasts are uncorrelated with common variance `v`. -/
theorem covariance_residualContrast
    (h : GaussianSampleN ν X P μ v) (k l : Fin ν) :
    covariance (residualContrastN ν X k) (residualContrastN ν X l) P =
      (v : ℝ) * (if k = l then 1 else 0) := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  rw [show residualContrastN ν X k =
      fun ω => ∑ i, residualContrastCoefficientN ν k i * X i ω by
    ext ω
    simp]
  rw [show residualContrastN ν X l =
      fun ω => ∑ i, residualContrastCoefficientN ν l i * X i ω by
    ext ω
    simp]
  rw [covariance_fun_sum_fun_sum
    (fun i => (h.memLp_two_coord i).const_mul _)
    (fun i => (h.memLp_two_coord i).const_mul _)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right,
    h.covariance_coord]
  simp_rw [mul_ite, mul_zero, Fintype.sum_ite_eq]
  rw [show
    (∑ i, residualContrastCoefficientN ν k i *
      (residualContrastCoefficientN ν l i * (v : ℝ))) =
        (v : ℝ) *
          ∑ i, residualContrastCoefficientN ν k i *
            residualContrastCoefficientN ν l i by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
  rw [sum_mul_residualContrastCoefficientN]
  by_cases hkl : k = l <;> simp [hkl]

theorem hasGaussianLaw_standardizedResidualContrasts
    (h : GaussianSampleN ν X P μ v) :
    HasGaussianLaw
      (fun ω k => standardizedResidualContrastN ν (v : ℝ) X k ω) P := by
  have hscaled :=
    h.hasGaussianLaw_residualContrasts.fun_smul (√(v : ℝ))⁻¹
  apply hscaled.congr
  filter_upwards [] with ω
  ext k
  simp [standardizedResidualContrastN, div_eq_mul_inv,
    Pi.smul_apply, smul_eq_mul, mul_comm]

theorem integral_standardizedResidualContrast
    (h : GaussianSampleN ν X P μ v) (k : Fin ν) :
    ∫ ω, standardizedResidualContrastN ν (v : ℝ) X k ω ∂P = 0 := by
  unfold standardizedResidualContrastN
  rw [integral_div, h.integral_residualContrast]
  simp

theorem covariance_standardizedResidualContrast
    (h : GaussianSampleN ν X P μ v) (hv : 0 < (v : ℝ)) (k l : Fin ν) :
    covariance
      (standardizedResidualContrastN ν (v : ℝ) X k)
      (standardizedResidualContrastN ν (v : ℝ) X l) P =
      if k = l then 1 else 0 := by
  unfold standardizedResidualContrastN
  rw [covariance_fun_div_left, covariance_fun_div_right,
    h.covariance_residualContrast]
  by_cases hkl : k = l
  · rw [if_pos hkl]
    simp only [mul_one]
    rw [div_div, ← pow_two, Real.sq_sqrt hv.le,
      div_self (ne_of_gt hv)]
  · simp [hkl]

/-- Each standardized residual contrast is a standard Gaussian. -/
theorem hasLaw_standardizedResidualContrast
    (h : GaussianSampleN ν X P μ v) (hv : 0 < (v : ℝ)) (k : Fin ν) :
    HasLaw (standardizedResidualContrastN ν (v : ℝ) X k)
      (gaussianReal 0 1) P := by
  have hgauss := h.hasGaussianLaw_standardizedResidualContrasts.eval k
  refine
    { aemeasurable := hgauss.aemeasurable
      map_eq := ?_ }
  rw [hgauss.map_eq_gaussianReal,
    h.integral_standardizedResidualContrast]
  have hvar :
      ProbabilityTheory.variance
        (standardizedResidualContrastN ν (v : ℝ) X k) P = 1 := by
    rw [← covariance_self hgauss.aemeasurable,
      h.covariance_standardizedResidualContrast hv k k]
    simp
  rw [hvar]
  norm_num

/-- The `ν` standardized residual contrasts are mutually independent. -/
theorem iIndepFun_standardizedResidualContrasts
    (h : GaussianSampleN ν X P μ v) (hv : 0 < (v : ℝ)) :
    iIndepFun
      (fun k ω => standardizedResidualContrastN ν (v : ℝ) X k ω) P := by
  apply h.hasGaussianLaw_standardizedResidualContrasts
    |>.iIndepFun_of_covariance_eq_zero
  intro k l hkl
  rw [h.covariance_standardizedResidualContrast hv k l, if_neg hkl]

/--
**Cochran's theorem, single sample.**  For one sample of `ν + 1`
independent `N(μ, v)` observations with `v > 0`,

```
RSS / v ~ Gamma(ν / 2, 1 / 2),
```

the chi-square law on `ν` degrees of freedom.
-/
theorem hasLaw_scaledResidualSumSquares
    (h : GaussianSampleN ν X P μ v) (hν : 0 < ν) (hv : 0 < (v : ℝ)) :
    HasLaw (scaledResidualSumSquaresN ν (v : ℝ) X)
      (gammaMeasure ((ν : ℝ) / 2) (1 / 2)) P := by
  letI : Nonempty (Fin ν) := Fin.pos_iff_nonempty.mp hν
  have hsum :
      HasLaw
        (fun ω =>
          ∑ k, standardizedResidualContrastN ν (v : ℝ) X k ω ^ 2)
        (gammaMeasure ((ν : ℝ) / 2) (1 / 2)) P := by
    simpa using
      hasLaw_sum_sq_standardGaussian
        (fun k => h.hasLaw_standardizedResidualContrast hv k)
        (h.iIndepFun_standardizedResidualContrasts hv)
  apply hsum.congr
  filter_upwards [] with ω
  exact
    (sum_sq_standardizedResidualContrastN_eq_scaledResidualSumSquaresN
      ν (v : ℝ) hv.le X ω).symm

end GaussianSampleN

namespace TwoNormalSamplesU

variable {ν₁ ν₂ : ℕ}
  {X : Fin (ν₁ + 1) → Ω → ℝ} {Y : Fin (ν₂ + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}

/-- The first sample of an unequal-size model is a Gaussian sample. -/
theorem gaussianSampleX
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    GaussianSampleN ν₁ X P μ v₁ where
  law := h.lawX
  indep := by
    have hpre := h.indep.precomp Sum.inl_injective
    apply hpre.congr
    intro i
    filter_upwards [] with ω
    rfl

/-- The second sample of an unequal-size model is a Gaussian sample. -/
theorem gaussianSampleY
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    GaussianSampleN ν₂ Y P μ v₂ where
  law := h.lawY
  indep := by
    have hpre := h.indep.precomp Sum.inr_injective
    apply hpre.congr
    intro j
    filter_upwards [] with ω
    rfl

/-- **Cochran law for the first sample**: `RSS₁ / v₁ ~ Gamma(ν₁/2, 1/2)`. -/
theorem hasLaw_scaledResidualSumSquaresX
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hν₁ : 0 < ν₁) (hv₁ : 0 < (v₁ : ℝ)) :
    HasLaw (scaledResidualSumSquaresN ν₁ (v₁ : ℝ) X)
      (gammaMeasure ((ν₁ : ℝ) / 2) (1 / 2)) P :=
  h.gaussianSampleX.hasLaw_scaledResidualSumSquares hν₁ hv₁

/-- **Cochran law for the second sample**: `RSS₂ / v₂ ~ Gamma(ν₂/2, 1/2)`.
Note the shape differs from the first sample's whenever `ν₁ ≠ ν₂`; this is
exactly the asymmetry that the unequal-size beta reduction must absorb. -/
theorem hasLaw_scaledResidualSumSquaresY
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hν₂ : 0 < ν₂) (hv₂ : 0 < (v₂ : ℝ)) :
    HasLaw (scaledResidualSumSquaresN ν₂ (v₂ : ℝ) Y)
      (gammaMeasure ((ν₂ : ℝ) / 2) (1 / 2)) P :=
  h.gaussianSampleY.hasLaw_scaledResidualSumSquares hν₂ hv₂

/-- The two residual sums of squares are independent. -/
theorem indepFun_residualSumSquares
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    IndepFun (residualSumSquaresN ν₁ X) (residualSumSquaresN ν₂ Y) P := by
  have hcomp :=
    h.indepFun_sample_pair.comp
      (show Measurable (fun x : Fin (ν₁ + 1) → ℝ =>
          ∑ i, (x i - (∑ j, x j) / (ν₁ + 1)) ^ 2) by fun_prop)
      (show Measurable (fun y : Fin (ν₂ + 1) → ℝ =>
          ∑ i, (y i - (∑ j, y j) / (ν₂ + 1)) ^ 2) by fun_prop)
  apply hcomp.congr
  · filter_upwards [] with ω
    simp [Function.comp_apply, residualSumSquaresN,
      sampleResidualN, sampleMeanN]
  · filter_upwards [] with ω
    simp [Function.comp_apply, residualSumSquaresN,
      sampleResidualN, sampleMeanN]

/-- The two *scaled* residual sums of squares are independent. -/
theorem indepFun_scaledResidualSumSquares
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    IndepFun
      (scaledResidualSumSquaresN ν₁ (v₁ : ℝ) X)
      (scaledResidualSumSquaresN ν₂ (v₂ : ℝ) Y) P := by
  have hcomp :=
    h.indepFun_residualSumSquares.comp
      (show Measurable (fun t : ℝ => t / (v₁ : ℝ)) by fun_prop)
      (show Measurable (fun t : ℝ => t / (v₂ : ℝ)) by fun_prop)
  apply hcomp.congr
  · filter_upwards [] with ω
    rfl
  · filter_upwards [] with ω
    rfl

end TwoNormalSamplesU

end

end GraybillDeal
