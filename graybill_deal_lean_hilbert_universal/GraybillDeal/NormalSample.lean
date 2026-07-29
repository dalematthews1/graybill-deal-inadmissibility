import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Two raw normal samples of size thirteen

This file begins the bridge from the original sampling model to the
canonical beta/gamma summary laws used by the Graybill--Deal risk proof.

The two samples are represented by

`X : Fin 2 → Fin 13 → Ω → ℝ`.

The first index selects the population and the second selects an observation.
`TwoNormalSamples13 X ℙ μ variance` says that all twenty-six observations are
mutually independent and that observation `(g,i)` has law
`N(μ, variance g)`.

This layer deliberately separates the Gaussian linear algebra from Cochran's
theorem.  In particular, it defines the residual sums of squares from which
the chi-square, beta, and gamma variables will subsequently be obtained.
-/

namespace GraybillDeal

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The arithmetic mean of thirteen real observations. -/
def sampleMean13 (X : Fin 13 → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ i, X i ω) / 13

/-- The vector of deviations from the sample mean. -/
def sampleResidual13 (X : Fin 13 → Ω → ℝ) (ω : Ω) (i : Fin 13) : ℝ :=
  X i ω - sampleMean13 X ω

/-- The unnormalised residual sum of squares. -/
def residualSumSquares13 (X : Fin 13 → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i, sampleResidual13 X ω i ^ 2

/-- The usual unbiased sample variance, with divisor `13 - 1 = 12`. -/
def sampleVariance13 (X : Fin 13 → Ω → ℝ) (ω : Ω) : ℝ :=
  residualSumSquares13 X ω / 12

/-- Difference of the second and first sample means. -/
def meanDifference13 (X : Fin 2 → Fin 13 → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleMean13 (X 1) ω - sampleMean13 (X 0) ω

/--
The error of the known-variance estimator
`sampleMean₁ + θ (sampleMean₂ - sampleMean₁)`.
-/
def oracleCenteredError13
    (μ θ : ℝ) (X : Fin 2 → Fin 13 → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleMean13 (X 0) ω + θ * meanDifference13 X ω - μ

/-- The known-variance weight `σ₁²/(σ₁²+σ₂²)`. -/
def oracleVarianceWeight13 (variance : Fin 2 → NNReal) : ℝ :=
  (variance 0 : ℝ) / ((variance 0 : ℝ) + variance 1)

/--
The scaled residual statistic

`U_g = 12 S_g² / variance_g = RSS_g / variance_g`.

Its chi-square law is the remaining Cochran-theorem step.
-/
def scaledResidualSumSquares13
    (variance : ℝ) (X : Fin 13 → Ω → ℝ) (ω : Ω) : ℝ :=
  residualSumSquares13 X ω / variance

/-- The complete raw two-sample normal model. -/
structure TwoNormalSamples13
    (X : Fin 2 → Fin 13 → Ω → ℝ)
    (ℙ : Measure Ω) (μ : ℝ) (variance : Fin 2 → NNReal) : Prop where
  law :
    ∀ g i,
      ProbabilityTheory.HasLaw (X g i)
        (ProbabilityTheory.gaussianReal μ (variance g)) ℙ
  indep :
    ProbabilityTheory.iIndepFun
      (fun gi : Fin 2 × Fin 13 => X gi.1 gi.2) ℙ

@[measurability, fun_prop]
theorem measurable_sampleMean13
    {X : Fin 13 → Ω → ℝ} (hX : ∀ i, Measurable (X i)) :
    Measurable (sampleMean13 X) := by
  unfold sampleMean13
  fun_prop

@[measurability, fun_prop]
theorem measurable_sampleResidual13
    {X : Fin 13 → Ω → ℝ} (hX : ∀ i, Measurable (X i)) :
    Measurable (fun ω => sampleResidual13 X ω) := by
  unfold sampleResidual13
  fun_prop

@[measurability, fun_prop]
theorem measurable_residualSumSquares13
    {X : Fin 13 → Ω → ℝ} (hX : ∀ i, Measurable (X i)) :
    Measurable (residualSumSquares13 X) := by
  unfold residualSumSquares13
  fun_prop

@[measurability, fun_prop]
theorem measurable_sampleVariance13
    {X : Fin 13 → Ω → ℝ} (hX : ∀ i, Measurable (X i)) :
    Measurable (sampleVariance13 X) := by
  unfold sampleVariance13
  fun_prop

@[measurability, fun_prop]
theorem measurable_meanDifference13
    {X : Fin 2 → Fin 13 → Ω → ℝ}
    (hX : ∀ g i, Measurable (X g i)) :
    Measurable (meanDifference13 X) := by
  unfold meanDifference13
  fun_prop

@[measurability, fun_prop]
theorem measurable_oracleCenteredError13
    {X : Fin 2 → Fin 13 → Ω → ℝ}
    (hX : ∀ g i, Measurable (X g i)) (μ θ : ℝ) :
    Measurable (oracleCenteredError13 μ θ X) := by
  unfold oracleCenteredError13
  fun_prop

@[measurability, fun_prop]
theorem measurable_scaledResidualSumSquares13
    {X : Fin 13 → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (variance : ℝ) :
    Measurable (scaledResidualSumSquares13 variance X) := by
  unfold scaledResidualSumSquares13
  fun_prop

theorem sum_sampleResidual13
    (X : Fin 13 → Ω → ℝ) (ω : Ω) :
    ∑ i, sampleResidual13 X ω i = 0 := by
  unfold sampleResidual13 sampleMean13
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem residualSumSquares13_eq
    (X : Fin 13 → Ω → ℝ) (ω : Ω) :
    residualSumSquares13 X ω
      = (∑ i, X i ω ^ 2) - 13 * sampleMean13 X ω ^ 2 := by
  unfold residualSumSquares13 sampleResidual13 sampleMean13
  simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_mul]
  rw [← Finset.mul_sum]
  ring

theorem residualSumSquares13_nonneg
    (X : Fin 13 → Ω → ℝ) (ω : Ω) :
    0 ≤ residualSumSquares13 X ω := by
  unfold residualSumSquares13
  positivity

theorem sampleVariance13_nonneg
    (X : Fin 13 → Ω → ℝ) (ω : Ω) :
    0 ≤ sampleVariance13 X ω := by
  unfold sampleVariance13
  exact div_nonneg (residualSumSquares13_nonneg X ω) (by norm_num)

theorem twelve_mul_sampleVariance13
    (X : Fin 13 → Ω → ℝ) (ω : Ω) :
    12 * sampleVariance13 X ω = residualSumSquares13 X ω := by
  unfold sampleVariance13
  ring

/-- The continuous linear functional taking the arithmetic mean of 13 coordinates. -/
def sampleMeanLinear13 : (Fin 13 → ℝ) →L[ℝ] ℝ :=
  (13⁻¹ : ℝ) • ∑ i, ContinuousLinearMap.proj i

/-- The continuous linear map subtracting the coordinate mean. -/
def sampleResidualLinear13 : (Fin 13 → ℝ) →L[ℝ] (Fin 13 → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj i - sampleMeanLinear13

/-- The joint linear map from a sample to its mean and residual vector. -/
def sampleMeanResidualLinear13 :
    (Fin 13 → ℝ) →L[ℝ] ℝ × (Fin 13 → ℝ) :=
  sampleMeanLinear13.prod sampleResidualLinear13

/-- Split the 26-coordinate raw vector into its two 13-coordinate samples. -/
def splitTwoSamplesLinear13 :
    ((Fin 2 × Fin 13) → ℝ) →L[ℝ]
      ((Fin 13 → ℝ) × (Fin 13 → ℝ)) :=
  (ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (0, i)).prod
  (ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (1, i))

@[simp]
theorem sampleMeanLinear13_apply (x : Fin 13 → ℝ) :
    sampleMeanLinear13 x = (∑ i, x i) / 13 := by
  simp only [sampleMeanLinear13, ContinuousLinearMap.smul_apply,
    Finset.sum_apply, ContinuousLinearMap.coe_sum',
    ContinuousLinearMap.proj_apply, smul_eq_mul, div_eq_mul_inv]
  ring

@[simp]
theorem sampleResidualLinear13_apply (x : Fin 13 → ℝ) (i : Fin 13) :
    sampleResidualLinear13 x i = x i - (∑ j, x j) / 13 := by
  simp [sampleResidualLinear13]

@[simp]
theorem sampleMeanResidualLinear13_apply (x : Fin 13 → ℝ) :
    sampleMeanResidualLinear13 x
      = ((∑ i, x i) / 13, fun i => x i - (∑ j, x j) / 13) := by
  ext <;> simp [sampleMeanResidualLinear13]

@[simp]
theorem splitTwoSamplesLinear13_apply
    (x : (Fin 2 × Fin 13) → ℝ) :
    splitTwoSamplesLinear13 x
      = (fun i => x (0, i), fun i => x (1, i)) := by
  ext <;> simp [splitTwoSamplesLinear13]

namespace TwoNormalSamples13

variable {X : Fin 2 → Fin 13 → Ω → ℝ}
  {ℙ : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}

/-- Every raw observation is a Gaussian random variable. -/
theorem hasGaussianLaw_coord
    (h : TwoNormalSamples13 X ℙ μ variance) (g : Fin 2) (i : Fin 13) :
    ProbabilityTheory.HasGaussianLaw (X g i) ℙ :=
  (h.law g i).hasGaussianLaw

/-- Every raw observation belongs to `L²`. -/
theorem memLp_two_coord
    (h : TwoNormalSamples13 X ℙ μ variance) (g : Fin 2) (i : Fin 13) :
    MemLp (X g i) 2 ℙ :=
  (h.hasGaussianLaw_coord g i).memLp_two

/-- Every raw observation has expectation `μ`. -/
theorem integral_coord
    (h : TwoNormalSamples13 X ℙ μ variance) (g : Fin 2) (i : Fin 13) :
    ∫ ω, X g i ω ∂ℙ = μ := by
  rw [(h.law g i).integral_eq,
    ProbabilityTheory.integral_id_gaussianReal]

/-- Every raw observation has the specified population variance. -/
theorem variance_coord
    (h : TwoNormalSamples13 X ℙ μ variance) (g : Fin 2) (i : Fin 13) :
    ProbabilityTheory.variance (X g i) ℙ = variance g := by
  rw [(h.law g i).variance_eq,
    ProbabilityTheory.variance_id_gaussianReal]

/--
The covariance matrix of the twenty-six raw observations is diagonal, with
the population variance on the diagonal.
-/
theorem covariance_coord
    (h : TwoNormalSamples13 X ℙ μ variance)
    (g k : Fin 2) (i j : Fin 13) :
    ProbabilityTheory.covariance (X g i) (X k j) ℙ
      = if (g, i) = (k, j) then (variance g : ℝ) else 0 := by
  letI : IsProbabilityMeasure ℙ := h.indep.isProbabilityMeasure
  by_cases heq : (g, i) = (k, j)
  · have hg : g = k := congrArg Prod.fst heq
    have hi : i = j := congrArg Prod.snd heq
    subst k
    subst j
    rw [if_pos rfl, ProbabilityTheory.covariance_self (h.law g i).aemeasurable,
      h.variance_coord]
  · rw [if_neg heq]
    exact
      (h.indep.indepFun heq).covariance_eq_zero
        (h.memLp_two_coord g i) (h.memLp_two_coord k j)

/-- All twenty-six raw observations form one jointly Gaussian vector. -/
theorem hasGaussianLaw_all
    (h : TwoNormalSamples13 X ℙ μ variance) :
    ProbabilityTheory.HasGaussianLaw
      (fun ω (gi : Fin 2 × Fin 13) => X gi.1 gi.2 ω) ℙ :=
  h.indep.hasGaussianLaw fun gi =>
    h.hasGaussianLaw_coord gi.1 gi.2

/-- The pair of complete sample vectors is jointly Gaussian. -/
theorem hasGaussianLaw_sample_pair
    (h : TwoNormalSamples13 X ℙ μ variance) :
    ProbabilityTheory.HasGaussianLaw
      (fun ω => (fun i => X 0 i ω, fun i => X 1 i ω)) ℙ := by
  have hmap := h.hasGaussianLaw_all.map_fun splitTwoSamplesLinear13
  apply hmap.congr
  filter_upwards [] with ω
  simp

/-- The two complete sample vectors are independent. -/
theorem indepFun_sample_pair
    (h : TwoNormalSamples13 X ℙ μ variance) :
    ProbabilityTheory.IndepFun
      (fun ω i => X 0 i ω) (fun ω i => X 1 i ω) ℙ := by
  apply h.hasGaussianLaw_sample_pair.indepFun_of_covariance_eval
  intro i j
  rw [h.covariance_coord, if_neg]
  intro heq
  have := congrArg Prod.fst heq
  norm_num at this

/-- The thirteen observations within either sample are jointly Gaussian. -/
theorem hasGaussianLaw_sample
    (h : TwoNormalSamples13 X ℙ μ variance) (g : Fin 2) :
    ProbabilityTheory.HasGaussianLaw (fun ω i => X g i ω) ℙ := by
  have hinj : Function.Injective (fun i : Fin 13 => (g, i)) := by
    intro i j hij
    exact congrArg Prod.snd hij
  exact
    (h.indep.precomp hinj).hasGaussianLaw
      (fun i => h.hasGaussianLaw_coord g i)

/-- The sample mean is Gaussian. -/
theorem hasGaussianLaw_sampleMean
    (h : TwoNormalSamples13 X ℙ μ variance) (g : Fin 2) :
    ProbabilityTheory.HasGaussianLaw (sampleMean13 (X g)) ℙ := by
  have hsum :
      ProbabilityTheory.HasGaussianLaw
        (fun ω => ∑ i, X g i ω) ℙ :=
    (h.hasGaussianLaw_sample g).fun_sum
  have hscaled := hsum.fun_smul (13⁻¹ : ℝ)
  apply hscaled.congr
  filter_upwards [] with ω
  simp only [Pi.smul_apply, smul_eq_mul, sampleMean13, div_eq_mul_inv]
  ring

/-- The sample mean has expectation `μ`. -/
theorem integral_sampleMean
    (h : TwoNormalSamples13 X ℙ μ variance) (g : Fin 2) :
    ∫ ω, sampleMean13 (X g) ω ∂ℙ = μ := by
  unfold sampleMean13
  rw [integral_div]
  rw [integral_finsetSum Finset.univ
    (fun i _ => (h.hasGaussianLaw_coord g i).integrable)]
  simp_rw [h.integral_coord]
  simp

/-- The sample mean has variance `variance g / 13`. -/
theorem variance_sampleMean
    (h : TwoNormalSamples13 X ℙ μ variance) (g : Fin 2) :
    ProbabilityTheory.variance (sampleMean13 (X g)) ℙ
      = (variance g : ℝ) / 13 := by
  letI : IsProbabilityMeasure ℙ := h.indep.isProbabilityMeasure
  change ProbabilityTheory.variance
    (fun ω => (∑ i, X g i ω) * (13 : ℝ)⁻¹) ℙ
      = (variance g : ℝ) / 13
  rw [ProbabilityTheory.variance_mul_const]
  rw [ProbabilityTheory.variance_fun_sum
    (fun i => h.memLp_two_coord g i)]
  simp_rw [h.covariance_coord]
  simp
  ring

/-- Exact law of the sample mean. -/
theorem hasLaw_sampleMean
    (h : TwoNormalSamples13 X ℙ μ variance) (g : Fin 2) :
    ProbabilityTheory.HasLaw (sampleMean13 (X g))
      (ProbabilityTheory.gaussianReal μ (variance g / 13)) ℙ := by
  refine
    { aemeasurable := (h.hasGaussianLaw_sampleMean g).aemeasurable
      map_eq := ?_ }
  rw [(h.hasGaussianLaw_sampleMean g).map_eq_gaussianReal,
    h.integral_sampleMean, h.variance_sampleMean]
  congr 1
  ext
  calc
    ↑((↑(variance g) / 13 : ℝ).toNNReal)
        = (↑(variance g) / 13 : ℝ) :=
      Real.coe_toNNReal _ (by positivity)
    _ = ↑(variance g / 13) := by simp

/-- The two sample means are independent. -/
theorem indepFun_sampleMeans01
    (h : TwoNormalSamples13 X ℙ μ variance) :
    ProbabilityTheory.IndepFun
      (sampleMean13 (X 0)) (sampleMean13 (X 1)) ℙ := by
  have hmeans :=
    h.indepFun_sample_pair.comp
      (show Measurable sampleMeanLinear13 by fun_prop)
      (show Measurable sampleMeanLinear13 by fun_prop)
  apply hmeans.congr
  · filter_upwards [] with ω
    simp [Function.comp_apply, sampleMean13]
  · filter_upwards [] with ω
    simp [Function.comp_apply, sampleMean13]

/-- The difference of sample means is Gaussian. -/
theorem hasGaussianLaw_meanDifference
    (h : TwoNormalSamples13 X ℙ μ variance) :
    ProbabilityTheory.HasGaussianLaw (meanDifference13 X) ℙ := by
  have hpair :
      ProbabilityTheory.HasGaussianLaw
        (fun ω =>
          (sampleMean13 (X 1) ω, sampleMean13 (X 0) ω)) ℙ :=
    h.indepFun_sampleMeans01.symm.hasGaussianLaw
      (h.hasGaussianLaw_sampleMean 1)
      (h.hasGaussianLaw_sampleMean 0)
  apply hpair.fun_sub.congr
  filter_upwards [] with ω
  rfl

/-- The difference of sample means has expectation zero. -/
theorem integral_meanDifference
    (h : TwoNormalSamples13 X ℙ μ variance) :
    ∫ ω, meanDifference13 X ω ∂ℙ = 0 := by
  unfold meanDifference13
  rw [integral_sub
    (h.hasGaussianLaw_sampleMean 1).integrable
    (h.hasGaussianLaw_sampleMean 0).integrable,
    h.integral_sampleMean, h.integral_sampleMean]
  ring

/-- The difference of sample means has variance `(variance₁+variance₂)/13`. -/
theorem variance_meanDifference
    (h : TwoNormalSamples13 X ℙ μ variance) :
    ProbabilityTheory.variance (meanDifference13 X) ℙ
      = ((variance 0 : ℝ) + variance 1) / 13 := by
  letI : IsProbabilityMeasure ℙ := h.indep.isProbabilityMeasure
  have hmean1 : MemLp (sampleMean13 (X 1)) 2 ℙ :=
    (h.hasGaussianLaw_sampleMean 1).memLp_two
  have hmean0 : MemLp (sampleMean13 (X 0)) 2 ℙ :=
    (h.hasGaussianLaw_sampleMean 0).memLp_two
  have hcov :
      ProbabilityTheory.covariance
        (sampleMean13 (X 1)) (sampleMean13 (X 0)) ℙ = 0 :=
    h.indepFun_sampleMeans01.symm.covariance_eq_zero hmean1 hmean0
  unfold meanDifference13
  rw [ProbabilityTheory.variance_fun_sub hmean1 hmean0,
    h.variance_sampleMean, h.variance_sampleMean,
    hcov]
  ring

/-- Exact normal law of `D = sampleMean₂ - sampleMean₁`. -/
theorem hasLaw_meanDifference
    (h : TwoNormalSamples13 X ℙ μ variance) :
    ProbabilityTheory.HasLaw (meanDifference13 X)
      (ProbabilityTheory.gaussianReal 0 ((variance 0 + variance 1) / 13)) ℙ := by
  refine
    { aemeasurable := h.hasGaussianLaw_meanDifference.aemeasurable
      map_eq := ?_ }
  rw [h.hasGaussianLaw_meanDifference.map_eq_gaussianReal,
    h.integral_meanDifference, h.variance_meanDifference]
  congr 1
  ext
  calc
    ↑((((variance 0 : ℝ) + variance 1) / 13).toNNReal)
        = ((variance 0 : ℝ) + variance 1) / 13 :=
      Real.coe_toNNReal _ (by positivity)
    _ = ↑((variance 0 + variance 1) / 13) := by
      simp

/--
For a fixed `θ`, the uncentered oracle estimator and the mean difference are
jointly Gaussian.
-/
theorem hasGaussianLaw_oracleUncentered_meanDifference
    (h : TwoNormalSamples13 X ℙ μ variance) (θ : ℝ) :
    ProbabilityTheory.HasGaussianLaw
      (fun ω =>
        (sampleMean13 (X 0) ω + θ * meanDifference13 X ω,
          meanDifference13 X ω)) ℙ := by
  have hmeans :
      ProbabilityTheory.HasGaussianLaw
        (fun ω =>
          (sampleMean13 (X 0) ω, sampleMean13 (X 1) ω)) ℙ :=
    h.indepFun_sampleMeans01.hasGaussianLaw
      (h.hasGaussianLaw_sampleMean 0)
      (h.hasGaussianLaw_sampleMean 1)
  let d : (ℝ × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ
  let transform : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ + θ • d).prod d
  have hmap := hmeans.map_fun transform
  apply hmap.congr
  filter_upwards [] with ω
  simp [transform, d, meanDifference13]

/-- `Cov(sampleMean₁,D) = -variance₁/13`. -/
theorem covariance_sampleMean0_meanDifference
    (h : TwoNormalSamples13 X ℙ μ variance) :
    ProbabilityTheory.covariance
      (sampleMean13 (X 0)) (meanDifference13 X) ℙ
      = -(variance 0 : ℝ) / 13 := by
  letI : IsProbabilityMeasure ℙ := h.indep.isProbabilityMeasure
  have hmean0 : MemLp (sampleMean13 (X 0)) 2 ℙ :=
    (h.hasGaussianLaw_sampleMean 0).memLp_two
  have hmean1 : MemLp (sampleMean13 (X 1)) 2 ℙ :=
    (h.hasGaussianLaw_sampleMean 1).memLp_two
  have hcross :
      ProbabilityTheory.covariance
        (sampleMean13 (X 0)) (sampleMean13 (X 1)) ℙ = 0 :=
    h.indepFun_sampleMeans01.covariance_eq_zero hmean0 hmean1
  unfold meanDifference13
  rw [ProbabilityTheory.covariance_fun_sub_right
    hmean0 hmean1 hmean0, hcross,
    ProbabilityTheory.covariance_self hmean0.aemeasurable,
    h.variance_sampleMean]
  ring

/-- Covariance formula for the uncentered oracle estimator and `D`. -/
theorem covariance_oracleUncentered_meanDifference
    (h : TwoNormalSamples13 X ℙ μ variance) (θ : ℝ) :
    ProbabilityTheory.covariance
      (fun ω =>
        sampleMean13 (X 0) ω + θ * meanDifference13 X ω)
      (meanDifference13 X) ℙ
      =
    -(variance 0 : ℝ) / 13
      + θ * (((variance 0 : ℝ) + variance 1) / 13) := by
  letI : IsProbabilityMeasure ℙ := h.indep.isProbabilityMeasure
  have hmean0 : MemLp (sampleMean13 (X 0)) 2 ℙ :=
    (h.hasGaussianLaw_sampleMean 0).memLp_two
  have hD : MemLp (meanDifference13 X) 2 ℙ :=
    h.hasGaussianLaw_meanDifference.memLp_two
  rw [show
    (fun ω =>
      sampleMean13 (X 0) ω + θ * meanDifference13 X ω)
      =
    sampleMean13 (X 0) + fun ω => θ * meanDifference13 X ω by rfl]
  rw [ProbabilityTheory.covariance_add_left
    hmean0 (hD.const_mul θ) hD,
    ProbabilityTheory.covariance_const_mul_left,
    h.covariance_sampleMean0_meanDifference,
    ProbabilityTheory.covariance_self hD.aemeasurable,
    h.variance_meanDifference]

/--
At the known-variance weight, the oracle centered error is independent of
the mean difference.
-/
theorem indepFun_oracleCenteredError_meanDifference
    (h : TwoNormalSamples13 X ℙ μ variance)
    (hsum : 0 < (variance 0 : ℝ) + variance 1) :
    ProbabilityTheory.IndepFun
      (oracleCenteredError13 μ (oracleVarianceWeight13 variance) X)
      (meanDifference13 X) ℙ := by
  let θ := oracleVarianceWeight13 variance
  have hcov :
      ProbabilityTheory.covariance
        (fun ω =>
          sampleMean13 (X 0) ω + θ * meanDifference13 X ω)
        (meanDifference13 X) ℙ = 0 := by
    rw [h.covariance_oracleUncentered_meanDifference]
    dsimp only [θ, oracleVarianceWeight13]
    field_simp
    ring
  have hindep :
      ProbabilityTheory.IndepFun
        (fun ω =>
          sampleMean13 (X 0) ω + θ * meanDifference13 X ω)
        (meanDifference13 X) ℙ :=
    (h.hasGaussianLaw_oracleUncentered_meanDifference θ)
      |>.indepFun_of_covariance_eq_zero hcov
  have hcomp :=
    hindep.comp
      (show Measurable (fun x : ℝ => x - μ) by fun_prop)
      measurable_id
  apply hcomp.congr
  · filter_upwards [] with ω
    rfl
  · filter_upwards [] with ω
    rfl

/-- The sample mean together with the full residual vector is jointly Gaussian. -/
theorem hasGaussianLaw_sampleMean_residual
    (h : TwoNormalSamples13 X ℙ μ variance) (g : Fin 2) :
    ProbabilityTheory.HasGaussianLaw
      (fun ω =>
        (sampleMean13 (X g) ω, fun i => sampleResidual13 (X g) ω i)) ℙ := by
  have hmap :=
    (h.hasGaussianLaw_sample g).map_fun sampleMeanResidualLinear13
  apply hmap.congr
  filter_upwards [] with ω
  ext <;> simp [sampleMean13, sampleResidual13]

/-- Covariance of a sample mean with any raw coordinate in that sample. -/
theorem covariance_sampleMean_coord
    (h : TwoNormalSamples13 X ℙ μ variance) (g : Fin 2) (i : Fin 13) :
    ProbabilityTheory.covariance (sampleMean13 (X g)) (X g i) ℙ
      = (variance g : ℝ) / 13 := by
  letI : IsProbabilityMeasure ℙ := h.indep.isProbabilityMeasure
  unfold sampleMean13
  rw [ProbabilityTheory.covariance_fun_div_left]
  rw [ProbabilityTheory.covariance_fun_sum_left
    (fun j => h.memLp_two_coord g j) (h.memLp_two_coord g i)]
  simp_rw [h.covariance_coord]
  simp

/-- Covariance of either sample mean with any raw coordinate. -/
theorem covariance_sampleMean_coord_general
    (h : TwoNormalSamples13 X ℙ μ variance)
    (g k : Fin 2) (i : Fin 13) :
    ProbabilityTheory.covariance (sampleMean13 (X g)) (X k i) ℙ
      = if g = k then (variance g : ℝ) / 13 else 0 := by
  letI : IsProbabilityMeasure ℙ := h.indep.isProbabilityMeasure
  unfold sampleMean13
  rw [ProbabilityTheory.covariance_fun_div_left]
  rw [ProbabilityTheory.covariance_fun_sum_left
    (fun j => h.memLp_two_coord g j) (h.memLp_two_coord k i)]
  simp_rw [h.covariance_coord]
  by_cases hgk : g = k
  · subst k
    simp
  · simp [hgk]

/-- Covariance matrix of the two sample means. -/
theorem covariance_sampleMeans
    (h : TwoNormalSamples13 X ℙ μ variance) (g k : Fin 2) :
    ProbabilityTheory.covariance
      (sampleMean13 (X g)) (sampleMean13 (X k)) ℙ
      = if g = k then (variance g : ℝ) / 13 else 0 := by
  letI : IsProbabilityMeasure ℙ := h.indep.isProbabilityMeasure
  unfold sampleMean13
  rw [ProbabilityTheory.covariance_fun_div_left,
    ProbabilityTheory.covariance_fun_div_right]
  rw [ProbabilityTheory.covariance_fun_sum_fun_sum
    (fun i => h.memLp_two_coord g i)
    (fun j => h.memLp_two_coord k j)]
  simp_rw [h.covariance_coord]
  by_cases hgk : g = k
  · subst k
    simp
  · simp [hgk]

/-- Every residual coordinate is uncorrelated with its sample mean. -/
theorem covariance_sampleMean_residual
    (h : TwoNormalSamples13 X ℙ μ variance) (g : Fin 2) (i : Fin 13) :
    ProbabilityTheory.covariance
      (sampleMean13 (X g)) (fun ω => sampleResidual13 (X g) ω i) ℙ = 0 := by
  letI : IsProbabilityMeasure ℙ := h.indep.isProbabilityMeasure
  have hmean : MemLp (sampleMean13 (X g)) 2 ℙ :=
    (h.hasGaussianLaw_sampleMean g).memLp_two
  unfold sampleResidual13
  rw [ProbabilityTheory.covariance_fun_sub_right
    hmean (h.memLp_two_coord g i) hmean]
  rw [h.covariance_sampleMean_coord,
    ProbabilityTheory.covariance_self hmean.aemeasurable,
    h.variance_sampleMean]
  ring

/-- Every residual coordinate is uncorrelated with both sample means. -/
theorem covariance_sampleMean_residual_general
    (h : TwoNormalSamples13 X ℙ μ variance)
    (g k : Fin 2) (i : Fin 13) :
    ProbabilityTheory.covariance
      (sampleMean13 (X g))
      (fun ω => sampleResidual13 (X k) ω i) ℙ = 0 := by
  letI : IsProbabilityMeasure ℙ := h.indep.isProbabilityMeasure
  have hmean_g : MemLp (sampleMean13 (X g)) 2 ℙ :=
    (h.hasGaussianLaw_sampleMean g).memLp_two
  have hmean_k : MemLp (sampleMean13 (X k)) 2 ℙ :=
    (h.hasGaussianLaw_sampleMean k).memLp_two
  unfold sampleResidual13
  rw [ProbabilityTheory.covariance_fun_sub_right
    hmean_g (h.memLp_two_coord k i) hmean_k]
  rw [h.covariance_sampleMean_coord_general,
    h.covariance_sampleMeans]
  by_cases hgk : g = k <;> simp [hgk]

/-- Exact covariance matrix of the residual vector in one sample. -/
theorem covariance_residual
    (h : TwoNormalSamples13 X ℙ μ variance)
    (g : Fin 2) (i j : Fin 13) :
    ProbabilityTheory.covariance
      (fun ω => sampleResidual13 (X g) ω i)
      (fun ω => sampleResidual13 (X g) ω j) ℙ
      =
    (if i = j then (variance g : ℝ) else 0)
      - (variance g : ℝ) / 13 := by
  letI : IsProbabilityMeasure ℙ := h.indep.isProbabilityMeasure
  have hmean : MemLp (sampleMean13 (X g)) 2 ℙ :=
    (h.hasGaussianLaw_sampleMean g).memLp_two
  unfold sampleResidual13
  rw [ProbabilityTheory.covariance_fun_sub_fun_sub
    (h.memLp_two_coord g i) hmean
    (h.memLp_two_coord g j) hmean]
  rw [h.covariance_coord,
    h.covariance_sampleMean_coord,
    ProbabilityTheory.covariance_comm
      (X g i) (sampleMean13 (X g)),
    h.covariance_sampleMean_coord,
    ProbabilityTheory.covariance_self hmean.aemeasurable,
    h.variance_sampleMean]
  simp only [Prod.mk.injEq, true_and]
  ring

/--
The sample mean is independent of the full residual vector.  This is the
Gaussian linear-algebra part of the classical mean/sample-variance
independence theorem; no chi-square density calculation is used.
-/
theorem indepFun_sampleMean_residual
    (h : TwoNormalSamples13 X ℙ μ variance) (g : Fin 2) :
    ProbabilityTheory.IndepFun
      (sampleMean13 (X g))
      (fun ω i => sampleResidual13 (X g) ω i) ℙ := by
  letI : IsProbabilityMeasure ℙ := h.indep.isProbabilityMeasure
  let lift :
      (ℝ × (Fin 13 → ℝ)) →L[ℝ] ((Unit → ℝ) × (Fin 13 → ℝ)) :=
    (ContinuousLinearMap.pi fun _ : Unit =>
      ContinuousLinearMap.fst ℝ ℝ (Fin 13 → ℝ)).prod
      (ContinuousLinearMap.snd ℝ ℝ (Fin 13 → ℝ))
  have hjointPi :
      ProbabilityTheory.HasGaussianLaw
        (fun ω =>
          (fun _ : Unit => sampleMean13 (X g) ω,
            fun i => sampleResidual13 (X g) ω i)) ℙ := by
    have hmap :=
      (h.hasGaussianLaw_sampleMean_residual g).map_fun lift
    apply hmap.congr
    filter_upwards [] with ω
    ext <;> simp [lift]
  have hblocks :
      ProbabilityTheory.IndepFun
        (fun ω (_ : Unit) => sampleMean13 (X g) ω)
        (fun ω i => sampleResidual13 (X g) ω i) ℙ :=
    hjointPi.indepFun_of_covariance_eval
      (fun _ i => h.covariance_sampleMean_residual g i)
  exact hblocks.comp (measurable_pi_apply ()) measurable_id

/--
The complete `(mean, residual-vector)` block from sample 1 is independent of
the corresponding block from sample 2.
-/
theorem indepFun_sampleMeanResidual_blocks
    (h : TwoNormalSamples13 X ℙ μ variance) :
    ProbabilityTheory.IndepFun
      (fun ω =>
        (sampleMean13 (X 0) ω, fun i => sampleResidual13 (X 0) ω i))
      (fun ω =>
        (sampleMean13 (X 1) ω, fun i => sampleResidual13 (X 1) ω i)) ℙ := by
  have hblocks :=
    h.indepFun_sample_pair.comp
      (show Measurable sampleMeanResidualLinear13 by fun_prop)
      (show Measurable sampleMeanResidualLinear13 by fun_prop)
  apply hblocks.congr
  · filter_upwards [] with ω
    ext <;> simp [Function.comp_def, sampleMean13, sampleResidual13]
  · filter_upwards [] with ω
    ext <;> simp [Function.comp_def, sampleMean13, sampleResidual13]

/--
The pair of sample means is independent of the pair of complete residual
vectors.  This is the two-sample Gaussian decomposition in the form needed
before applying Cochran's theorem.
-/
theorem indepFun_allSampleMeans_allResiduals
    (h : TwoNormalSamples13 X ℙ μ variance) :
    ProbabilityTheory.IndepFun
      (fun ω g => sampleMean13 (X g) ω)
      (fun ω (gi : Fin 2 × Fin 13) =>
        sampleResidual13 (X gi.1) ω gi.2) ℙ := by
  let selectSample (g : Fin 2) :
      ((Fin 2 × Fin 13) → ℝ) →L[ℝ] (Fin 13 → ℝ) :=
    ContinuousLinearMap.pi fun i =>
      ContinuousLinearMap.proj (g, i)
  let allMeans :
      ((Fin 2 × Fin 13) → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearMap.pi fun g =>
      sampleMeanLinear13.comp (selectSample g)
  let allResiduals :
      ((Fin 2 × Fin 13) → ℝ) →L[ℝ]
        ((Fin 2 × Fin 13) → ℝ) :=
    ContinuousLinearMap.pi fun gi =>
      (ContinuousLinearMap.proj gi.2).comp
        (sampleResidualLinear13.comp (selectSample gi.1))
  let split :
      ((Fin 2 × Fin 13) → ℝ) →L[ℝ]
        ((Fin 2 → ℝ) × ((Fin 2 × Fin 13) → ℝ)) :=
    allMeans.prod allResiduals
  have hjoint :
      ProbabilityTheory.HasGaussianLaw
        (fun ω =>
          (fun g => sampleMean13 (X g) ω,
            fun gi : Fin 2 × Fin 13 =>
              sampleResidual13 (X gi.1) ω gi.2)) ℙ := by
    have hmap := h.hasGaussianLaw_all.map_fun split
    apply hmap.congr
    filter_upwards [] with ω
    ext <;>
      simp [split, allMeans, allResiduals, selectSample,
        sampleMean13, sampleResidual13]
  exact hjoint.indepFun_of_covariance_eval fun g gi =>
    h.covariance_sampleMean_residual_general g gi.1 gi.2

/-- The two sample means are jointly independent of the two residual sums of squares. -/
theorem indepFun_sampleMeans_residualSumSquares
    (h : TwoNormalSamples13 X ℙ μ variance) :
    ProbabilityTheory.IndepFun
      (fun ω g => sampleMean13 (X g) ω)
      (fun ω =>
        (residualSumSquares13 (X 0) ω,
          residualSumSquares13 (X 1) ω)) ℙ := by
  let rssPair : ((Fin 2 × Fin 13) → ℝ) → ℝ × ℝ :=
    fun z =>
      (∑ i, z (0, i) ^ 2,
        ∑ i, z (1, i) ^ 2)
  have hcomp :=
    h.indepFun_allSampleMeans_allResiduals.comp measurable_id
      (show Measurable rssPair by
        dsimp only [rssPair]
        fun_prop)
  apply hcomp.congr .rfl
  filter_upwards [] with ω
  simp only [Function.comp_apply, rssPair, residualSumSquares13,
    sampleResidual13]

/-- The two residual sums of squares are independent. -/
theorem indepFun_residualSumSquares
    (h : TwoNormalSamples13 X ℙ μ variance) :
    ProbabilityTheory.IndepFun
      (residualSumSquares13 (X 0))
      (residualSumSquares13 (X 1)) ℙ := by
  have hcomp :=
    h.indepFun_sample_pair.comp
      (show Measurable (fun x : Fin 13 → ℝ =>
          ∑ i, (x i - (∑ j, x j) / 13) ^ 2) by fun_prop)
      (show Measurable (fun x : Fin 13 → ℝ =>
          ∑ i, (x i - (∑ j, x j) / 13) ^ 2) by fun_prop)
  apply hcomp.congr
  · filter_upwards [] with ω
    simp [Function.comp_apply, residualSumSquares13,
      sampleResidual13, sampleMean13]
  · filter_upwards [] with ω
    simp [Function.comp_apply, residualSumSquares13,
      sampleResidual13, sampleMean13]

/-- The difference of sample means is independent of both residual sums of squares jointly. -/
theorem indepFun_meanDifference_residualSumSquares
    (h : TwoNormalSamples13 X ℙ μ variance) :
    ProbabilityTheory.IndepFun
      (meanDifference13 X)
      (fun ω =>
        (residualSumSquares13 (X 0) ω,
          residualSumSquares13 (X 1) ω)) ℙ := by
  have hcomp :=
    h.indepFun_sampleMeans_residualSumSquares.comp
      (show Measurable (fun m : Fin 2 → ℝ => m 1 - m 0) by fun_prop)
      measurable_id
  apply hcomp.congr
  · filter_upwards [] with ω
    rfl
  · filter_upwards [] with ω
    rfl

/--
For every fixed weight `θ`, the oracle centered error is independent of both
residual sums of squares jointly.
-/
theorem indepFun_oracleCenteredError_residualSumSquares
    (h : TwoNormalSamples13 X ℙ μ variance) (θ : ℝ) :
    ProbabilityTheory.IndepFun
      (oracleCenteredError13 μ θ X)
      (fun ω =>
        (residualSumSquares13 (X 0) ω,
          residualSumSquares13 (X 1) ω)) ℙ := by
  have hcomp :=
    h.indepFun_sampleMeans_residualSumSquares.comp
      (show Measurable
          (fun m : Fin 2 → ℝ => m 0 + θ * (m 1 - m 0) - μ) by
        fun_prop)
      measurable_id
  apply hcomp.congr
  · filter_upwards [] with ω
    rfl
  · filter_upwards [] with ω
    rfl

end TwoNormalSamples13

end

end GraybillDeal
