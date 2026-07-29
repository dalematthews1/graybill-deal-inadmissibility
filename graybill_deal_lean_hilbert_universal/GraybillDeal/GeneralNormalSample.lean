import GraybillDeal.NormalSquare
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Two normal samples with arbitrary residual degrees of freedom

This file is the sample-size-generic version of the probability scaffold used
in `NormalSample.lean` and `Cochran13.lean`.  The parameter `ν` is the residual
degrees of freedom, so each raw sample has `ν + 1` observations.  In
particular, the old size-thirteen case is `ν = 12`.

The main result is `TwoNormalSamplesN.hasLaw_scaledResidualSumSquares`: for
`ν > 0`, the residual sum of squares divided by the population variance has
law `Gamma(ν / 2, 1 / 2)`.
-/

namespace GraybillDeal

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators RealInnerProductSpace EuclideanSpace

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The arithmetic mean of a sample with `ν + 1` observations. -/
def sampleMeanN (ν : ℕ) (X : Fin (ν + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ i, X i ω) / (ν + 1)

/-- The vector of deviations from the sample mean. -/
def sampleResidualN
    (ν : ℕ) (X : Fin (ν + 1) → Ω → ℝ) (ω : Ω) (i : Fin (ν + 1)) : ℝ :=
  X i ω - sampleMeanN ν X ω

/-- The unnormalised residual sum of squares. -/
def residualSumSquaresN
    (ν : ℕ) (X : Fin (ν + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i, sampleResidualN ν X ω i ^ 2

/-- The usual unbiased sample variance, with divisor `ν`. -/
def sampleVarianceN
    (ν : ℕ) (X : Fin (ν + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  residualSumSquaresN ν X ω / ν

/-- Difference of the second and first sample means. -/
def meanDifferenceN
    (ν : ℕ) (X : Fin 2 → Fin (ν + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleMeanN ν (X 1) ω - sampleMeanN ν (X 0) ω

/-- The known-variance weight `σ₀² / (σ₀² + σ₁²)`. -/
def oracleVarianceWeightN (variance : Fin 2 → NNReal) : ℝ :=
  (variance 0 : ℝ) / ((variance 0 : ℝ) + variance 1)

/-- The residual sum of squares divided by the population variance. -/
def scaledResidualSumSquaresN
    (ν : ℕ) (variance : ℝ) (X : Fin (ν + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  residualSumSquaresN ν X ω / variance

/-- Two independent normal samples, each containing `ν + 1` observations. -/
structure TwoNormalSamplesN
    (ν : ℕ) (X : Fin 2 → Fin (ν + 1) → Ω → ℝ)
    (P : Measure Ω) (μ : ℝ) (variance : Fin 2 → NNReal) : Prop where
  law :
    ∀ g i,
      HasLaw (X g i) (gaussianReal μ (variance g)) P
  indep :
    iIndepFun (fun gi : Fin 2 × Fin (ν + 1) => X gi.1 gi.2) P

@[measurability, fun_prop]
theorem measurable_sampleMeanN
    {ν : ℕ} {X : Fin (ν + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) :
    Measurable (sampleMeanN ν X) := by
  unfold sampleMeanN
  fun_prop

@[measurability, fun_prop]
theorem measurable_sampleResidualN
    {ν : ℕ} {X : Fin (ν + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) :
    Measurable (fun ω => sampleResidualN ν X ω) := by
  unfold sampleResidualN
  fun_prop

@[measurability, fun_prop]
theorem measurable_residualSumSquaresN
    {ν : ℕ} {X : Fin (ν + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) :
    Measurable (residualSumSquaresN ν X) := by
  unfold residualSumSquaresN
  fun_prop

@[measurability, fun_prop]
theorem measurable_sampleVarianceN
    {ν : ℕ} {X : Fin (ν + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) :
    Measurable (sampleVarianceN ν X) := by
  unfold sampleVarianceN
  fun_prop

@[measurability, fun_prop]
theorem measurable_meanDifferenceN
    {ν : ℕ} {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
    (hX : ∀ g i, Measurable (X g i)) :
    Measurable (meanDifferenceN ν X) := by
  unfold meanDifferenceN
  fun_prop

@[measurability, fun_prop]
theorem measurable_scaledResidualSumSquaresN
    {ν : ℕ} {X : Fin (ν + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (variance : ℝ) :
    Measurable (scaledResidualSumSquaresN ν variance X) := by
  unfold scaledResidualSumSquaresN
  fun_prop

theorem sum_sampleResidualN
    (ν : ℕ) (X : Fin (ν + 1) → Ω → ℝ) (ω : Ω) :
    ∑ i, sampleResidualN ν X ω i = 0 := by
  unfold sampleResidualN sampleMeanN
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hν : (((ν + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  norm_num [Nat.cast_add, Nat.cast_one] at hν ⊢
  field_simp
  ring

theorem residualSumSquaresN_eq
    (ν : ℕ) (X : Fin (ν + 1) → Ω → ℝ) (ω : Ω) :
    residualSumSquaresN ν X ω =
      (∑ i, X i ω ^ 2) - (ν + 1) * sampleMeanN ν X ω ^ 2 := by
  unfold residualSumSquaresN sampleResidualN sampleMeanN
  simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hν : (((ν + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  norm_num [Nat.cast_add, Nat.cast_one] at hν ⊢
  field_simp
  ring

theorem residualSumSquaresN_nonneg
    (ν : ℕ) (X : Fin (ν + 1) → Ω → ℝ) (ω : Ω) :
    0 ≤ residualSumSquaresN ν X ω := by
  unfold residualSumSquaresN
  positivity

theorem sampleVarianceN_nonneg
    {ν : ℕ} (hν : 0 < ν)
    (X : Fin (ν + 1) → Ω → ℝ) (ω : Ω) :
    0 ≤ sampleVarianceN ν X ω := by
  unfold sampleVarianceN
  exact div_nonneg (residualSumSquaresN_nonneg ν X ω) (by positivity)

theorem residualDF_mul_sampleVarianceN
    {ν : ℕ} (hν : 0 < ν)
    (X : Fin (ν + 1) → Ω → ℝ) (ω : Ω) :
    (ν : ℝ) * sampleVarianceN ν X ω = residualSumSquaresN ν X ω := by
  unfold sampleVarianceN
  field_simp

/-- The continuous linear functional taking the arithmetic mean. -/
def sampleMeanLinearN (ν : ℕ) :
    (Fin (ν + 1) → ℝ) →L[ℝ] ℝ :=
  (((ν + 1 : ℕ) : ℝ)⁻¹) • ∑ i, ContinuousLinearMap.proj i

/-- The continuous linear map subtracting the coordinate mean. -/
def sampleResidualLinearN (ν : ℕ) :
    (Fin (ν + 1) → ℝ) →L[ℝ] (Fin (ν + 1) → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj i - sampleMeanLinearN ν

/-- Joint linear map from a sample to its mean and residual vector. -/
def sampleMeanResidualLinearN (ν : ℕ) :
    (Fin (ν + 1) → ℝ) →L[ℝ]
      (ℝ × (Fin (ν + 1) → ℝ)) :=
  (sampleMeanLinearN ν).prod (sampleResidualLinearN ν)

/-- Split the raw vector into its two samples. -/
def splitTwoSamplesLinearN (ν : ℕ) :
    ((Fin 2 × Fin (ν + 1)) → ℝ) →L[ℝ]
      ((Fin (ν + 1) → ℝ) × (Fin (ν + 1) → ℝ)) :=
  (ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (0, i)).prod
  (ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (1, i))

@[simp]
theorem sampleMeanLinearN_apply (ν : ℕ) (x : Fin (ν + 1) → ℝ) :
    sampleMeanLinearN ν x = (∑ i, x i) / (ν + 1) := by
  simp only [sampleMeanLinearN, ContinuousLinearMap.smul_apply,
    Finset.sum_apply, ContinuousLinearMap.coe_sum',
    ContinuousLinearMap.proj_apply, smul_eq_mul, div_eq_mul_inv]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

@[simp]
theorem sampleResidualLinearN_apply
    (ν : ℕ) (x : Fin (ν + 1) → ℝ) (i : Fin (ν + 1)) :
    sampleResidualLinearN ν x i = x i - (∑ j, x j) / (ν + 1) := by
  simp [sampleResidualLinearN]

@[simp]
theorem sampleMeanResidualLinearN_apply
    (ν : ℕ) (x : Fin (ν + 1) → ℝ) :
    sampleMeanResidualLinearN ν x =
      ((∑ i, x i) / (ν + 1),
        fun i => x i - (∑ j, x j) / (ν + 1)) := by
  ext <;> simp [sampleMeanResidualLinearN]

@[simp]
theorem splitTwoSamplesLinearN_apply
    (ν : ℕ) (x : (Fin 2 × Fin (ν + 1)) → ℝ) :
    splitTwoSamplesLinearN ν x =
      (fun i => x (0, i), fun i => x (1, i)) := by
  ext <;> simp [splitTwoSamplesLinearN]

namespace TwoNormalSamplesN

variable {ν : ℕ}
  {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}

theorem hasGaussianLaw_coord
    (h : TwoNormalSamplesN ν X P μ variance)
    (g : Fin 2) (i : Fin (ν + 1)) :
    HasGaussianLaw (X g i) P :=
  (h.law g i).hasGaussianLaw

theorem memLp_two_coord
    (h : TwoNormalSamplesN ν X P μ variance)
    (g : Fin 2) (i : Fin (ν + 1)) :
    MemLp (X g i) 2 P :=
  (h.hasGaussianLaw_coord g i).memLp_two

theorem integral_coord
    (h : TwoNormalSamplesN ν X P μ variance)
    (g : Fin 2) (i : Fin (ν + 1)) :
    ∫ ω, X g i ω ∂P = μ := by
  rw [(h.law g i).integral_eq, integral_id_gaussianReal]

theorem variance_coord
    (h : TwoNormalSamplesN ν X P μ variance)
    (g : Fin 2) (i : Fin (ν + 1)) :
    ProbabilityTheory.variance (X g i) P = variance g := by
  rw [(h.law g i).variance_eq, variance_id_gaussianReal]

theorem covariance_coord
    (h : TwoNormalSamplesN ν X P μ variance)
    (g k : Fin 2) (i j : Fin (ν + 1)) :
    covariance (X g i) (X k j) P =
      if (g, i) = (k, j) then (variance g : ℝ) else 0 := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  by_cases heq : (g, i) = (k, j)
  · have hg : g = k := congrArg Prod.fst heq
    have hi : i = j := congrArg Prod.snd heq
    subst k
    subst j
    rw [if_pos rfl, covariance_self (h.law g i).aemeasurable,
      h.variance_coord]
  · rw [if_neg heq]
    exact (h.indep.indepFun heq).covariance_eq_zero
      (h.memLp_two_coord g i) (h.memLp_two_coord k j)

theorem hasGaussianLaw_all
    (h : TwoNormalSamplesN ν X P μ variance) :
    HasGaussianLaw
      (fun ω (gi : Fin 2 × Fin (ν + 1)) => X gi.1 gi.2 ω) P :=
  h.indep.hasGaussianLaw fun gi => h.hasGaussianLaw_coord gi.1 gi.2

theorem hasGaussianLaw_sample
    (h : TwoNormalSamplesN ν X P μ variance) (g : Fin 2) :
    HasGaussianLaw (fun ω i => X g i ω) P := by
  have hinj : Function.Injective
      (fun i : Fin (ν + 1) => (g, i)) := by
    intro i j hij
    exact congrArg Prod.snd hij
  exact (h.indep.precomp hinj).hasGaussianLaw
    (fun i => h.hasGaussianLaw_coord g i)

theorem hasGaussianLaw_sampleMean
    (h : TwoNormalSamplesN ν X P μ variance) (g : Fin 2) :
    HasGaussianLaw (sampleMeanN ν (X g)) P := by
  have hsum :
      HasGaussianLaw (fun ω => ∑ i, X g i ω) P :=
    (h.hasGaussianLaw_sample g).fun_sum
  have hscaled :=
    hsum.fun_smul ((((ν + 1 : ℕ) : ℝ))⁻¹)
  apply hscaled.congr
  filter_upwards [] with ω
  simp only [Pi.smul_apply, smul_eq_mul, sampleMeanN, div_eq_mul_inv]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

theorem integral_sampleMean
    (h : TwoNormalSamplesN ν X P μ variance) (g : Fin 2) :
    ∫ ω, sampleMeanN ν (X g) ω ∂P = μ := by
  unfold sampleMeanN
  rw [integral_div]
  rw [integral_finsetSum Finset.univ
    (fun i _ => (h.hasGaussianLaw_coord g i).integrable)]
  simp_rw [h.integral_coord]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hν : (((ν + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  norm_num [Nat.cast_add, Nat.cast_one] at hν ⊢
  field_simp

theorem variance_sampleMean
    (h : TwoNormalSamplesN ν X P μ variance) (g : Fin 2) :
    ProbabilityTheory.variance (sampleMeanN ν (X g)) P =
      (variance g : ℝ) / (ν + 1) := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  unfold sampleMeanN
  simp only [div_eq_mul_inv]
  rw [variance_mul_const]
  rw [variance_fun_sum (fun i => h.memLp_two_coord g i)]
  simp_rw [h.covariance_coord]
  simp only [Prod.mk.injEq, true_and, Finset.sum_ite_irrel,
    Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hν : (((ν + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  norm_num [Nat.cast_add, Nat.cast_one] at hν ⊢
  field_simp

theorem hasLaw_sampleMean
    (h : TwoNormalSamplesN ν X P μ variance) (g : Fin 2) :
    HasLaw (sampleMeanN ν (X g))
      (gaussianReal μ (variance g / (ν + 1))) P := by
  refine
    { aemeasurable := (h.hasGaussianLaw_sampleMean g).aemeasurable
      map_eq := ?_ }
  rw [(h.hasGaussianLaw_sampleMean g).map_eq_gaussianReal,
    h.integral_sampleMean, h.variance_sampleMean]
  congr 1
  ext
  calc
    ↑(((↑(variance g) / (ν + 1) : ℝ)).toNNReal) =
        (↑(variance g) / (ν + 1) : ℝ) :=
      Real.coe_toNNReal _ (by positivity)
    _ = ↑(variance g / (ν + 1)) := by simp

theorem hasGaussianLaw_sample_pair
    (h : TwoNormalSamplesN ν X P μ variance) :
    HasGaussianLaw
      (fun ω => (fun i => X 0 i ω, fun i => X 1 i ω)) P := by
  have hmap := h.hasGaussianLaw_all.map_fun (splitTwoSamplesLinearN ν)
  apply hmap.congr
  filter_upwards [] with ω
  simp

theorem indepFun_sample_pair
    (h : TwoNormalSamplesN ν X P μ variance) :
    IndepFun (fun ω i => X 0 i ω) (fun ω i => X 1 i ω) P := by
  apply h.hasGaussianLaw_sample_pair.indepFun_of_covariance_eval
  intro i j
  rw [h.covariance_coord, if_neg]
  intro heq
  have := congrArg Prod.fst heq
  norm_num at this

theorem indepFun_sampleMeans01
    (h : TwoNormalSamplesN ν X P μ variance) :
    IndepFun (sampleMeanN ν (X 0)) (sampleMeanN ν (X 1)) P := by
  have hmeans :=
    h.indepFun_sample_pair.comp
      (show Measurable (sampleMeanLinearN ν) by fun_prop)
      (show Measurable (sampleMeanLinearN ν) by fun_prop)
  apply hmeans.congr
  · filter_upwards [] with ω
    simp [Function.comp_apply, sampleMeanN]
  · filter_upwards [] with ω
    simp [Function.comp_apply, sampleMeanN]

theorem hasGaussianLaw_meanDifference
    (h : TwoNormalSamplesN ν X P μ variance) :
    HasGaussianLaw (meanDifferenceN ν X) P := by
  have hpair :
      HasGaussianLaw
        (fun ω =>
          (sampleMeanN ν (X 1) ω, sampleMeanN ν (X 0) ω)) P :=
    h.indepFun_sampleMeans01.symm.hasGaussianLaw
      (h.hasGaussianLaw_sampleMean 1)
      (h.hasGaussianLaw_sampleMean 0)
  apply hpair.fun_sub.congr
  filter_upwards [] with ω
  rfl

theorem integral_meanDifference
    (h : TwoNormalSamplesN ν X P μ variance) :
    ∫ ω, meanDifferenceN ν X ω ∂P = 0 := by
  unfold meanDifferenceN
  rw [integral_sub
    (h.hasGaussianLaw_sampleMean 1).integrable
    (h.hasGaussianLaw_sampleMean 0).integrable,
    h.integral_sampleMean, h.integral_sampleMean]
  ring

theorem variance_meanDifference
    (h : TwoNormalSamplesN ν X P μ variance) :
    ProbabilityTheory.variance (meanDifferenceN ν X) P =
      ((variance 0 : ℝ) + variance 1) / (ν + 1) := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hmean1 : MemLp (sampleMeanN ν (X 1)) 2 P :=
    (h.hasGaussianLaw_sampleMean 1).memLp_two
  have hmean0 : MemLp (sampleMeanN ν (X 0)) 2 P :=
    (h.hasGaussianLaw_sampleMean 0).memLp_two
  have hcov :
      covariance (sampleMeanN ν (X 1)) (sampleMeanN ν (X 0)) P = 0 :=
    h.indepFun_sampleMeans01.symm.covariance_eq_zero hmean1 hmean0
  unfold meanDifferenceN
  rw [variance_fun_sub hmean1 hmean0,
    h.variance_sampleMean, h.variance_sampleMean, hcov]
  ring

theorem hasLaw_meanDifference
    (h : TwoNormalSamplesN ν X P μ variance) :
    HasLaw (meanDifferenceN ν X)
      (gaussianReal 0 ((variance 0 + variance 1) / (ν + 1))) P := by
  refine
    { aemeasurable := h.hasGaussianLaw_meanDifference.aemeasurable
      map_eq := ?_ }
  rw [h.hasGaussianLaw_meanDifference.map_eq_gaussianReal,
    h.integral_meanDifference, h.variance_meanDifference]
  congr 1
  ext
  calc
    ↑(((((variance 0 : ℝ) + variance 1) / (ν + 1))).toNNReal) =
        ((variance 0 : ℝ) + variance 1) / (ν + 1) :=
      Real.coe_toNNReal _ (by positivity)
    _ = ↑((variance 0 + variance 1) / (ν + 1)) := by simp

/-- A sample mean together with its complete residual vector is jointly Gaussian. -/
theorem hasGaussianLaw_sampleMean_residual
    (h : TwoNormalSamplesN ν X P μ variance) (g : Fin 2) :
    HasGaussianLaw
      (fun ω =>
        (sampleMeanN ν (X g) ω,
          fun i => sampleResidualN ν (X g) ω i)) P := by
  have hmap :=
    (h.hasGaussianLaw_sample g).map_fun (sampleMeanResidualLinearN ν)
  apply hmap.congr
  filter_upwards [] with ω
  ext <;> simp [sampleMeanN, sampleResidualN]

/-- Covariance of either sample mean with any raw observation. -/
theorem covariance_sampleMean_coord_general
    (h : TwoNormalSamplesN ν X P μ variance)
    (g k : Fin 2) (i : Fin (ν + 1)) :
    covariance (sampleMeanN ν (X g)) (X k i) P =
      if g = k then (variance g : ℝ) / (ν + 1) else 0 := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  unfold sampleMeanN
  rw [covariance_fun_div_left]
  rw [covariance_fun_sum_left
    (fun j => h.memLp_two_coord g j) (h.memLp_two_coord k i)]
  simp_rw [h.covariance_coord]
  by_cases hgk : g = k
  · subst k
    simp
  · simp [hgk]

/-- Covariance matrix of the two sample means. -/
theorem covariance_sampleMeans
    (h : TwoNormalSamplesN ν X P μ variance) (g k : Fin 2) :
    covariance (sampleMeanN ν (X g)) (sampleMeanN ν (X k)) P =
      if g = k then (variance g : ℝ) / (ν + 1) else 0 := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  unfold sampleMeanN
  rw [covariance_fun_div_left, covariance_fun_div_right]
  rw [covariance_fun_sum_fun_sum
    (fun i => h.memLp_two_coord g i)
    (fun j => h.memLp_two_coord k j)]
  simp_rw [h.covariance_coord]
  by_cases hgk : g = k
  · subst k
    simp
    have hν : (ν : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  · simp [hgk]

/-- Every residual coordinate is uncorrelated with both sample means. -/
theorem covariance_sampleMean_residual_general
    (h : TwoNormalSamplesN ν X P μ variance)
    (g k : Fin 2) (i : Fin (ν + 1)) :
    covariance (sampleMeanN ν (X g))
      (fun ω => sampleResidualN ν (X k) ω i) P = 0 := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hmean_g : MemLp (sampleMeanN ν (X g)) 2 P :=
    (h.hasGaussianLaw_sampleMean g).memLp_two
  have hmean_k : MemLp (sampleMeanN ν (X k)) 2 P :=
    (h.hasGaussianLaw_sampleMean k).memLp_two
  unfold sampleResidualN
  rw [covariance_fun_sub_right
    hmean_g (h.memLp_two_coord k i) hmean_k]
  rw [h.covariance_sampleMean_coord_general,
    h.covariance_sampleMeans]
  by_cases hgk : g = k <;> simp [hgk]

/--
The vector of both sample means is independent of both complete residual
vectors.
-/
theorem indepFun_allSampleMeans_allResiduals
    (h : TwoNormalSamplesN ν X P μ variance) :
    IndepFun
      (fun ω g => sampleMeanN ν (X g) ω)
      (fun ω (gi : Fin 2 × Fin (ν + 1)) =>
        sampleResidualN ν (X gi.1) ω gi.2) P := by
  let selectSample (g : Fin 2) :
      ((Fin 2 × Fin (ν + 1)) → ℝ) →L[ℝ] (Fin (ν + 1) → ℝ) :=
    ContinuousLinearMap.pi fun i =>
      ContinuousLinearMap.proj (g, i)
  let allMeans :
      ((Fin 2 × Fin (ν + 1)) → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearMap.pi fun g =>
      (sampleMeanLinearN ν).comp (selectSample g)
  let allResiduals :
      ((Fin 2 × Fin (ν + 1)) → ℝ) →L[ℝ]
        ((Fin 2 × Fin (ν + 1)) → ℝ) :=
    ContinuousLinearMap.pi fun gi =>
      (ContinuousLinearMap.proj gi.2).comp
        ((sampleResidualLinearN ν).comp (selectSample gi.1))
  let split :
      ((Fin 2 × Fin (ν + 1)) → ℝ) →L[ℝ]
        ((Fin 2 → ℝ) × ((Fin 2 × Fin (ν + 1)) → ℝ)) :=
    allMeans.prod allResiduals
  have hjoint :
      HasGaussianLaw
        (fun ω =>
          (fun g => sampleMeanN ν (X g) ω,
            fun gi : Fin 2 × Fin (ν + 1) =>
              sampleResidualN ν (X gi.1) ω gi.2)) P := by
    have hmap := h.hasGaussianLaw_all.map_fun split
    apply hmap.congr
    filter_upwards [] with ω
    ext <;>
      simp [split, allMeans, allResiduals, selectSample,
        sampleMeanN, sampleResidualN]
  exact hjoint.indepFun_of_covariance_eval fun g gi =>
    h.covariance_sampleMean_residual_general g gi.1 gi.2

/-- Both sample means are jointly independent of both residual sums of squares. -/
theorem indepFun_sampleMeans_residualSumSquares
    (h : TwoNormalSamplesN ν X P μ variance) :
    IndepFun
      (fun ω g => sampleMeanN ν (X g) ω)
      (fun ω =>
        (residualSumSquaresN ν (X 0) ω,
          residualSumSquaresN ν (X 1) ω)) P := by
  let rssPair :
      ((Fin 2 × Fin (ν + 1)) → ℝ) → ℝ × ℝ :=
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
  simp only [Function.comp_apply, rssPair, residualSumSquaresN,
    sampleResidualN]

/-- The mean difference is independent of the pair of residual sums of squares. -/
theorem indepFun_meanDifference_residualSumSquares
    (h : TwoNormalSamplesN ν X P μ variance) :
    IndepFun
      (meanDifferenceN ν X)
      (fun ω =>
        (residualSumSquaresN ν (X 0) ω,
          residualSumSquaresN ν (X 1) ω)) P := by
  have hcomp :=
    h.indepFun_sampleMeans_residualSumSquares.comp
      (show Measurable (fun m : Fin 2 → ℝ => m 1 - m 0) by fun_prop)
      measurable_id
  apply hcomp.congr
  · filter_upwards [] with ω
    rfl
  · filter_upwards [] with ω
    rfl

theorem indepFun_residualSumSquares
    (h : TwoNormalSamplesN ν X P μ variance) :
    IndepFun (residualSumSquaresN ν (X 0))
      (residualSumSquaresN ν (X 1)) P := by
  let rss : (Fin (ν + 1) → ℝ) → ℝ :=
    fun x => ∑ i, (x i - (∑ j, x j) / (ν + 1)) ^ 2
  have hcomp :=
    h.indepFun_sample_pair.comp
      (show Measurable rss by
        dsimp only [rss]
        fun_prop)
      (show Measurable rss by
        dsimp only [rss]
        fun_prop)
  apply hcomp.congr
  · filter_upwards [] with ω
    simp [Function.comp_apply, rss, residualSumSquaresN,
      sampleResidualN, sampleMeanN]
  · filter_upwards [] with ω
    simp [Function.comp_apply, rss, residualSumSquaresN,
      sampleResidualN, sampleMeanN]

end TwoNormalSamplesN

/-! ## Generic Cochran decomposition -/

/-- Euclidean realization of a sample with `ν + 1` coordinates. -/
abbrev SampleEuclideanN (ν : ℕ) :=
  EuclideanSpace ℝ (Fin (ν + 1))

/-- The constant-one direction in sample space. -/
def sampleOnesEuclideanN (ν : ℕ) : SampleEuclideanN ν :=
  WithLp.toLp 2 (fun _ => 1)

lemma sampleOnesEuclideanN_ne_zero (ν : ℕ) :
    sampleOnesEuclideanN ν ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : SampleEuclideanN ν => x 0) h
  simp [sampleOnesEuclideanN] at h0

/-- The residual hyperplane of coordinate-sum-zero vectors. -/
def sampleResidualSubspaceN (ν : ℕ) :
    Submodule ℝ (SampleEuclideanN ν) :=
  (ℝ ∙ sampleOnesEuclideanN ν)ᗮ

/-- An arbitrary orthonormal basis of the `ν`-dimensional residual hyperplane. -/
def residualOrthonormalBasisN (ν : ℕ) :
    OrthonormalBasis (Fin ν) ℝ (sampleResidualSubspaceN ν) :=
  OrthonormalBasis.fromOrthogonalSpanSingleton ν
    (sampleOnesEuclideanN_ne_zero ν)

/-- Coefficient of observation `i` in residual contrast `k`. -/
def residualContrastCoefficientN
    (ν : ℕ) (k : Fin ν) (i : Fin (ν + 1)) : ℝ :=
  ((residualOrthonormalBasisN ν k : sampleResidualSubspaceN ν) :
      SampleEuclideanN ν) i

/-- Residual contrasts as a continuous linear map. -/
def residualContrastLinearN (ν : ℕ) :
    (Fin (ν + 1) → ℝ) →L[ℝ] (Fin ν → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    ∑ i, residualContrastCoefficientN ν k i • ContinuousLinearMap.proj i

@[simp]
lemma residualContrastLinearN_apply
    (ν : ℕ) (x : Fin (ν + 1) → ℝ) (k : Fin ν) :
    residualContrastLinearN ν x k =
      ∑ i, residualContrastCoefficientN ν k i * x i := by
  simp [residualContrastLinearN]

/-- The `k`th orthonormal residual contrast. -/
def residualContrastN
    (ν : ℕ) (X : Fin (ν + 1) → Ω → ℝ)
    (k : Fin ν) (ω : Ω) : ℝ :=
  residualContrastLinearN ν (fun i => X i ω) k

@[simp]
lemma residualContrastN_eq_sum
    (ν : ℕ) (X : Fin (ν + 1) → Ω → ℝ)
    (k : Fin ν) (ω : Ω) :
    residualContrastN ν X k ω =
      ∑ i, residualContrastCoefficientN ν k i * X i ω := by
  simp [residualContrastN]

/-- Residual contrasts divided by population standard deviation. -/
def standardizedResidualContrastN
    (ν : ℕ) (variance : ℝ) (X : Fin (ν + 1) → Ω → ℝ)
    (k : Fin ν) (ω : Ω) : ℝ :=
  residualContrastN ν X k ω / √variance

lemma sum_residualContrastCoefficientN (ν : ℕ) (k : Fin ν) :
    ∑ i, residualContrastCoefficientN ν k i = 0 := by
  let v : SampleEuclideanN ν :=
    ((residualOrthonormalBasisN ν k : sampleResidualSubspaceN ν) :
      SampleEuclideanN ν)
  have hmem : v ∈ sampleResidualSubspaceN ν :=
    (residualOrthonormalBasisN ν k).property
  have horth : inner ℝ v (sampleOnesEuclideanN ν) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp hmem
  rw [PiLp.inner_apply] at horth
  simpa [residualContrastCoefficientN, sampleOnesEuclideanN,
    mul_comm, v] using horth

lemma sum_mul_residualContrastCoefficientN
    (ν : ℕ) (k l : Fin ν) :
    ∑ i, residualContrastCoefficientN ν k i *
        residualContrastCoefficientN ν l i =
      if k = l then 1 else 0 := by
  have hinner := (residualOrthonormalBasisN ν).inner_eq_ite k l
  simpa [residualContrastCoefficientN, PiLp.inner_apply, mul_comm] using hinner

/-- A residual vector regarded as a Euclidean vector. -/
def sampleResidualEuclideanN
    (ν : ℕ) (X : Fin (ν + 1) → Ω → ℝ) (ω : Ω) :
    SampleEuclideanN ν :=
  WithLp.toLp 2 (fun i => sampleResidualN ν X ω i)

lemma sampleResidualEuclideanN_mem
    (ν : ℕ) (X : Fin (ν + 1) → Ω → ℝ) (ω : Ω) :
    sampleResidualEuclideanN ν X ω ∈ sampleResidualSubspaceN ν := by
  rw [sampleResidualSubspaceN,
    Submodule.mem_orthogonal_singleton_iff_inner_left,
    PiLp.inner_apply]
  simpa [sampleResidualEuclideanN, sampleOnesEuclideanN] using
    sum_sampleResidualN ν X ω

def sampleResidualSubspaceValueN
    (ν : ℕ) (X : Fin (ν + 1) → Ω → ℝ) (ω : Ω) :
    sampleResidualSubspaceN ν :=
  ⟨sampleResidualEuclideanN ν X ω,
    sampleResidualEuclideanN_mem ν X ω⟩

lemma residualContrastN_eq_inner_residualSubspaceValueN
    (ν : ℕ) (X : Fin (ν + 1) → Ω → ℝ)
    (k : Fin ν) (ω : Ω) :
    residualContrastN ν X k ω =
      inner ℝ (residualOrthonormalBasisN ν k)
        (sampleResidualSubspaceValueN ν X ω) := by
  rw [residualContrastN_eq_sum]
  change
    (∑ i, residualContrastCoefficientN ν k i * X i ω) =
      inner ℝ
        (((residualOrthonormalBasisN ν k : sampleResidualSubspaceN ν) :
          SampleEuclideanN ν))
        (((sampleResidualSubspaceValueN ν X ω : sampleResidualSubspaceN ν) :
          SampleEuclideanN ν))
  rw [PiLp.inner_apply]
  simp_rw [Real.inner_apply]
  change
    (∑ i, residualContrastCoefficientN ν k i * X i ω) =
      ∑ i, residualContrastCoefficientN ν k i *
        sampleResidualN ν X ω i
  simp_rw [sampleResidualN, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_residualContrastCoefficientN]
  simp

lemma sum_sq_residualContrastN_eq_residualSumSquaresN
    (ν : ℕ) (X : Fin (ν + 1) → Ω → ℝ) (ω : Ω) :
    ∑ k, residualContrastN ν X k ω ^ 2 =
      residualSumSquaresN ν X ω := by
  simp_rw [residualContrastN_eq_inner_residualSubspaceValueN]
  rw [(residualOrthonormalBasisN ν).sum_sq_inner_right]
  change ‖sampleResidualEuclideanN ν X ω‖ ^ 2 =
    residualSumSquaresN ν X ω
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

lemma sum_sq_standardizedResidualContrastN_eq_scaledResidualSumSquaresN
    (ν : ℕ) (variance : ℝ) (hv : 0 ≤ variance)
    (X : Fin (ν + 1) → Ω → ℝ) (ω : Ω) :
    ∑ k, standardizedResidualContrastN ν variance X k ω ^ 2 =
      scaledResidualSumSquaresN ν variance X ω := by
  simp_rw [standardizedResidualContrastN, div_pow]
  rw [← Finset.sum_div,
    sum_sq_residualContrastN_eq_residualSumSquaresN,
    Real.sq_sqrt hv]
  rfl

namespace TwoNormalSamplesN

variable {ν : ℕ}
  {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}

theorem hasGaussianLaw_residualContrasts
    (h : TwoNormalSamplesN ν X P μ variance) (g : Fin 2) :
    HasGaussianLaw
      (fun ω k => residualContrastN ν (X g) k ω) P := by
  have hmap :=
    (h.hasGaussianLaw_sample g).map_fun (residualContrastLinearN ν)
  apply hmap.congr
  filter_upwards [] with ω
  rfl

theorem integral_residualContrast
    (h : TwoNormalSamplesN ν X P μ variance)
    (g : Fin 2) (k : Fin ν) :
    ∫ ω, residualContrastN ν (X g) k ω ∂P = 0 := by
  rw [show residualContrastN ν (X g) k =
      fun ω => ∑ i, residualContrastCoefficientN ν k i * X g i ω by
    ext ω
    simp]
  rw [integral_finsetSum Finset.univ]
  · simp_rw [integral_const_mul, h.integral_coord]
    rw [← Finset.sum_mul, sum_residualContrastCoefficientN]
    simp
  · intro i _
    exact (h.hasGaussianLaw_coord g i).integrable.const_mul _

theorem covariance_residualContrast
    (h : TwoNormalSamplesN ν X P μ variance)
    (g : Fin 2) (k l : Fin ν) :
    covariance (residualContrastN ν (X g) k)
      (residualContrastN ν (X g) l) P =
      (variance g : ℝ) * (if k = l then 1 else 0) := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  rw [show residualContrastN ν (X g) k =
      fun ω => ∑ i, residualContrastCoefficientN ν k i * X g i ω by
    ext ω
    simp]
  rw [show residualContrastN ν (X g) l =
      fun ω => ∑ i, residualContrastCoefficientN ν l i * X g i ω by
    ext ω
    simp]
  rw [covariance_fun_sum_fun_sum
    (fun i => (h.memLp_two_coord g i).const_mul _)
    (fun i => (h.memLp_two_coord g i).const_mul _)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right,
    h.covariance_coord]
  simp only [Prod.mk.injEq, true_and]
  simp_rw [mul_ite, mul_zero, Fintype.sum_ite_eq]
  rw [show
    (∑ i, residualContrastCoefficientN ν k i *
      (residualContrastCoefficientN ν l i * (variance g : ℝ))) =
        (variance g : ℝ) *
          ∑ i, residualContrastCoefficientN ν k i *
            residualContrastCoefficientN ν l i by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
  rw [sum_mul_residualContrastCoefficientN]
  by_cases hkl : k = l <;> simp [hkl]

theorem hasGaussianLaw_standardizedResidualContrasts
    (h : TwoNormalSamplesN ν X P μ variance) (g : Fin 2) :
    HasGaussianLaw
      (fun ω k =>
        standardizedResidualContrastN ν (variance g) (X g) k ω) P := by
  have hscaled :=
    (h.hasGaussianLaw_residualContrasts g).fun_smul
      (√(variance g : ℝ))⁻¹
  apply hscaled.congr
  filter_upwards [] with ω
  ext k
  simp [standardizedResidualContrastN, div_eq_mul_inv,
    Pi.smul_apply, smul_eq_mul, mul_comm]

theorem integral_standardizedResidualContrast
    (h : TwoNormalSamplesN ν X P μ variance)
    (g : Fin 2) (k : Fin ν) :
    ∫ ω, standardizedResidualContrastN ν (variance g) (X g) k ω ∂P = 0 := by
  unfold standardizedResidualContrastN
  rw [integral_div, h.integral_residualContrast]
  simp

theorem covariance_standardizedResidualContrast
    (h : TwoNormalSamplesN ν X P μ variance)
    (g : Fin 2) (hv : 0 < (variance g : ℝ)) (k l : Fin ν) :
    covariance
      (standardizedResidualContrastN ν (variance g) (X g) k)
      (standardizedResidualContrastN ν (variance g) (X g) l) P =
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

theorem hasLaw_standardizedResidualContrast
    (h : TwoNormalSamplesN ν X P μ variance)
    (g : Fin 2) (hv : 0 < (variance g : ℝ)) (k : Fin ν) :
    HasLaw (standardizedResidualContrastN ν (variance g) (X g) k)
      (gaussianReal 0 1) P := by
  have hgauss :=
    (h.hasGaussianLaw_standardizedResidualContrasts g).eval k
  refine
    { aemeasurable := hgauss.aemeasurable
      map_eq := ?_ }
  rw [hgauss.map_eq_gaussianReal,
    h.integral_standardizedResidualContrast]
  have hvar :
      ProbabilityTheory.variance
        (standardizedResidualContrastN ν (variance g) (X g) k) P = 1 := by
    rw [← covariance_self hgauss.aemeasurable,
      h.covariance_standardizedResidualContrast g hv k k]
    simp
  rw [hvar]
  norm_num

theorem iIndepFun_standardizedResidualContrasts
    (h : TwoNormalSamplesN ν X P μ variance)
    (g : Fin 2) (hv : 0 < (variance g : ℝ)) :
    iIndepFun
      (fun k ω =>
        standardizedResidualContrastN ν (variance g) (X g) k ω) P := by
  apply
    (h.hasGaussianLaw_standardizedResidualContrasts g)
      |>.iIndepFun_of_covariance_eq_zero
  intro k l hkl
  rw [h.covariance_standardizedResidualContrast g hv k l, if_neg hkl]

/--
Generic Cochran theorem: `RSS / σ²` has the chi-square law
`Gamma(ν / 2, 1 / 2)`.
-/
theorem hasLaw_scaledResidualSumSquares
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 0 < ν) (g : Fin 2) (hv : 0 < (variance g : ℝ)) :
    HasLaw (scaledResidualSumSquaresN ν (variance g) (X g))
      (gammaMeasure ((ν : ℝ) / 2) (1 / 2)) P := by
  letI : Nonempty (Fin ν) := Fin.pos_iff_nonempty.mp hν
  have hsum :
      HasLaw
        (fun ω =>
          ∑ k,
            standardizedResidualContrastN
              ν (variance g) (X g) k ω ^ 2)
        (gammaMeasure ((ν : ℝ) / 2) (1 / 2)) P := by
    simpa using
      hasLaw_sum_sq_standardGaussian
        (fun k => h.hasLaw_standardizedResidualContrast g hv k)
        (h.iIndepFun_standardizedResidualContrasts g hv)
  apply hsum.congr
  filter_upwards [] with ω
  exact
    (sum_sq_standardizedResidualContrastN_eq_scaledResidualSumSquaresN
      ν (variance g) hv.le (X g) ω).symm

end TwoNormalSamplesN

end

end GraybillDeal
