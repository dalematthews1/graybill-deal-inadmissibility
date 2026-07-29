import GraybillDeal.NormalSample
import GraybillDeal.NormalSquare
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Cochran's theorem for a normal sample of size thirteen

This file supplies the remaining distributional part of the raw-normal-sample
bridge.  The residual hyperplane in `ℝ¹³` has dimension twelve.  Coordinates
in an orthonormal basis of that hyperplane are independent standard Gaussians
after division by the population standard deviation, and Parseval identifies
their sum of squares with the scaled residual sum of squares.
-/

namespace GraybillDeal

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators RealInnerProductSpace EuclideanSpace

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Euclidean realization of a sample with thirteen coordinates. -/
abbrev SampleEuclidean13 := EuclideanSpace ℝ (Fin 13)

/-- The constant-one direction in the thirteen-dimensional sample space. -/
def sampleOnesEuclidean13 : SampleEuclidean13 :=
  WithLp.toLp 2 (fun _ => 1)

lemma sampleOnesEuclidean13_ne_zero :
    sampleOnesEuclidean13 ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : SampleEuclidean13 => x 0) h
  simp [sampleOnesEuclidean13] at h0

/-- The twelve-dimensional hyperplane of vectors whose coordinates sum to zero. -/
def sampleResidualSubspace13 : Submodule ℝ SampleEuclidean13 :=
  (ℝ ∙ sampleOnesEuclidean13)ᗮ

/-- An arbitrary orthonormal basis of the residual hyperplane. -/
def residualOrthonormalBasis13 :
    OrthonormalBasis (Fin 12) ℝ sampleResidualSubspace13 :=
  OrthonormalBasis.fromOrthogonalSpanSingleton 12
    sampleOnesEuclidean13_ne_zero

/-- The coefficient of observation `i` in residual contrast `k`. -/
def residualContrastCoefficient13 (k : Fin 12) (i : Fin 13) : ℝ :=
  ((residualOrthonormalBasis13 k : sampleResidualSubspace13) :
      SampleEuclidean13) i

/-- The twelve residual contrasts, as a continuous linear map on raw coordinate vectors. -/
def residualContrastLinear13 :
    (Fin 13 → ℝ) →L[ℝ] (Fin 12 → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    ∑ i, residualContrastCoefficient13 k i • ContinuousLinearMap.proj i

@[simp]
lemma residualContrastLinear13_apply
    (x : Fin 13 → ℝ) (k : Fin 12) :
    residualContrastLinear13 x k =
      ∑ i, residualContrastCoefficient13 k i * x i := by
  simp [residualContrastLinear13]

/-- The `k`th orthonormal residual contrast of a raw sample. -/
def residualContrast13
    (X : Fin 13 → Ω → ℝ) (k : Fin 12) (ω : Ω) : ℝ :=
  residualContrastLinear13 (fun i => X i ω) k

@[simp]
lemma residualContrast13_eq_sum
    (X : Fin 13 → Ω → ℝ) (k : Fin 12) (ω : Ω) :
    residualContrast13 X k ω =
      ∑ i, residualContrastCoefficient13 k i * X i ω := by
  simp [residualContrast13]

/-- Residual contrasts divided by the population standard deviation. -/
def standardizedResidualContrast13
    (variance : ℝ) (X : Fin 13 → Ω → ℝ)
    (k : Fin 12) (ω : Ω) : ℝ :=
  residualContrast13 X k ω / √variance

lemma sum_residualContrastCoefficient13 (k : Fin 12) :
    ∑ i, residualContrastCoefficient13 k i = 0 := by
  let v : SampleEuclidean13 :=
    ((residualOrthonormalBasis13 k : sampleResidualSubspace13) :
      SampleEuclidean13)
  have hmem :
      v ∈ sampleResidualSubspace13 :=
    (residualOrthonormalBasis13 k).property
  have horth :
      inner ℝ v sampleOnesEuclidean13 = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp hmem
  rw [PiLp.inner_apply] at horth
  simpa [residualContrastCoefficient13, sampleOnesEuclidean13,
    mul_comm, v] using horth

lemma sum_mul_residualContrastCoefficient13
    (k l : Fin 12) :
    ∑ i, residualContrastCoefficient13 k i *
        residualContrastCoefficient13 l i =
      if k = l then 1 else 0 := by
  have hinner := residualOrthonormalBasis13.inner_eq_ite k l
  simpa [residualContrastCoefficient13, PiLp.inner_apply, mul_comm] using hinner

/-- A residual vector, regarded as a vector in Euclidean thirteen-space. -/
def sampleResidualEuclidean13
    (X : Fin 13 → Ω → ℝ) (ω : Ω) : SampleEuclidean13 :=
  WithLp.toLp 2 (fun i => sampleResidual13 X ω i)

lemma sampleResidualEuclidean13_mem
    (X : Fin 13 → Ω → ℝ) (ω : Ω) :
    sampleResidualEuclidean13 X ω ∈ sampleResidualSubspace13 := by
  rw [sampleResidualSubspace13,
    Submodule.mem_orthogonal_singleton_iff_inner_left,
    PiLp.inner_apply]
  simpa [sampleResidualEuclidean13, sampleOnesEuclidean13] using
    sum_sampleResidual13 X ω

/-- A residual vector as an element of the residual hyperplane. -/
def sampleResidualSubspaceValue13
    (X : Fin 13 → Ω → ℝ) (ω : Ω) : sampleResidualSubspace13 :=
  ⟨sampleResidualEuclidean13 X ω, sampleResidualEuclidean13_mem X ω⟩

lemma residualContrast13_eq_inner_residualSubspaceValue13
    (X : Fin 13 → Ω → ℝ) (k : Fin 12) (ω : Ω) :
    residualContrast13 X k ω =
      inner ℝ (residualOrthonormalBasis13 k)
        (sampleResidualSubspaceValue13 X ω) := by
  rw [residualContrast13_eq_sum]
  change
    (∑ i, residualContrastCoefficient13 k i * X i ω) =
      inner ℝ
        (((residualOrthonormalBasis13 k : sampleResidualSubspace13) :
          SampleEuclidean13))
        (((sampleResidualSubspaceValue13 X ω : sampleResidualSubspace13) :
          SampleEuclidean13))
  rw [PiLp.inner_apply]
  simp_rw [Real.inner_apply]
  change
    (∑ i, residualContrastCoefficient13 k i * X i ω) =
      ∑ i, residualContrastCoefficient13 k i *
        sampleResidual13 X ω i
  simp_rw [sampleResidual13, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_residualContrastCoefficient13]
  simp

/-- Parseval's identity identifies the contrast norm with the residual sum of squares. -/
lemma sum_sq_residualContrast13_eq_residualSumSquares13
    (X : Fin 13 → Ω → ℝ) (ω : Ω) :
    ∑ k, residualContrast13 X k ω ^ 2 =
      residualSumSquares13 X ω := by
  simp_rw [residualContrast13_eq_inner_residualSubspaceValue13]
  rw [residualOrthonormalBasis13.sum_sq_inner_right]
  change ‖sampleResidualEuclidean13 X ω‖ ^ 2 =
    residualSumSquares13 X ω
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

lemma sum_sq_standardizedResidualContrast13_eq_scaledResidualSumSquares13
    (variance : ℝ) (hv : 0 ≤ variance)
    (X : Fin 13 → Ω → ℝ) (ω : Ω) :
    ∑ k, standardizedResidualContrast13 variance X k ω ^ 2 =
      scaledResidualSumSquares13 variance X ω := by
  simp_rw [standardizedResidualContrast13, div_pow]
  rw [← Finset.sum_div,
    sum_sq_residualContrast13_eq_residualSumSquares13,
    Real.sq_sqrt hv]
  rfl

namespace TwoNormalSamples13

variable {X : Fin 2 → Fin 13 → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}

/-- The vector of twelve residual contrasts is jointly Gaussian. -/
theorem hasGaussianLaw_residualContrasts
    (h : TwoNormalSamples13 X P μ variance) (g : Fin 2) :
    HasGaussianLaw
      (fun ω k => residualContrast13 (X g) k ω) P := by
  have hmap :=
    (h.hasGaussianLaw_sample g).map_fun residualContrastLinear13
  apply hmap.congr
  filter_upwards [] with ω
  rfl

/-- Every residual contrast has expectation zero. -/
theorem integral_residualContrast
    (h : TwoNormalSamples13 X P μ variance)
    (g : Fin 2) (k : Fin 12) :
    ∫ ω, residualContrast13 (X g) k ω ∂P = 0 := by
  rw [show residualContrast13 (X g) k =
      fun ω => ∑ i, residualContrastCoefficient13 k i * X g i ω by
    ext ω
    simp]
  rw [integral_finsetSum Finset.univ]
  · simp_rw [integral_const_mul, h.integral_coord]
    rw [← Finset.sum_mul, sum_residualContrastCoefficient13]
    simp
  · intro i _
    exact (h.hasGaussianLaw_coord g i).integrable.const_mul _

/-- Covariance matrix of the unstandardized residual contrasts. -/
theorem covariance_residualContrast
    (h : TwoNormalSamples13 X P μ variance)
    (g : Fin 2) (k l : Fin 12) :
    covariance
      (residualContrast13 (X g) k)
      (residualContrast13 (X g) l) P =
      (variance g : ℝ) * (if k = l then 1 else 0) := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  rw [show residualContrast13 (X g) k =
      fun ω => ∑ i, residualContrastCoefficient13 k i * X g i ω by
    ext ω
    simp]
  rw [show residualContrast13 (X g) l =
      fun ω => ∑ i, residualContrastCoefficient13 l i * X g i ω by
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
    (∑ i, residualContrastCoefficient13 k i *
      (residualContrastCoefficient13 l i * (variance g : ℝ))) =
        (variance g : ℝ) *
          ∑ i, residualContrastCoefficient13 k i *
            residualContrastCoefficient13 l i by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
  rw [sum_mul_residualContrastCoefficient13]
  by_cases hkl : k = l <;> simp [hkl]

/-- The vector of standardized residual contrasts is jointly Gaussian. -/
theorem hasGaussianLaw_standardizedResidualContrasts
    (h : TwoNormalSamples13 X P μ variance)
    (g : Fin 2) :
    HasGaussianLaw
      (fun ω k =>
        standardizedResidualContrast13 (variance g) (X g) k ω) P := by
  have hscaled :=
    (h.hasGaussianLaw_residualContrasts g).fun_smul
      (√(variance g : ℝ))⁻¹
  apply hscaled.congr
  filter_upwards [] with ω
  ext k
  simp [standardizedResidualContrast13, div_eq_mul_inv,
    Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Every standardized residual contrast has expectation zero. -/
theorem integral_standardizedResidualContrast
    (h : TwoNormalSamples13 X P μ variance)
    (g : Fin 2) (k : Fin 12) :
    ∫ ω, standardizedResidualContrast13 (variance g) (X g) k ω ∂P = 0 := by
  unfold standardizedResidualContrast13
  rw [integral_div, h.integral_residualContrast]
  simp

/-- Covariance matrix of the standardized residual contrasts. -/
theorem covariance_standardizedResidualContrast
    (h : TwoNormalSamples13 X P μ variance)
    (g : Fin 2) (hv : 0 < (variance g : ℝ)) (k l : Fin 12) :
    covariance
      (standardizedResidualContrast13 (variance g) (X g) k)
      (standardizedResidualContrast13 (variance g) (X g) l) P =
      if k = l then 1 else 0 := by
  unfold standardizedResidualContrast13
  rw [covariance_fun_div_left, covariance_fun_div_right,
    h.covariance_residualContrast]
  by_cases hkl : k = l
  · rw [if_pos hkl]
    simp only [mul_one]
    rw [div_div, ← pow_two, Real.sq_sqrt hv.le,
      div_self (ne_of_gt hv)]
  · simp [hkl]

/-- Each standardized residual contrast is a standard normal random variable. -/
theorem hasLaw_standardizedResidualContrast
    (h : TwoNormalSamples13 X P μ variance)
    (g : Fin 2) (hv : 0 < (variance g : ℝ)) (k : Fin 12) :
    HasLaw (standardizedResidualContrast13 (variance g) (X g) k)
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
        (standardizedResidualContrast13 (variance g) (X g) k) P = 1 := by
    rw [← covariance_self hgauss.aemeasurable,
      h.covariance_standardizedResidualContrast g hv k k]
    simp
  rw [hvar]
  norm_num

/-- The twelve standardized residual contrasts are mutually independent. -/
theorem iIndepFun_standardizedResidualContrasts
    (h : TwoNormalSamples13 X P μ variance)
    (g : Fin 2) (hv : 0 < (variance g : ℝ)) :
    iIndepFun
      (fun k ω =>
        standardizedResidualContrast13 (variance g) (X g) k ω) P := by
  apply
    (h.hasGaussianLaw_standardizedResidualContrasts g)
      |>.iIndepFun_of_covariance_eq_zero
  intro k l hkl
  rw [h.covariance_standardizedResidualContrast g hv k l, if_neg hkl]

/--
Cochran's theorem for either sample: the residual sum of squares divided by
the population variance has the `χ²₁₂ = Gamma(6, 1 / 2)` law.
-/
theorem hasLaw_scaledResidualSumSquares13
    (h : TwoNormalSamples13 X P μ variance)
    (g : Fin 2) (hv : 0 < (variance g : ℝ)) :
    HasLaw (scaledResidualSumSquares13 (variance g) (X g))
      (gammaMeasure 6 (1 / 2)) P := by
  have hsum :
      HasLaw
        (fun ω =>
          ∑ k,
            standardizedResidualContrast13
              (variance g) (X g) k ω ^ 2)
        (gammaMeasure 6 (1 / 2)) P :=
    hasLaw_sum_sq_standardGaussian_fin12
      (fun k => h.hasLaw_standardizedResidualContrast g hv k)
      (h.iIndepFun_standardizedResidualContrasts g hv)
  apply hsum.congr
  filter_upwards [] with ω
  exact
    (sum_sq_standardizedResidualContrast13_eq_scaledResidualSumSquares13
      (variance g) hv.le (X g) ω).symm

end TwoNormalSamples13

end

end GraybillDeal
