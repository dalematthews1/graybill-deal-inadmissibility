import GraybillDeal.GeneralNormalSample

/-!
# Two raw normal samples of unequal sizes

This file begins the extension of the Graybill--Deal dominance argument to
unequal sample sizes.  The two samples are

* `X : Fin (ν₁ + 1) → Ω → ℝ` of size `n₁ = ν₁ + 1`, and
* `Y : Fin (ν₂ + 1) → Ω → ℝ` of size `n₂ = ν₂ + 1`.

The joint family is indexed by the disjoint union
`Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)`.  `TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂`
says that all `n₁ + n₂` observations are mutually independent, each `X i`
has law `N(μ, v₁)`, and each `Y j` has law `N(μ, v₂)`.

The per-sample statistics (`sampleMeanN`, `sampleVarianceN`,
`residualSumSquaresN`) are reused from `GeneralNormalSample.lean`; they
are already parameterized by the residual degrees of freedom.

The final theorem of this file is the unequal-size oracle independence:
with `τᵢ = vᵢ / nᵢ` and oracle weight `θ = τ₁ / (τ₁ + τ₂)`, the centered
error of `X̄ + θ D` is independent of the mean difference `D = Ȳ - X̄`.
This is the identity that lets the perturbed weight depend on `D²`, i.e.
the door out of the class in which Duanmu--Roy--Schrittesser proved
relative admissibility.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The joint observation family over the disjoint union of index sets. -/
def obsU {ν₁ ν₂ : ℕ}
    (X : Fin (ν₁ + 1) → Ω → ℝ) (Y : Fin (ν₂ + 1) → Ω → ℝ) :
    (Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → Ω → ℝ :=
  Sum.elim X Y

/-- The population variance attached to each joint index. -/
def varU (ν₁ ν₂ : ℕ) (v₁ v₂ : NNReal) :
    (Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → NNReal :=
  Sum.elim (fun _ => v₁) (fun _ => v₂)

/-- Difference of the second and first sample means, unequal sizes. -/
def meanDifferenceU (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ) (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleMeanN ν₂ Y ω - sampleMeanN ν₁ X ω

/-- The known-variance oracle weight `τ₁ / (τ₁ + τ₂)`, `τᵢ = vᵢ / nᵢ`. -/
def oracleVarianceWeightU (ν₁ ν₂ : ℕ) (v₁ v₂ : NNReal) : ℝ :=
  ((v₁ : ℝ) / (ν₁ + 1)) /
    ((v₁ : ℝ) / (ν₁ + 1) + (v₂ : ℝ) / (ν₂ + 1))

/-- The centered error of the estimator `X̄ + θ D`. -/
def oracleCenteredErrorU (ν₁ ν₂ : ℕ) (μ θ : ℝ)
    (X : Fin (ν₁ + 1) → Ω → ℝ) (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleMeanN ν₁ X ω + θ * meanDifferenceU ν₁ ν₂ X Y ω - μ

/-- The complete raw two-sample normal model with unequal sizes. -/
structure TwoNormalSamplesU
    (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ) (Y : Fin (ν₂ + 1) → Ω → ℝ)
    (P : Measure Ω) (μ : ℝ) (v₁ v₂ : NNReal) : Prop where
  lawX : ∀ i, HasLaw (X i) (gaussianReal μ v₁) P
  lawY : ∀ j, HasLaw (Y j) (gaussianReal μ v₂) P
  indep : iIndepFun (obsU X Y) P

@[measurability, fun_prop]
theorem measurable_meanDifferenceU
    {ν₁ ν₂ : ℕ} {X : Fin (ν₁ + 1) → Ω → ℝ} {Y : Fin (ν₂ + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j)) :
    Measurable (meanDifferenceU ν₁ ν₂ X Y) := by
  unfold meanDifferenceU
  have h₁ := measurable_sampleMeanN (ν := ν₂) hY
  have h₂ := measurable_sampleMeanN (ν := ν₁) hX
  fun_prop

@[measurability, fun_prop]
theorem measurable_oracleCenteredErrorU
    {ν₁ ν₂ : ℕ} {X : Fin (ν₁ + 1) → Ω → ℝ} {Y : Fin (ν₂ + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (μ θ : ℝ) :
    Measurable (oracleCenteredErrorU ν₁ ν₂ μ θ X Y) := by
  unfold oracleCenteredErrorU
  have h₁ := measurable_sampleMeanN (ν := ν₁) hX
  have h₂ := measurable_meanDifferenceU hX hY
  fun_prop

/-- Split the joint vector into the two sample vectors. -/
def splitSamplesLinearU (ν₁ ν₂ : ℕ) :
    ((Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) →L[ℝ]
      ((Fin (ν₁ + 1) → ℝ) × (Fin (ν₂ + 1) → ℝ)) :=
  (ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (Sum.inl i)).prod
  (ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (Sum.inr j))

@[simp]
theorem splitSamplesLinearU_apply
    (ν₁ ν₂ : ℕ) (x : (Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) :
    splitSamplesLinearU ν₁ ν₂ x =
      (fun i => x (Sum.inl i), fun j => x (Sum.inr j)) := by
  ext <;> simp [splitSamplesLinearU]

/-- Select the first sample from the joint vector. -/
def selectXLinearU (ν₁ ν₂ : ℕ) :
    ((Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) →L[ℝ] (Fin (ν₁ + 1) → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.inl i)

/-- Select the second sample from the joint vector. -/
def selectYLinearU (ν₁ ν₂ : ℕ) :
    ((Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) →L[ℝ] (Fin (ν₂ + 1) → ℝ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Sum.inr j)

/-- The first sample mean as a functional of the joint vector. -/
def meanXLinearU (ν₁ ν₂ : ℕ) :
    ((Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) →L[ℝ] ℝ :=
  (sampleMeanLinearN ν₁).comp (selectXLinearU ν₁ ν₂)

/-- The second sample mean as a functional of the joint vector. -/
def meanYLinearU (ν₁ ν₂ : ℕ) :
    ((Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) →L[ℝ] ℝ :=
  (sampleMeanLinearN ν₂).comp (selectYLinearU ν₁ ν₂)

/-- The mean difference as a functional of the joint vector. -/
def diffLinearU (ν₁ ν₂ : ℕ) :
    ((Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) →L[ℝ] ℝ :=
  meanYLinearU ν₁ ν₂ - meanXLinearU ν₁ ν₂

/-- Each residual coordinate as a functional of the joint vector. -/
def residLinearU (ν₁ ν₂ : ℕ) (k : Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) :
    ((Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) →L[ℝ] ℝ :=
  Sum.elim
    (fun i =>
      (ContinuousLinearMap.proj i).comp
        ((sampleResidualLinearN ν₁).comp (selectXLinearU ν₁ ν₂)))
    (fun j =>
      (ContinuousLinearMap.proj j).comp
        ((sampleResidualLinearN ν₂).comp (selectYLinearU ν₁ ν₂)))
    k

@[simp]
theorem meanXLinearU_apply (ν₁ ν₂ : ℕ)
    (x : (Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) :
    meanXLinearU ν₁ ν₂ x = (∑ i, x (Sum.inl i)) / (ν₁ + 1) := by
  simp [meanXLinearU, selectXLinearU]

@[simp]
theorem meanYLinearU_apply (ν₁ ν₂ : ℕ)
    (x : (Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) :
    meanYLinearU ν₁ ν₂ x = (∑ j, x (Sum.inr j)) / (ν₂ + 1) := by
  simp [meanYLinearU, selectYLinearU]

@[simp]
theorem diffLinearU_apply (ν₁ ν₂ : ℕ)
    (x : (Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) :
    diffLinearU ν₁ ν₂ x =
      (∑ j, x (Sum.inr j)) / (ν₂ + 1) - (∑ i, x (Sum.inl i)) / (ν₁ + 1) := by
  simp [diffLinearU]

@[simp]
theorem residLinearU_apply_inl (ν₁ ν₂ : ℕ) (i : Fin (ν₁ + 1))
    (x : (Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) :
    residLinearU ν₁ ν₂ (Sum.inl i) x =
      x (Sum.inl i) - (∑ i', x (Sum.inl i')) / (ν₁ + 1) := by
  simp [residLinearU, selectXLinearU]

@[simp]
theorem residLinearU_apply_inr (ν₁ ν₂ : ℕ) (j : Fin (ν₂ + 1))
    (x : (Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) :
    residLinearU ν₁ ν₂ (Sum.inr j) x =
      x (Sum.inr j) - (∑ j', x (Sum.inr j')) / (ν₂ + 1) := by
  simp [residLinearU, selectYLinearU]

namespace TwoNormalSamplesU

variable {ν₁ ν₂ : ℕ}
  {X : Fin (ν₁ + 1) → Ω → ℝ} {Y : Fin (ν₂ + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}

/-- The law of an arbitrary joint coordinate. -/
theorem law_coord (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (k : Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) :
    HasLaw (obsU X Y k) (gaussianReal μ (varU ν₁ ν₂ v₁ v₂ k)) P := by
  cases k with
  | inl i => exact h.lawX i
  | inr j => exact h.lawY j

theorem hasGaussianLaw_coord
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (k : Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) :
    HasGaussianLaw (obsU X Y k) P :=
  (h.law_coord k).hasGaussianLaw

theorem memLp_two_coord
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (k : Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) :
    MemLp (obsU X Y k) 2 P :=
  (h.hasGaussianLaw_coord k).memLp_two

theorem integral_coord
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (k : Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) :
    ∫ ω, obsU X Y k ω ∂P = μ := by
  rw [(h.law_coord k).integral_eq, integral_id_gaussianReal]

theorem variance_coord
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (k : Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) :
    ProbabilityTheory.variance (obsU X Y k) P = varU ν₁ ν₂ v₁ v₂ k := by
  rw [(h.law_coord k).variance_eq, variance_id_gaussianReal]

/-- The joint covariance matrix is diagonal. -/
theorem covariance_coord
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (k l : Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) :
    covariance (obsU X Y k) (obsU X Y l) P =
      if k = l then (varU ν₁ ν₂ v₁ v₂ k : ℝ) else 0 := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  by_cases heq : k = l
  · subst heq
    rw [if_pos rfl, covariance_self (h.law_coord k).aemeasurable,
      h.variance_coord]
  · rw [if_neg heq]
    exact (h.indep.indepFun heq).covariance_eq_zero
      (h.memLp_two_coord k) (h.memLp_two_coord l)

/-- All `n₁ + n₂` observations form one jointly Gaussian vector. -/
theorem hasGaussianLaw_all
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    HasGaussianLaw (fun ω k => obsU X Y k ω) P :=
  h.indep.hasGaussianLaw fun k => h.hasGaussianLaw_coord k

/-- The first sample is jointly Gaussian. -/
theorem hasGaussianLaw_sampleX
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    HasGaussianLaw (fun ω i => X i ω) P :=
  (h.indep.precomp Sum.inl_injective).hasGaussianLaw
    (fun i => (h.lawX i).hasGaussianLaw)

/-- The second sample is jointly Gaussian. -/
theorem hasGaussianLaw_sampleY
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    HasGaussianLaw (fun ω j => Y j ω) P :=
  (h.indep.precomp Sum.inr_injective).hasGaussianLaw
    (fun j => (h.lawY j).hasGaussianLaw)

/-- Covariance within the first sample. -/
theorem covariance_coordX
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) (i j : Fin (ν₁ + 1)) :
    covariance (X i) (X j) P = if i = j then (v₁ : ℝ) else 0 := by
  have := h.covariance_coord (Sum.inl i) (Sum.inl j)
  simpa [obsU, varU, Sum.inl.injEq] using this

/-- Covariance within the second sample. -/
theorem covariance_coordY
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) (i j : Fin (ν₂ + 1)) :
    covariance (Y i) (Y j) P = if i = j then (v₂ : ℝ) else 0 := by
  have := h.covariance_coord (Sum.inr i) (Sum.inr j)
  simpa [obsU, varU, Sum.inr.injEq] using this

/-- The mean of the first sample is Gaussian. -/
theorem hasGaussianLaw_sampleMeanX
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    HasGaussianLaw (sampleMeanN ν₁ X) P := by
  have hsum : HasGaussianLaw (fun ω => ∑ i, X i ω) P :=
    h.hasGaussianLaw_sampleX.fun_sum
  have hscaled := hsum.fun_smul ((((ν₁ + 1 : ℕ) : ℝ))⁻¹)
  apply hscaled.congr
  filter_upwards [] with ω
  simp only [smul_eq_mul, sampleMeanN, div_eq_mul_inv]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

/-- The mean of the second sample is Gaussian. -/
theorem hasGaussianLaw_sampleMeanY
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    HasGaussianLaw (sampleMeanN ν₂ Y) P := by
  have hsum : HasGaussianLaw (fun ω => ∑ j, Y j ω) P :=
    h.hasGaussianLaw_sampleY.fun_sum
  have hscaled := hsum.fun_smul ((((ν₂ + 1 : ℕ) : ℝ))⁻¹)
  apply hscaled.congr
  filter_upwards [] with ω
  simp only [smul_eq_mul, sampleMeanN, div_eq_mul_inv]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

theorem integral_sampleMeanX
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    ∫ ω, sampleMeanN ν₁ X ω ∂P = μ := by
  unfold sampleMeanN
  rw [integral_div]
  rw [integral_finsetSum Finset.univ
    (fun i _ => ((h.lawX i).hasGaussianLaw).integrable)]
  have : ∀ i : Fin (ν₁ + 1), ∫ ω, X i ω ∂P = μ := fun i =>
    h.integral_coord (Sum.inl i)
  simp_rw [this]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hν : (((ν₁ + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  norm_num [Nat.cast_add, Nat.cast_one] at hν ⊢
  field_simp

theorem integral_sampleMeanY
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    ∫ ω, sampleMeanN ν₂ Y ω ∂P = μ := by
  unfold sampleMeanN
  rw [integral_div]
  rw [integral_finsetSum Finset.univ
    (fun j _ => ((h.lawY j).hasGaussianLaw).integrable)]
  have : ∀ j : Fin (ν₂ + 1), ∫ ω, Y j ω ∂P = μ := fun j =>
    h.integral_coord (Sum.inr j)
  simp_rw [this]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hν : (((ν₂ + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  norm_num [Nat.cast_add, Nat.cast_one] at hν ⊢
  field_simp

theorem variance_sampleMeanX
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    ProbabilityTheory.variance (sampleMeanN ν₁ X) P =
      (v₁ : ℝ) / (ν₁ + 1) := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hLp : ∀ i, MemLp (X i) 2 P := fun i =>
    h.memLp_two_coord (Sum.inl i)
  unfold sampleMeanN
  simp only [div_eq_mul_inv]
  rw [variance_mul_const]
  rw [variance_fun_sum hLp]
  have : ∀ i j : Fin (ν₁ + 1),
      covariance (X i) (X j) P = if i = j then (v₁ : ℝ) else 0 :=
    h.covariance_coordX
  simp_rw [this]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hν : (((ν₁ + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  norm_num [Nat.cast_add, Nat.cast_one] at hν ⊢
  field_simp

theorem variance_sampleMeanY
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    ProbabilityTheory.variance (sampleMeanN ν₂ Y) P =
      (v₂ : ℝ) / (ν₂ + 1) := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hLp : ∀ j, MemLp (Y j) 2 P := fun j =>
    h.memLp_two_coord (Sum.inr j)
  unfold sampleMeanN
  simp only [div_eq_mul_inv]
  rw [variance_mul_const]
  rw [variance_fun_sum hLp]
  have : ∀ i j : Fin (ν₂ + 1),
      covariance (Y i) (Y j) P = if i = j then (v₂ : ℝ) else 0 :=
    h.covariance_coordY
  simp_rw [this]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hν : (((ν₂ + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  norm_num [Nat.cast_add, Nat.cast_one] at hν ⊢
  field_simp

/-- Exact law of the first sample mean: `N(μ, v₁ / n₁)`. -/
theorem hasLaw_sampleMeanX
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    HasLaw (sampleMeanN ν₁ X)
      (gaussianReal μ (v₁ / (ν₁ + 1))) P := by
  refine
    { aemeasurable := h.hasGaussianLaw_sampleMeanX.aemeasurable
      map_eq := ?_ }
  rw [h.hasGaussianLaw_sampleMeanX.map_eq_gaussianReal,
    h.integral_sampleMeanX, h.variance_sampleMeanX]
  congr 1
  ext
  calc
    ↑(((↑v₁ / (ν₁ + 1) : ℝ)).toNNReal) = (↑v₁ / (ν₁ + 1) : ℝ) :=
      Real.coe_toNNReal _ (by positivity)
    _ = ↑(v₁ / (ν₁ + 1)) := by
      push_cast
      simp

/-- Exact law of the second sample mean: `N(μ, v₂ / n₂)`. -/
theorem hasLaw_sampleMeanY
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    HasLaw (sampleMeanN ν₂ Y)
      (gaussianReal μ (v₂ / (ν₂ + 1))) P := by
  refine
    { aemeasurable := h.hasGaussianLaw_sampleMeanY.aemeasurable
      map_eq := ?_ }
  rw [h.hasGaussianLaw_sampleMeanY.map_eq_gaussianReal,
    h.integral_sampleMeanY, h.variance_sampleMeanY]
  congr 1
  ext
  calc
    ↑(((↑v₂ / (ν₂ + 1) : ℝ)).toNNReal) = (↑v₂ / (ν₂ + 1) : ℝ) :=
      Real.coe_toNNReal _ (by positivity)
    _ = ↑(v₂ / (ν₂ + 1)) := by
      push_cast
      simp

/-- The pair of complete sample vectors is jointly Gaussian. -/
theorem hasGaussianLaw_sample_pair
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    HasGaussianLaw
      (fun ω => (fun i => X i ω, fun j => Y j ω)) P := by
  have hmap := h.hasGaussianLaw_all.map_fun (splitSamplesLinearU ν₁ ν₂)
  apply hmap.congr
  filter_upwards [] with ω
  simp [obsU]

/-- The two complete sample vectors are independent. -/
theorem indepFun_sample_pair
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    IndepFun (fun ω i => X i ω) (fun ω j => Y j ω) P := by
  apply h.hasGaussianLaw_sample_pair.indepFun_of_covariance_eval
  intro i j
  have := h.covariance_coord (Sum.inl i) (Sum.inr j)
  simpa [obsU] using this

/-- The two sample means are independent. -/
theorem indepFun_sampleMeans
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    IndepFun (sampleMeanN ν₁ X) (sampleMeanN ν₂ Y) P := by
  have hmeans :=
    h.indepFun_sample_pair.comp
      (show Measurable (sampleMeanLinearN ν₁) by fun_prop)
      (show Measurable (sampleMeanLinearN ν₂) by fun_prop)
  apply hmeans.congr
  · filter_upwards [] with ω
    simp [Function.comp_apply, sampleMeanN]
  · filter_upwards [] with ω
    simp [Function.comp_apply, sampleMeanN]

/-- The mean difference is Gaussian. -/
theorem hasGaussianLaw_meanDifference
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    HasGaussianLaw (meanDifferenceU ν₁ ν₂ X Y) P := by
  have hpair :
      HasGaussianLaw
        (fun ω => (sampleMeanN ν₂ Y ω, sampleMeanN ν₁ X ω)) P :=
    h.indepFun_sampleMeans.symm.hasGaussianLaw
      h.hasGaussianLaw_sampleMeanY
      h.hasGaussianLaw_sampleMeanX
  apply hpair.fun_sub.congr
  filter_upwards [] with ω
  rfl

theorem integral_meanDifference
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    ∫ ω, meanDifferenceU ν₁ ν₂ X Y ω ∂P = 0 := by
  unfold meanDifferenceU
  rw [integral_sub
    h.hasGaussianLaw_sampleMeanY.integrable
    h.hasGaussianLaw_sampleMeanX.integrable,
    h.integral_sampleMeanY, h.integral_sampleMeanX]
  ring

/-- `Var(D) = v₁/n₁ + v₂/n₂`. -/
theorem variance_meanDifference
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    ProbabilityTheory.variance (meanDifferenceU ν₁ ν₂ X Y) P =
      (v₁ : ℝ) / (ν₁ + 1) + (v₂ : ℝ) / (ν₂ + 1) := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hmeanY : MemLp (sampleMeanN ν₂ Y) 2 P :=
    h.hasGaussianLaw_sampleMeanY.memLp_two
  have hmeanX : MemLp (sampleMeanN ν₁ X) 2 P :=
    h.hasGaussianLaw_sampleMeanX.memLp_two
  have hcov :
      covariance (sampleMeanN ν₂ Y) (sampleMeanN ν₁ X) P = 0 :=
    h.indepFun_sampleMeans.symm.covariance_eq_zero hmeanY hmeanX
  unfold meanDifferenceU
  rw [variance_fun_sub hmeanY hmeanX,
    h.variance_sampleMeanY, h.variance_sampleMeanX, hcov]
  ring

/-- Exact law of `D = Ȳ - X̄`: centered normal with variance
`v₁/n₁ + v₂/n₂`. -/
theorem hasLaw_meanDifference
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    HasLaw (meanDifferenceU ν₁ ν₂ X Y)
      (gaussianReal 0 (v₁ / (ν₁ + 1) + v₂ / (ν₂ + 1))) P := by
  refine
    { aemeasurable := h.hasGaussianLaw_meanDifference.aemeasurable
      map_eq := ?_ }
  rw [h.hasGaussianLaw_meanDifference.map_eq_gaussianReal,
    h.integral_meanDifference, h.variance_meanDifference]
  congr 1
  ext
  calc
    ↑((((v₁ : ℝ) / (ν₁ + 1) + (v₂ : ℝ) / (ν₂ + 1))).toNNReal) =
        ((v₁ : ℝ) / (ν₁ + 1) + (v₂ : ℝ) / (ν₂ + 1)) :=
      Real.coe_toNNReal _ (by positivity)
    _ = ↑(v₁ / (ν₁ + 1) + v₂ / (ν₂ + 1)) := by
      push_cast
      simp

/-- For a fixed weight `θ`, the uncentered oracle estimator and the mean
difference are jointly Gaussian. -/
theorem hasGaussianLaw_oracleUncentered_meanDifference
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) (θ : ℝ) :
    HasGaussianLaw
      (fun ω =>
        (sampleMeanN ν₁ X ω + θ * meanDifferenceU ν₁ ν₂ X Y ω,
          meanDifferenceU ν₁ ν₂ X Y ω)) P := by
  have hmeans :
      HasGaussianLaw
        (fun ω => (sampleMeanN ν₁ X ω, sampleMeanN ν₂ Y ω)) P :=
    h.indepFun_sampleMeans.hasGaussianLaw
      h.hasGaussianLaw_sampleMeanX
      h.hasGaussianLaw_sampleMeanY
  let d : (ℝ × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ
  let transform : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ + θ • d).prod d
  have hmap := hmeans.map_fun transform
  apply hmap.congr
  filter_upwards [] with ω
  simp [transform, d, meanDifferenceU]

/-- `Cov(X̄, D) = -v₁/n₁`. -/
theorem covariance_sampleMeanX_meanDifference
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    covariance (sampleMeanN ν₁ X) (meanDifferenceU ν₁ ν₂ X Y) P =
      -(v₁ : ℝ) / (ν₁ + 1) := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hmeanX : MemLp (sampleMeanN ν₁ X) 2 P :=
    h.hasGaussianLaw_sampleMeanX.memLp_two
  have hmeanY : MemLp (sampleMeanN ν₂ Y) 2 P :=
    h.hasGaussianLaw_sampleMeanY.memLp_two
  have hcross :
      covariance (sampleMeanN ν₁ X) (sampleMeanN ν₂ Y) P = 0 :=
    h.indepFun_sampleMeans.covariance_eq_zero hmeanX hmeanY
  unfold meanDifferenceU
  rw [covariance_fun_sub_right hmeanX hmeanY hmeanX, hcross,
    covariance_self hmeanX.aemeasurable, h.variance_sampleMeanX]
  ring

/-- Covariance of the uncentered oracle estimator with `D`. -/
theorem covariance_oracleUncentered_meanDifference
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) (θ : ℝ) :
    covariance
      (fun ω =>
        sampleMeanN ν₁ X ω + θ * meanDifferenceU ν₁ ν₂ X Y ω)
      (meanDifferenceU ν₁ ν₂ X Y) P =
    -(v₁ : ℝ) / (ν₁ + 1)
      + θ * ((v₁ : ℝ) / (ν₁ + 1) + (v₂ : ℝ) / (ν₂ + 1)) := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hmeanX : MemLp (sampleMeanN ν₁ X) 2 P :=
    h.hasGaussianLaw_sampleMeanX.memLp_two
  have hD : MemLp (meanDifferenceU ν₁ ν₂ X Y) 2 P :=
    h.hasGaussianLaw_meanDifference.memLp_two
  rw [show
    (fun ω =>
      sampleMeanN ν₁ X ω + θ * meanDifferenceU ν₁ ν₂ X Y ω) =
    sampleMeanN ν₁ X + fun ω => θ * meanDifferenceU ν₁ ν₂ X Y ω from rfl]
  rw [covariance_add_left hmeanX (hD.const_mul θ) hD,
    covariance_const_mul_left,
    h.covariance_sampleMeanX_meanDifference,
    covariance_self hD.aemeasurable,
    h.variance_meanDifference]

/--
**Oracle independence, unequal sizes.**  At the known-variance oracle
weight `θ = τ₁ / (τ₁ + τ₂)` with `τᵢ = vᵢ / nᵢ`, the centered error of
`X̄ + θ D` is independent of the mean difference `D`.

This is the identity that makes the risk decomposition
`R(w) - R(r) = E[D²((w-θ)² - (r-θ)²)]` valid for weights `w` that
depend on `D²` as well as on the two sample variances.
-/
theorem indepFun_oracleCenteredError_meanDifference
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hsum : 0 < (v₁ : ℝ) / (ν₁ + 1) + (v₂ : ℝ) / (ν₂ + 1)) :
    IndepFun
      (oracleCenteredErrorU ν₁ ν₂ μ
        (oracleVarianceWeightU ν₁ ν₂ v₁ v₂) X Y)
      (meanDifferenceU ν₁ ν₂ X Y) P := by
  let θ := oracleVarianceWeightU ν₁ ν₂ v₁ v₂
  have hcov :
      covariance
        (fun ω =>
          sampleMeanN ν₁ X ω + θ * meanDifferenceU ν₁ ν₂ X Y ω)
        (meanDifferenceU ν₁ ν₂ X Y) P = 0 := by
    rw [h.covariance_oracleUncentered_meanDifference]
    dsimp only [θ, oracleVarianceWeightU]
    rw [div_mul_cancel₀ _ (ne_of_gt hsum)]
    ring
  have hindep :
      IndepFun
        (fun ω =>
          sampleMeanN ν₁ X ω + θ * meanDifferenceU ν₁ ν₂ X Y ω)
        (meanDifferenceU ν₁ ν₂ X Y) P :=
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

/-- Cross-sample coordinates are uncorrelated. -/
theorem covariance_coordXY
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (i : Fin (ν₁ + 1)) (j : Fin (ν₂ + 1)) :
    covariance (X i) (Y j) P = 0 := by
  have := h.covariance_coord (Sum.inl i) (Sum.inr j)
  simpa [obsU] using this

/-- The two sample means are uncorrelated. -/
theorem covariance_sampleMeans_cross
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    covariance (sampleMeanN ν₁ X) (sampleMeanN ν₂ Y) P = 0 :=
  h.indepFun_sampleMeans.covariance_eq_zero
    h.hasGaussianLaw_sampleMeanX.memLp_two
    h.hasGaussianLaw_sampleMeanY.memLp_two

/-- `Cov(X̄, X i) = v₁ / n₁`. -/
theorem covariance_sampleMeanX_coordX
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) (i : Fin (ν₁ + 1)) :
    covariance (sampleMeanN ν₁ X) (X i) P = (v₁ : ℝ) / (ν₁ + 1) := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hLp : ∀ i', MemLp (X i') 2 P := fun i' =>
    h.memLp_two_coord (Sum.inl i')
  unfold sampleMeanN
  rw [covariance_fun_div_left]
  rw [covariance_fun_sum_left hLp (hLp i)]
  have : ∀ i' j : Fin (ν₁ + 1),
      covariance (X i') (X j) P = if i' = j then (v₁ : ℝ) else 0 :=
    h.covariance_coordX
  simp_rw [this]
  simp

/-- `Cov(X̄, Y j) = 0`. -/
theorem covariance_sampleMeanX_coordY
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) (j : Fin (ν₂ + 1)) :
    covariance (sampleMeanN ν₁ X) (Y j) P = 0 := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hLpX : ∀ i, MemLp (X i) 2 P := fun i =>
    h.memLp_two_coord (Sum.inl i)
  have hLpY : MemLp (Y j) 2 P := h.memLp_two_coord (Sum.inr j)
  unfold sampleMeanN
  rw [covariance_fun_div_left]
  rw [covariance_fun_sum_left hLpX hLpY]
  have : ∀ i : Fin (ν₁ + 1), covariance (X i) (Y j) P = 0 := fun i =>
    h.covariance_coordXY i j
  simp_rw [this]
  simp

/-- `Cov(Ȳ, X i) = 0`. -/
theorem covariance_sampleMeanY_coordX
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) (i : Fin (ν₁ + 1)) :
    covariance (sampleMeanN ν₂ Y) (X i) P = 0 := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hLpY : ∀ j, MemLp (Y j) 2 P := fun j =>
    h.memLp_two_coord (Sum.inr j)
  have hLpX : MemLp (X i) 2 P := h.memLp_two_coord (Sum.inl i)
  unfold sampleMeanN
  rw [covariance_fun_div_left]
  rw [covariance_fun_sum_left hLpY hLpX]
  have : ∀ j : Fin (ν₂ + 1), covariance (Y j) (X i) P = 0 := fun j => by
    rw [covariance_comm]
    exact h.covariance_coordXY i j
  simp_rw [this]
  simp

/-- `Cov(Ȳ, Y j) = v₂ / n₂`. -/
theorem covariance_sampleMeanY_coordY
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) (j : Fin (ν₂ + 1)) :
    covariance (sampleMeanN ν₂ Y) (Y j) P = (v₂ : ℝ) / (ν₂ + 1) := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hLp : ∀ j', MemLp (Y j') 2 P := fun j' =>
    h.memLp_two_coord (Sum.inr j')
  unfold sampleMeanN
  rw [covariance_fun_div_left]
  rw [covariance_fun_sum_left hLp (hLp j)]
  have : ∀ j' i : Fin (ν₂ + 1),
      covariance (Y j') (Y i) P = if j' = i then (v₂ : ℝ) else 0 :=
    h.covariance_coordY
  simp_rw [this]
  simp

/-- Every residual coordinate of the first sample is uncorrelated with `X̄`. -/
theorem covariance_sampleMeanX_residualX
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) (i : Fin (ν₁ + 1)) :
    covariance (sampleMeanN ν₁ X)
      (fun ω => sampleResidualN ν₁ X ω i) P = 0 := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hmean : MemLp (sampleMeanN ν₁ X) 2 P :=
    h.hasGaussianLaw_sampleMeanX.memLp_two
  have hLpXi : MemLp (X i) 2 P := h.memLp_two_coord (Sum.inl i)
  unfold sampleResidualN
  rw [covariance_fun_sub_right hmean hLpXi hmean]
  rw [h.covariance_sampleMeanX_coordX,
    covariance_self hmean.aemeasurable, h.variance_sampleMeanX]
  ring

/-- Every residual coordinate of the second sample is uncorrelated with `X̄`. -/
theorem covariance_sampleMeanX_residualY
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) (j : Fin (ν₂ + 1)) :
    covariance (sampleMeanN ν₁ X)
      (fun ω => sampleResidualN ν₂ Y ω j) P = 0 := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hmeanX : MemLp (sampleMeanN ν₁ X) 2 P :=
    h.hasGaussianLaw_sampleMeanX.memLp_two
  have hmeanY : MemLp (sampleMeanN ν₂ Y) 2 P :=
    h.hasGaussianLaw_sampleMeanY.memLp_two
  have hLpYj : MemLp (Y j) 2 P := h.memLp_two_coord (Sum.inr j)
  unfold sampleResidualN
  rw [covariance_fun_sub_right hmeanX hLpYj hmeanY]
  rw [h.covariance_sampleMeanX_coordY, h.covariance_sampleMeans_cross]
  ring

/-- Every residual coordinate of the first sample is uncorrelated with `Ȳ`. -/
theorem covariance_sampleMeanY_residualX
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) (i : Fin (ν₁ + 1)) :
    covariance (sampleMeanN ν₂ Y)
      (fun ω => sampleResidualN ν₁ X ω i) P = 0 := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hmeanX : MemLp (sampleMeanN ν₁ X) 2 P :=
    h.hasGaussianLaw_sampleMeanX.memLp_two
  have hmeanY : MemLp (sampleMeanN ν₂ Y) 2 P :=
    h.hasGaussianLaw_sampleMeanY.memLp_two
  have hLpXi : MemLp (X i) 2 P := h.memLp_two_coord (Sum.inl i)
  unfold sampleResidualN
  rw [covariance_fun_sub_right hmeanY hLpXi hmeanX]
  rw [h.covariance_sampleMeanY_coordX]
  rw [covariance_comm, h.covariance_sampleMeans_cross]
  ring

/-- Every residual coordinate of the second sample is uncorrelated with `Ȳ`. -/
theorem covariance_sampleMeanY_residualY
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) (j : Fin (ν₂ + 1)) :
    covariance (sampleMeanN ν₂ Y)
      (fun ω => sampleResidualN ν₂ Y ω j) P = 0 := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hmean : MemLp (sampleMeanN ν₂ Y) 2 P :=
    h.hasGaussianLaw_sampleMeanY.memLp_two
  have hLpYj : MemLp (Y j) 2 P := h.memLp_two_coord (Sum.inr j)
  unfold sampleResidualN
  rw [covariance_fun_sub_right hmean hLpYj hmean]
  rw [h.covariance_sampleMeanY_coordY,
    covariance_self hmean.aemeasurable, h.variance_sampleMeanY]
  ring

/--
For any square-integrable `Z` uncorrelated with both sample means, the
uncentered oracle estimator `X̄ + θ D` is uncorrelated with `Z`, for every
weight `θ`.
-/
theorem covariance_oracleUncentered_of_mean_covs
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    {Z : Ω → ℝ} (hZ : MemLp Z 2 P)
    (hX0 : covariance (sampleMeanN ν₁ X) Z P = 0)
    (hY0 : covariance (sampleMeanN ν₂ Y) Z P = 0) (θ : ℝ) :
    covariance
      (fun ω => sampleMeanN ν₁ X ω + θ * meanDifferenceU ν₁ ν₂ X Y ω)
      Z P = 0 := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hmeanX : MemLp (sampleMeanN ν₁ X) 2 P :=
    h.hasGaussianLaw_sampleMeanX.memLp_two
  have hmeanY : MemLp (sampleMeanN ν₂ Y) 2 P :=
    h.hasGaussianLaw_sampleMeanY.memLp_two
  have hD : MemLp (meanDifferenceU ν₁ ν₂ X Y) 2 P :=
    h.hasGaussianLaw_meanDifference.memLp_two
  have hDZ : covariance (meanDifferenceU ν₁ ν₂ X Y) Z P = 0 := by
    unfold meanDifferenceU
    rw [covariance_fun_sub_left hmeanY hmeanX hZ, hX0, hY0]
    ring
  rw [show
    (fun ω =>
      sampleMeanN ν₁ X ω + θ * meanDifferenceU ν₁ ν₂ X Y ω) =
    sampleMeanN ν₁ X + fun ω => θ * meanDifferenceU ν₁ ν₂ X Y ω from rfl]
  rw [covariance_add_left hmeanX (hD.const_mul θ) hZ,
    covariance_const_mul_left, hX0, hDZ]
  ring

/--
The uncentered oracle estimator, the mean difference, and the full pair of
residual vectors are jointly Gaussian, packaged in the block form needed for
the covariance-criterion independence lemma.
-/
theorem hasGaussianLaw_oracleUncentered_diff_residuals
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) (θ : ℝ) :
    HasGaussianLaw
      (fun ω =>
        (fun _ : Unit =>
          sampleMeanN ν₁ X ω + θ * meanDifferenceU ν₁ ν₂ X Y ω,
          fun k : Option (Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) =>
            Option.elim k (meanDifferenceU ν₁ ν₂ X Y ω)
              (Sum.elim
                (fun i => sampleResidualN ν₁ X ω i)
                (fun j => sampleResidualN ν₂ Y ω j)))) P := by
  let oracleCLM :
      ((Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) →L[ℝ] ℝ :=
    meanXLinearU ν₁ ν₂ + θ • diffLinearU ν₁ ν₂
  let split :
      ((Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1)) → ℝ) →L[ℝ]
        ((Unit → ℝ) ×
          ((Option (Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1))) → ℝ)) :=
    (ContinuousLinearMap.pi fun _ : Unit => oracleCLM).prod
      (ContinuousLinearMap.pi fun k =>
        Option.elim k (diffLinearU ν₁ ν₂) (residLinearU ν₁ ν₂))
  have hmap := h.hasGaussianLaw_all.map_fun split
  apply hmap.congr
  filter_upwards [] with ω
  refine Prod.ext ?_ ?_
  · funext u
    simp [split, oracleCLM, obsU, sampleMeanN, meanDifferenceU, mul_sub]
  · funext k
    cases k with
    | none =>
      simp [split, obsU, meanDifferenceU, sampleMeanN]
    | some s =>
      cases s with
      | inl i =>
        simp [split, obsU, sampleResidualN, sampleMeanN]
      | inr j =>
        simp [split, obsU, sampleResidualN, sampleMeanN]

/--
**Joint oracle independence, unequal sizes.**  At the oracle weight, the
centered error of `X̄ + θ D` is independent of the triple
`(D, RSS₁, RSS₂)`.  This is the exact independence input for the risk
decomposition `R(w) - R(r) = E[D²((w-θ)² - (r-θ)²)]` with weights
depending on `D²` and both sample variances.
-/
theorem indepFun_oracleCenteredError_meanDifference_residualSumSquares
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hsum : 0 < (v₁ : ℝ) / (ν₁ + 1) + (v₂ : ℝ) / (ν₂ + 1)) :
    IndepFun
      (oracleCenteredErrorU ν₁ ν₂ μ
        (oracleVarianceWeightU ν₁ ν₂ v₁ v₂) X Y)
      (fun ω =>
        (meanDifferenceU ν₁ ν₂ X Y ω,
          residualSumSquaresN ν₁ X ω,
          residualSumSquaresN ν₂ Y ω)) P := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  let θ := oracleVarianceWeightU ν₁ ν₂ v₁ v₂
  have hmeanX : MemLp (sampleMeanN ν₁ X) 2 P :=
    h.hasGaussianLaw_sampleMeanX.memLp_two
  have hLpResidX : ∀ i, MemLp (fun ω => sampleResidualN ν₁ X ω i) 2 P :=
    fun i => (h.memLp_two_coord (Sum.inl i)).sub hmeanX
  have hmeanY : MemLp (sampleMeanN ν₂ Y) 2 P :=
    h.hasGaussianLaw_sampleMeanY.memLp_two
  have hLpResidY : ∀ j, MemLp (fun ω => sampleResidualN ν₂ Y ω j) 2 P :=
    fun j => (h.memLp_two_coord (Sum.inr j)).sub hmeanY
  have hcovD :
      covariance
        (fun ω =>
          sampleMeanN ν₁ X ω + θ * meanDifferenceU ν₁ ν₂ X Y ω)
        (meanDifferenceU ν₁ ν₂ X Y) P = 0 := by
    rw [h.covariance_oracleUncentered_meanDifference]
    dsimp only [θ, oracleVarianceWeightU]
    rw [div_mul_cancel₀ _ (ne_of_gt hsum)]
    ring
  have hblocks :
      IndepFun
        (fun ω (_ : Unit) =>
          sampleMeanN ν₁ X ω + θ * meanDifferenceU ν₁ ν₂ X Y ω)
        (fun ω (k : Option (Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1))) =>
          Option.elim k (meanDifferenceU ν₁ ν₂ X Y ω)
            (Sum.elim
              (fun i => sampleResidualN ν₁ X ω i)
              (fun j => sampleResidualN ν₂ Y ω j))) P := by
    apply (h.hasGaussianLaw_oracleUncentered_diff_residuals θ)
      |>.indepFun_of_covariance_eval
    intro _ k
    cases k with
    | none => exact hcovD
    | some s =>
      cases s with
      | inl i =>
        exact h.covariance_oracleUncentered_of_mean_covs
          (hLpResidX i)
          (h.covariance_sampleMeanX_residualX i)
          (h.covariance_sampleMeanY_residualX i) θ
      | inr j =>
        exact h.covariance_oracleUncentered_of_mean_covs
          (hLpResidY j)
          (h.covariance_sampleMeanX_residualY j)
          (h.covariance_sampleMeanY_residualY j) θ
  have hcomp :=
    hblocks.comp
      (show Measurable (fun f : Unit → ℝ => f () - μ) by fun_prop)
      (show Measurable
          (fun f : (Option (Fin (ν₁ + 1) ⊕ Fin (ν₂ + 1))) → ℝ =>
            (f none,
              ∑ i, f (some (Sum.inl i)) ^ 2,
              ∑ j, f (some (Sum.inr j)) ^ 2)) by fun_prop)
  apply hcomp.congr
  · filter_upwards [] with ω
    rfl
  · filter_upwards [] with ω
    simp only [Function.comp_apply, Option.elim, Sum.elim_inl,
      Sum.elim_inr, residualSumSquaresN]

end TwoNormalSamplesU

end

end GraybillDeal
