import GraybillDeal.UniversalLimitingBayes

/-!
# Endpoint reweighting of finite priors

The full reduced density contains a parameter-only endpoint factor

`θ ^ (b + 3 / 2) * (1 - θ) ^ (a + 3 / 2)`.

For a finite prior supported in the open interval this factor is strictly
positive.  It can therefore be absorbed into the prior and normalized
without changing the posterior weighted mean.  This file formalizes that
finite algebraic bridge.
-/

namespace GraybillDeal

open MeasureTheory
open scoped BigOperators NNReal

noncomputable section

/-- A finite prior whose support presentation lies strictly inside
`(0,1)`.  Repeated support points remain allowed. -/
structure UniversalInteriorFinitePrior extends UniversalFinitePrior where
  point_pos : ∀ i, 0 < (point i : ℝ)
  point_lt_one : ∀ i, (point i : ℝ) < 1

/-- The parameter-only endpoint factor in the full reduced density. -/
def universalEndpointWeight (a b : ℝ) (θ : UniversalTheta) : ℝ :=
  (θ : ℝ) ^ (b + 3 / 2) *
    (1 - (θ : ℝ)) ^ (a + 3 / 2)

theorem universalEndpointWeight_nonneg
    (a b : ℝ) (θ : UniversalTheta) :
    0 ≤ universalEndpointWeight a b θ := by
  unfold universalEndpointWeight
  exact mul_nonneg
    (Real.rpow_nonneg θ.property.1 _)
    (Real.rpow_nonneg (sub_nonneg.mpr θ.property.2) _)

theorem universalEndpointWeight_pos
    {a b : ℝ} {θ : UniversalTheta}
    (hθ0 : 0 < (θ : ℝ)) (hθ1 : (θ : ℝ) < 1) :
    0 < universalEndpointWeight a b θ := by
  unfold universalEndpointWeight
  exact mul_pos
    (Real.rpow_pos_of_pos hθ0 _)
    (Real.rpow_pos_of_pos (sub_pos.mpr hθ1) _)

/-- The endpoint factor bundled as a nonnegative real. -/
def universalEndpointWeightNNReal
    (a b : ℝ) (θ : UniversalTheta) : ℝ≥0 :=
  Real.toNNReal (universalEndpointWeight a b θ)

@[simp]
theorem coe_universalEndpointWeightNNReal
    (a b : ℝ) (θ : UniversalTheta) :
    (universalEndpointWeightNNReal a b θ : ℝ)
      = universalEndpointWeight a b θ := by
  exact Real.coe_toNNReal _
    (universalEndpointWeight_nonneg a b θ)

theorem universalEndpointWeightNNReal_pos
    {a b : ℝ} {θ : UniversalTheta}
    (hθ0 : 0 < (θ : ℝ)) (hθ1 : (θ : ℝ) < 1) :
    0 < universalEndpointWeightNNReal a b θ := by
  exact Real.toNNReal_pos.mpr
    (universalEndpointWeight_pos hθ0 hθ1)

namespace UniversalInteriorFinitePrior

/-- The endpoint factor is strictly positive at every presented support
point of an interior finite prior. -/
theorem endpointWeight_pos_on_support
    (π : UniversalInteriorFinitePrior) (a b : ℝ)
    (i : Fin π.card) :
    0 < universalEndpointWeight a b (π.point i) :=
  universalEndpointWeight_pos
    (π.point_pos i) (π.point_lt_one i)

/-- The total unnormalized endpoint-reweighted mass. -/
def endpointNormalizer
    (π : UniversalInteriorFinitePrior) (a b : ℝ) : ℝ≥0 :=
  ∑ i, π.weight i *
    universalEndpointWeightNNReal a b (π.point i)

theorem exists_weight_pos
    (π : UniversalInteriorFinitePrior) :
    ∃ i, 0 < π.weight i := by
  have hsum : 0 < ∑ i, π.weight i := by
    rw [π.weight_sum]
    exact zero_lt_one
  rw [Finset.sum_pos_iff] at hsum
  simpa using hsum

theorem endpointNormalizer_pos
    (π : UniversalInteriorFinitePrior) (a b : ℝ) :
    0 < π.endpointNormalizer a b := by
  obtain ⟨i, hi⟩ := π.exists_weight_pos
  unfold endpointNormalizer
  exact Finset.sum_pos'
    (fun j hj => by positivity)
    ⟨i, Finset.mem_univ i,
      mul_pos hi
        (universalEndpointWeightNNReal_pos
          (π.point_pos i) (π.point_lt_one i))⟩

/-- Absorb the endpoint factor into the masses and normalize. -/
def endpointReweightedPrior
    (π : UniversalInteriorFinitePrior) (a b : ℝ) :
    UniversalFinitePrior where
  card := π.card
  point := π.point
  weight i :=
    (π.endpointNormalizer a b)⁻¹ *
      (π.weight i *
        universalEndpointWeightNNReal a b (π.point i))
  weight_sum := by
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀
      (ne_of_gt (π.endpointNormalizer_pos a b))

@[simp]
theorem endpointReweightedPrior_card
    (π : UniversalInteriorFinitePrior) (a b : ℝ) :
    (π.endpointReweightedPrior a b).card = π.card :=
  rfl

@[simp]
theorem endpointReweightedPrior_point
    (π : UniversalInteriorFinitePrior) (a b : ℝ)
    (i : Fin π.card) :
    (π.endpointReweightedPrior a b).point i = π.point i :=
  rfl

@[simp]
theorem endpointReweightedPrior_weight_coe
    (π : UniversalInteriorFinitePrior) (a b : ℝ)
    (i : Fin π.card) :
    ((π.endpointReweightedPrior a b).weight i : ℝ)
      =
    ((π.weight i : ℝ) *
        universalEndpointWeight a b (π.point i))
      / (π.endpointNormalizer a b : ℝ) := by
  unfold endpointReweightedPrior
  rw [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_mul,
    coe_universalEndpointWeightNNReal]
  field_simp

/-- The posterior mean computed with the full reduced density, after
dropping constants depending only on the observation. -/
def fullReducedPosteriorAction
    (π : UniversalInteriorFinitePrior)
    (a b r q : ℝ) : ℝ :=
  finiteWeightedMean Finset.univ
    (fun i =>
      (π.weight i : ℝ) *
        universalEndpointWeight a b (π.point i) *
        universalKernel a b r q (π.point i))
    (fun i => (π.point i : ℝ))

theorem fullReducedPosteriorWeightTotal_pos
    (π : UniversalInteriorFinitePrior)
    {a b r q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q) :
    0 <
      finiteWeightTotal Finset.univ
        (fun i =>
          (π.weight i : ℝ) *
            universalEndpointWeight a b (π.point i) *
            universalKernel a b r q (π.point i)) := by
  obtain ⟨i, hi⟩ := π.exists_weight_pos
  unfold finiteWeightTotal
  exact Finset.sum_pos'
    (fun j hj =>
      (mul_nonneg
        (mul_nonneg (NNReal.coe_nonneg (π.weight j))
          (universalEndpointWeight_nonneg a b (π.point j)))
        (universalKernel_pos
          ha hb hr0 hr1 hq (π.point j)).le))
    ⟨i, Finset.mem_univ i,
      mul_pos
        (mul_pos (by exact_mod_cast hi)
          (universalEndpointWeight_pos
            (π.point_pos i) (π.point_lt_one i)))
        (universalKernel_pos
          ha hb hr0 hr1 hq (π.point i))⟩

/-- Absorbing and normalizing the endpoint factor does not change the
finite posterior mean. -/
theorem fullReducedPosteriorAction_eq_reweighted
    (π : UniversalInteriorFinitePrior)
    {a b r q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q) :
    π.fullReducedPosteriorAction a b r q
      =
    universalFinitePriorPosteriorAction
      (π.endpointReweightedPrior a b) a b r q := by
  have hnormalizer :
      (π.endpointNormalizer a b : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (π.endpointNormalizer_pos a b)
  have hposterior :
      finiteWeightTotal Finset.univ
        (fun i =>
          (π.weight i : ℝ) *
            universalEndpointWeight a b (π.point i) *
            universalKernel a b r q (π.point i)) ≠ 0 :=
    ne_of_gt
      (π.fullReducedPosteriorWeightTotal_pos
        ha hb hr0 hr1 hq)
  have hcancel :=
    finiteWeightedMean_reweight_normalization
      Finset.univ
      (fun i => (π.weight i : ℝ))
      (fun i => universalEndpointWeight a b (π.point i))
      (fun i => universalKernel a b r q (π.point i))
      (fun i => (π.point i : ℝ))
      hnormalizer hposterior
  unfold fullReducedPosteriorAction
    universalFinitePriorPosteriorAction
  rw [← hcancel]
  congr 1
  funext i
  simp only [endpointReweightedPrior_weight_coe,
    endpointReweightedPrior_point]

end UniversalInteriorFinitePrior

end

end GraybillDeal
