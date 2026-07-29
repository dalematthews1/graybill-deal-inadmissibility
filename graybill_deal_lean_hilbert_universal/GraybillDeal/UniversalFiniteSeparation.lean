import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A finite-dimensional separation lemma for complete-class arguments

The proof of the finite-support limiting-Bayes theorem ultimately uses
convex separation.  Mathlib contains the geometric Hahn--Banach theorem,
but no statistical decision-theory wrapper around it.  This file supplies
the finite-dimensional core needed by such a wrapper.

Let `S` be a convex set of real risk vectors indexed by a finite parameter
set, and let `x ∈ S`.  If no vector in `S` is strictly smaller than `x` in
every coordinate, then there are nonnegative weights, summing to one, for
which `x` minimizes the weighted sum over `S`.

This is the finite-parameter supporting-prior theorem.  It is weaker than
the full Brown/Lehmann--Casella limiting-Bayes theorem: the latter also
constructs a sequence of finite parameter sets and proves almost-everywhere
convergence of the corresponding Bayes rules.
-/

namespace GraybillDeal

open Filter Set
open scoped BigOperators NNReal Topology

noncomputable section

namespace FiniteCompleteClass

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `i`th coordinate vector in a finite real product. -/
def coordinateVector (i : ι) : ι → ℝ :=
  Pi.single i 1

/-- The open strict lower orthant below `x`. -/
def strictLowerOrthant (x : ι → ℝ) : Set (ι → ℝ) :=
  {y | ∀ i, y i < x i}

theorem strictLowerOrthant_isOpen (x : ι → ℝ) :
    IsOpen (strictLowerOrthant x) := by
  rw [strictLowerOrthant, ← Set.iInter_setOf]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (continuous_apply i) continuous_const

theorem strictLowerOrthant_convex (x : ι → ℝ) :
    Convex ℝ (strictLowerOrthant x) := by
  intro y hy z hz a b ha hb hab i
  dsimp only [strictLowerOrthant, Set.mem_setOf_eq] at hy hz ⊢
  have hyi := hy i
  have hzi := hz i
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by linarith
    simpa [this] using hzi
  rcases hb.eq_or_lt with rfl | hb'
  · have : a = 1 := by linarith
    simpa [this] using hyi
  have hay : a * y i < a * x i :=
    mul_lt_mul_of_pos_left hyi ha'
  have hbz : b * z i < b * x i :=
    mul_lt_mul_of_pos_left hzi hb'
  calc
    a * y i + b * z i < a * x i + b * x i :=
      add_lt_add hay hbz
    _ = x i := by rw [← add_mul, hab, one_mul]

theorem strictLowerOrthant_nonempty (x : ι → ℝ) :
    (strictLowerOrthant x).Nonempty := by
  refine ⟨fun i => x i - 1, ?_⟩
  intro i
  simp [strictLowerOrthant]

/-- Every continuous linear functional on a finite product is the weighted
sum of its values on the coordinate vectors. -/
theorem continuousLinearMap_eq_sum_coordinates
    (f : StrongDual ℝ (ι → ℝ)) (z : ι → ℝ) :
    f z = ∑ i, f (coordinateVector i) * z i := by
  classical
  have hz : z = ∑ i, z i • coordinateVector i := by
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp [coordinateVector]
    · intro i _hi hij
      simp [coordinateVector, hij]
    · simp
  calc
    f z = f (∑ i, z i • coordinateVector i) := congrArg f hz
    _ = ∑ i, f (z i • coordinateVector i) := by rw [map_sum]
    _ = ∑ i, f (coordinateVector i) * z i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul]
      simp [mul_comm]

/-- Separation by the open lower orthant yields a nonzero functional
supporting `S` at `x`, nonnegative on every coordinate vector. -/
theorem exists_nonnegative_supporting_functional
    {S : Set (ι → ℝ)} {x : ι → ℝ}
    (hS : Convex ℝ S) (hx : x ∈ S)
    (hno : Disjoint (strictLowerOrthant x) S) :
    ∃ f : StrongDual ℝ (ι → ℝ),
      f ≠ 0 ∧
      (∀ i, 0 ≤ f (coordinateVector i)) ∧
      ∀ y ∈ S, f x ≤ f y := by
  obtain ⟨f, u, hlow, hhigh⟩ :=
    geometric_hahn_banach_open
      (strictLowerOrthant_convex x)
      (strictLowerOrthant_isOpen x)
      hS hno

  have hfx_le : f x ≤ u := by
    let y : ℕ → (ι → ℝ) :=
      fun n i => x i - (1 / ((n : ℝ) + 1))
    have hy_mem : ∀ n, y n ∈ strictLowerOrthant x := by
      intro n i
      dsimp [y]
      have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      linarith
    have hy_tendsto : Tendsto y atTop (𝓝 x) := by
      apply tendsto_pi_nhds.2
      intro i
      simpa [y] using
        (tendsto_const_nhds.sub
          (tendsto_one_div_add_atTop_nhds_zero_nat :
            Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1))
              atTop (𝓝 0)))
    have hfy_tendsto : Tendsto (fun n => f (y n)) atTop (𝓝 (f x)) :=
      f.continuous.continuousAt.tendsto.comp hy_tendsto
    exact le_of_tendsto' hfy_tendsto fun n => (hlow (y n) (hy_mem n)).le

  have hfx : f x = u :=
    le_antisymm hfx_le (hhigh x hx)

  have hcoord_nonneg : ∀ i, 0 ≤ f (coordinateVector i) := by
    intro i
    let v : ℕ → (ι → ℝ) :=
      fun n j =>
        coordinateVector i j
          + 1 / ((n : ℝ) + 1)
    have hv_pos : ∀ n j, 0 < v n j := by
      intro n j
      dsimp [v]
      have hsingle : 0 ≤ coordinateVector i j := by
        classical
        simp only [coordinateVector, Pi.single_apply]
        split <;> norm_num
      have hone : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      positivity
    have hxsub_mem :
        ∀ n, (fun j => x j - v n j) ∈ strictLowerOrthant x := by
      intro n j
      have := hv_pos n j
      dsimp only [strictLowerOrthant, Set.mem_setOf_eq]
      linarith
    have hv_tendsto :
        Tendsto v atTop (𝓝 (coordinateVector i)) := by
      apply tendsto_pi_nhds.2
      intro j
      simpa [v] using
        (tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat :
            Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1))
              atTop (𝓝 0)))
    have hfv_tendsto :
        Tendsto (fun n => f (v n)) atTop
          (𝓝 (f (coordinateVector i))) :=
      f.continuous.continuousAt.tendsto.comp hv_tendsto
    apply ge_of_tendsto' hfv_tendsto
    intro n
    have hsep :=
      (hlow (fun j => x j - v n j) (hxsub_mem n)).trans_le
        (hhigh x hx)
    have hmap :
        f (fun j => x j - v n j) = f x - f (v n) := by
      rw [← map_sub]
      rfl
    rw [hmap] at hsep
    linarith

  have hf_ne : f ≠ 0 := by
    intro hf
    obtain ⟨y, hy⟩ := strictLowerOrthant_nonempty x
    have := (hlow y hy).trans_le (hhigh x hx)
    simp [hf] at this

  refine ⟨f, hf_ne, hcoord_nonneg, ?_⟩
  intro y hy
  rw [hfx]
  exact hhigh y hy

/-- An undominated point of a convex finite-dimensional risk set is
Bayes for a nonzero nonnegative vector of prior weights. -/
theorem exists_nonnegative_supporting_weights
    {S : Set (ι → ℝ)} {x : ι → ℝ}
    (hS : Convex ℝ S) (hx : x ∈ S)
    (hno : ∀ y ∈ S, ¬ ∀ i, y i < x i) :
    ∃ w : ι → ℝ,
      (∀ i, 0 ≤ w i) ∧
      0 < ∑ i, w i ∧
      ∀ y ∈ S, (∑ i, w i * x i) ≤ ∑ i, w i * y i := by
  have hdisj : Disjoint (strictLowerOrthant x) S := by
    rw [Set.disjoint_left]
    intro y hyLower hyS
    exact hno y hyS hyLower
  obtain ⟨f, hf_ne, hw, hsupport⟩ :=
    exists_nonnegative_supporting_functional hS hx hdisj
  let w : ι → ℝ := fun i => f (coordinateVector i)
  have hsum_ne : ∑ i, w i ≠ 0 := by
    intro hzero
    have hwi : ∀ i, w i = 0 := by
      intro i
      have hall := Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_hj : j ∈ (Finset.univ : Finset ι)) => hw j)
      exact (hall.mp hzero) i (Finset.mem_univ i)
    apply hf_ne
    ext z
    rw [ContinuousLinearMap.zero_apply,
      continuousLinearMap_eq_sum_coordinates f z]
    simp [w, hwi]
  have hsum_pos : 0 < ∑ i, w i :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => hw i)
      (Ne.symm hsum_ne)
  refine ⟨w, hw, hsum_pos, ?_⟩
  intro y hy
  have hs := hsupport y hy
  rw [continuousLinearMap_eq_sum_coordinates,
    continuousLinearMap_eq_sum_coordinates] at hs
  simpa only [w] using hs

/-- Normalized form of `exists_nonnegative_supporting_weights`.
The resulting weights are an honest `NNReal` probability vector. -/
theorem exists_probability_supporting_weights
    {S : Set (ι → ℝ)} {x : ι → ℝ}
    (hS : Convex ℝ S) (hx : x ∈ S)
    (hno : ∀ y ∈ S, ¬ ∀ i, y i < x i) :
    ∃ w : ι → ℝ≥0,
      (∑ i, w i = 1) ∧
      ∀ y ∈ S,
        (∑ i, (w i : ℝ) * x i) ≤
          ∑ i, (w i : ℝ) * y i := by
  obtain ⟨v, hv_nonneg, hv_sum_pos, hv_support⟩ :=
    exists_nonnegative_supporting_weights hS hx hno
  let total : ℝ := ∑ i, v i
  let w : ι → ℝ≥0 :=
    fun i =>
      ⟨total⁻¹ * v i,
        mul_nonneg (inv_nonneg.mpr hv_sum_pos.le) (hv_nonneg i)⟩
  have htotal : total ≠ 0 := ne_of_gt hv_sum_pos
  have hw_coe (i : ι) :
      (w i : ℝ) = total⁻¹ * v i :=
    rfl
  have hw_sum_real : ∑ i, (w i : ℝ) = 1 := by
    simp_rw [hw_coe]
    rw [← Finset.mul_sum]
    rw [show (∑ i, v i) = total by rfl, inv_mul_cancel₀ htotal]
  have hw_sum : ∑ i, w i = 1 := by
    apply NNReal.eq
    simpa using hw_sum_real
  refine ⟨w, hw_sum, ?_⟩
  intro y hy
  have hs := hv_support y hy
  have hscale : 0 ≤ total⁻¹ := inv_nonneg.mpr hv_sum_pos.le
  have := mul_le_mul_of_nonneg_left hs hscale
  simp_rw [hw_coe]
  simpa only [mul_assoc, ← Finset.mul_sum] using this

end FiniteCompleteClass

end

end GraybillDeal
