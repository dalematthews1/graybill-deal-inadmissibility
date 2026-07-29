import GraybillDeal.UniversalHilbertStrictMidpoint

/-!
# Strong convergence from weak convergence and the anchor-risk bound

At the distinguished model measure, squared risk is a squared Hilbert-space
distance from the constant target.  Consequently, a weakly convergent
sequence whose anchor risks are all bounded by the limit's anchor risk
actually converges strongly in `L²`.

This is the Hilbert-space step which turns the weak compactness construction
into almost-everywhere convergence of a subsequence.
-/

namespace GraybillDeal

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X]
variable {μ : Measure X}

/-- Exact `ENNReal` form of the anchor risk/norm identity. -/
theorem weakLpSquaredRisk_self_eq_ofReal_norm_sub_const_sq
    [IsFiniteMeasure μ]
    (f : WeakSpace ℝ (Lp ℝ 2 μ)) (target : ℝ) :
    weakLpSquaredRisk μ target f
      =
    ENNReal.ofReal
      (‖(toWeakSpace ℝ (Lp ℝ 2 μ)).symm f
          - Lp.const 2 μ target‖ ^ 2) := by
  let g : Lp ℝ 2 μ :=
    (toWeakSpace ℝ (Lp ℝ 2 μ)).symm f
  let c : Lp ℝ 2 μ := Lp.const 2 μ target
  have hae :
      (fun x => (g x - target) ^ 2)
        =ᵐ[μ]
      (fun x => inner ℝ ((g - c) x) ((g - c) x)) := by
    filter_upwards
      [Lp.coeFn_sub g c,
        Lp.coeFn_const (p := (2 : ℝ≥0∞)) (μ := μ) (c := target)]
      with x hsub hconst
    rw [hsub]
    change
      (g x - target) ^ 2
        =
      inner ℝ (g x - c x) (g x - c x)
    rw [hconst]
    simp [pow_two]
  have hint :
      Integrable (fun x => (g x - target) ^ 2) μ :=
    (L2.integrable_inner (g - c) (g - c)).congr hae.symm
  calc
    weakLpSquaredRisk μ target f
        =
      ∫⁻ x, ENNReal.ofReal ((g x - target) ^ 2) ∂μ := rfl
    _ =
      ENNReal.ofReal (∫ x, (g x - target) ^ 2 ∂μ) := by
        exact
          (ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
    _ =
      ENNReal.ofReal
        (‖g - Lp.const 2 μ target‖ ^ 2) := by
        rw [integral_sq_sub_eq_norm_sub_const_sq]

/-- Evaluation against a fixed Hilbert vector is continuous for the weak
topology. -/
theorem tendsto_inner_symm_of_tendsto_weak
    (b : ℕ → WeakSpace ℝ (Lp ℝ 2 μ))
    (d₀ : WeakSpace ℝ (Lp ℝ 2 μ))
    (u : Lp ℝ 2 μ)
    (hb : Tendsto b atTop (𝓝 d₀)) :
    Tendsto
      (fun n =>
        inner ℝ u
          ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm (b n)))
      atTop
      (𝓝
        (inner ℝ u
          ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm d₀))) := by
  let φ : StrongDual ℝ (Lp ℝ 2 μ) :=
    InnerProductSpace.toDual ℝ (Lp ℝ 2 μ) u
  have hcont :
      Continuous
        (fun z : WeakSpace ℝ (Lp ℝ 2 μ) =>
          φ ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm z)) :=
    WeakBilin.eval_continuous
      (topDualPairing ℝ (Lp ℝ 2 μ)).flip φ
  have ht := hcont.continuousAt.tendsto.comp hb
  change Tendsto
    (fun n => φ ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm (b n)))
    atTop
    (𝓝
      (φ ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm d₀))) at ht
  simpa only
      [φ, InnerProductSpace.toDual_apply_apply] using ht

/-- Weak convergence plus an upper anchor-risk bound gives strong `L²`
convergence. -/
theorem tendsto_strong_of_tendsto_weak_of_anchorRisk_le
    [IsFiniteMeasure μ]
    (b : ℕ → WeakSpace ℝ (Lp ℝ 2 μ))
    (d₀ : WeakSpace ℝ (Lp ℝ 2 μ))
    (target : ℝ)
    (hb : Tendsto b atTop (𝓝 d₀))
    (hrisk : ∀ n,
      weakLpSquaredRisk μ target (b n)
        ≤ weakLpSquaredRisk μ target d₀) :
    Tendsto
      (fun n => (toWeakSpace ℝ (Lp ℝ 2 μ)).symm (b n))
      atTop
      (𝓝
        ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm d₀)) := by
  let f : ℕ → Lp ℝ 2 μ :=
    fun n => (toWeakSpace ℝ (Lp ℝ 2 μ)).symm (b n)
  let f₀ : Lp ℝ 2 μ :=
    (toWeakSpace ℝ (Lp ℝ 2 μ)).symm d₀
  let c : Lp ℝ 2 μ := Lp.const 2 μ target
  let u : ℕ → Lp ℝ 2 μ := fun n => f n - c
  let u₀ : Lp ℝ 2 μ := f₀ - c
  have hnormsq (n : ℕ) : ‖u n‖ ^ 2 ≤ ‖u₀‖ ^ 2 := by
    have h := hrisk n
    rw [weakLpSquaredRisk_self_eq_ofReal_norm_sub_const_sq,
      weakLpSquaredRisk_self_eq_ofReal_norm_sub_const_sq] at h
    have h' :
        ‖(toWeakSpace ℝ (Lp ℝ 2 μ)).symm (b n)
            - Lp.const 2 μ target‖ ^ 2
          ≤
        ‖(toWeakSpace ℝ (Lp ℝ 2 μ)).symm d₀
            - Lp.const 2 μ target‖ ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff
        (sq_nonneg
          ‖(toWeakSpace ℝ (Lp ℝ 2 μ)).symm d₀
              - Lp.const 2 μ target‖)).mp h
    simpa only [u, u₀, f, f₀, c] using h'
  have hinner :
      Tendsto
        (fun n => inner ℝ u₀ (u n))
        atTop
        (𝓝 (inner ℝ u₀ u₀)) := by
    have hc :
        Tendsto
          (fun _ : ℕ => inner ℝ u₀ c)
          atTop
          (𝓝 (inner ℝ u₀ c)) :=
      tendsto_const_nhds
    have h :=
      (tendsto_inner_symm_of_tendsto_weak b d₀ u₀ hb).sub hc
    simpa only [u, u₀, f, f₀, c, inner_sub_right] using h
  have hupper :
      Tendsto
        (fun n =>
          2 * (‖u₀‖ ^ 2 - inner ℝ u₀ (u n)))
        atTop
        (𝓝 0) := by
    have hconst :
        Tendsto
          (fun _ : ℕ => ‖u₀‖ ^ 2)
          atTop
          (𝓝 (‖u₀‖ ^ 2)) :=
      tendsto_const_nhds
    have h :=
      (hconst.sub hinner).const_mul (2 : ℝ)
    simpa only
        [real_inner_self_eq_norm_sq, sub_self, mul_zero] using h
  have hdist (n : ℕ) :
      ‖u n - u₀‖ ^ 2
        ≤
      2 * (‖u₀‖ ^ 2 - inner ℝ u₀ (u n)) := by
    rw [norm_sub_sq_real]
    rw [real_inner_comm (u n) u₀]
    nlinarith [hnormsq n]
  have hdistSq :
      Tendsto
        (fun n => ‖u n - u₀‖ ^ 2)
        atTop
        (𝓝 0) :=
    squeeze_zero
      (fun n => sq_nonneg ‖u n - u₀‖)
      hdist
      hupper
  have hnorm :
      Tendsto
        (fun n => ‖u n - u₀‖)
        atTop
        (𝓝 0) := by
    have hsqrt :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hdistSq
    change
      Tendsto
        (fun n => Real.sqrt (‖u n - u₀‖ ^ 2))
        atTop
        (𝓝 (Real.sqrt 0)) at hsqrt
    simpa only
        [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  have hzero :
      Tendsto
        (fun n => u n - u₀)
        atTop
        (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hsub :
      Tendsto
        (fun n => f n - f₀)
        atTop
        (𝓝 0) := by
    simpa only [u, u₀, sub_sub_sub_cancel_right] using hzero
  have hadd :=
    hsub.add
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => f₀) atTop (𝓝 f₀))
  simpa only [sub_add_cancel, zero_add, f, f₀] using hadd

end

end GraybillDeal
