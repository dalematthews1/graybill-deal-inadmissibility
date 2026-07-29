import GraybillDeal.UniversalAELimitBridge
import GraybillDeal.UniversalReducedExperiment
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The limiting-Bayes bridge from the genuine open sample space

The complete-class theorem is applied on

`UniversalReducedObservation = (0,1) × (0,∞)`.

The analytic contradiction, however, uses the continuous extension to
`q = 0`.  This module closes that small but logically important interface
gap.  It first upgrades almost-everywhere convergence on the genuine open
sample space to pointwise equality there.  It then lets
`q_n = 1 / (n+1) ↓ 0` and uses continuity of the limiting posterior action.

No mass at the artificial boundary `q = 0` is assumed.
-/

namespace GraybillDeal

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- Include a genuine reduced observation (`q > 0`) into the observation
space on which the limiting posterior action also permits `q = 0`. -/
def universalReducedObservationToObservation
    (x : UniversalReducedObservation) : UniversalObservation :=
  (⟨x.r, x.r_pos, x.r_lt_one⟩, ⟨x.q, x.q_nonneg⟩)

@[simp]
theorem universalReducedObservationToObservation_r
    (x : UniversalReducedObservation) :
    universalObservation_r
        (universalReducedObservationToObservation x) = x.r :=
  rfl

@[simp]
theorem universalReducedObservationToObservation_q
    (x : UniversalReducedObservation) :
    universalObservation_q
        (universalReducedObservationToObservation x) = x.q :=
  rfl

theorem continuous_universalReducedObservationToObservation :
    Continuous universalReducedObservationToObservation := by
  unfold universalReducedObservationToObservation
    UniversalReducedObservation.r UniversalReducedObservation.q
  fun_prop

theorem continuous_universalReducedObservation_r :
    Continuous (fun x : UniversalReducedObservation => x.r) := by
  unfold UniversalReducedObservation.r
  fun_prop

/-- The limiting posterior action is continuous on the genuine open
reduced sample space. -/
theorem continuous_universalPosteriorAction_reducedObservation
    (ν : ProbabilityMeasure UniversalTheta)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous
      (fun x : UniversalReducedObservation =>
        universalPosteriorAction
          (ν : Measure UniversalTheta) a b x.r x.q) := by
  change Continuous
    ((fun z : UniversalObservation =>
        universalPosteriorAction
          (ν : Measure UniversalTheta) a b
          (universalObservation_r z)
          (universalObservation_q z))
      ∘ universalReducedObservationToObservation)
  exact
    (continuous_universalPosteriorAction_observation ν ha hb).comp
      continuous_universalReducedObservationToObservation

/-- Continuous real functions which agree almost everywhere under a measure
charging every nonempty open set agree everywhere.  This is the open
sample-space counterpart of the corresponding lemma in
`UniversalAELimitBridge`. -/
theorem continuous_eq_of_ae_eq_of_open_pos_reduced
    {ρ : Measure UniversalReducedObservation}
    {f g : UniversalReducedObservation → ℝ}
    (hopen :
      ∀ U : Set UniversalReducedObservation,
        IsOpen U → U.Nonempty → 0 < ρ U)
    (hae : f =ᵐ[ρ] g)
    (hf : Continuous f) (hg : Continuous g) :
    f = g := by
  letI : ρ.IsOpenPosMeasure :=
    ⟨fun U hU hUne => ne_of_gt (hopen U hU hUne)⟩
  exact Measure.eq_of_ae_eq hae hf hg

/-- Endpoint reweighting and weak compactness, starting from convergence
only on the genuine open sample space, produce the universal posterior
identity including its boundary value at `q = 0`. -/
theorem exists_universalPosteriorIdentity_of_reduced_ae_finitePrior_tendsto
    (πs : ℕ → UniversalInteriorFinitePrior)
    (ρ : Measure UniversalReducedObservation)
    {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hopen :
      ∀ U : Set UniversalReducedObservation,
        IsOpen U → U.Nonempty → 0 < ρ U)
    (haction :
      ∀ᵐ x ∂ρ,
        Tendsto
          (fun n =>
            (πs n).fullReducedPosteriorAction a b x.r x.q)
          atTop (𝓝 x.r)) :
    ∃ ν : ProbabilityMeasure UniversalTheta,
      UniversalPosteriorIdentity
        (ν : Measure UniversalTheta) a b := by
  let τs : ℕ → UniversalFinitePrior :=
    fun n => (πs n).endpointReweightedPrior a b
  obtain ⟨ν, φ, hφ, hν⟩ :=
    exists_universalFinitePrior_tendsto_subseq τs
  have hae_identity :
      (fun x : UniversalReducedObservation =>
        universalPosteriorAction
          (ν : Measure UniversalTheta) a b x.r x.q)
        =ᵐ[ρ]
      (fun x : UniversalReducedObservation => x.r) := by
    filter_upwards [haction] with x hx
    apply universalPosteriorAction_eq_of_finitePrior_tendsto
      hν ha hb x.r_pos x.r_lt_one x.q_nonneg
    have hx_sub := hx.comp hφ.tendsto_atTop
    exact hx_sub.congr'
      (Eventually.of_forall fun j =>
        (UniversalInteriorFinitePrior.fullReducedPosteriorAction_eq_reweighted
          (πs (φ j)) ha hb
          x.r_pos x.r_lt_one x.q_nonneg))
  have hfun :
      (fun x : UniversalReducedObservation =>
        universalPosteriorAction
          (ν : Measure UniversalTheta) a b x.r x.q)
        =
      (fun x : UniversalReducedObservation => x.r) :=
    continuous_eq_of_ae_eq_of_open_pos_reduced
      hopen hae_identity
      (continuous_universalPosteriorAction_reducedObservation ν ha hb)
      continuous_universalReducedObservation_r
  refine ⟨ν, ?_⟩
  constructor
  intro r q hr0 hr1 hq
  by_cases hq0 : q = 0
  · subst q
    let rsub : UniversalObservationR := ⟨r, hr0, hr1⟩
    let qseq : ℕ → UniversalObservationQ :=
      fun n => ⟨1 / ((n : ℝ) + 1), by
        change 0 ≤ 1 / ((n : ℝ) + 1)
        positivity⟩
    let qzero : UniversalObservationQ := ⟨0, by simp⟩
    have hqseq :
        Tendsto qseq atTop (𝓝 qzero) := by
      apply tendsto_subtype_rng.mpr
      simpa only [qseq, qzero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hcontinuous :
        Continuous
          (fun q' : UniversalObservationQ =>
            universalPosteriorAction
              (ν : Measure UniversalTheta) a b r (q' : ℝ)) := by
      have hmap :
          Continuous
            (fun q' : UniversalObservationQ =>
              ((rsub, q') : UniversalObservation)) := by
        fun_prop
      change Continuous
        ((fun z : UniversalObservation =>
            universalPosteriorAction
              (ν : Measure UniversalTheta) a b
              (universalObservation_r z)
              (universalObservation_q z))
          ∘ fun q' : UniversalObservationQ =>
              ((rsub, q') : UniversalObservation))
      exact
        (continuous_universalPosteriorAction_observation ν ha hb).comp hmap
    have hlimit :
        Tendsto
          (fun n =>
            universalPosteriorAction
              (ν : Measure UniversalTheta) a b r (qseq n : ℝ))
          atTop
          (𝓝
            (universalPosteriorAction
              (ν : Measure UniversalTheta) a b r 0)) := by
      change Tendsto
        ((fun q' : UniversalObservationQ =>
            universalPosteriorAction
              (ν : Measure UniversalTheta) a b r (q' : ℝ))
          ∘ qseq)
        atTop
        (𝓝
          (universalPosteriorAction
            (ν : Measure UniversalTheta) a b r (qzero : ℝ)))
      exact hcontinuous.continuousAt.tendsto.comp hqseq
    have heq :
        ∀ n,
          universalPosteriorAction
              (ν : Measure UniversalTheta) a b r (qseq n : ℝ)
            = r := by
      intro n
      let x : UniversalReducedObservation :=
        ⟨(r, (qseq n : ℝ)), hr0, hr1, by
          dsimp only [qseq]
          positivity⟩
      simpa only [x, UniversalReducedObservation.r,
        UniversalReducedObservation.q] using congrFun hfun x
    have hlimit_r :
        Tendsto
          (fun n =>
            universalPosteriorAction
              (ν : Measure UniversalTheta) a b r (qseq n : ℝ))
          atTop (𝓝 r) :=
      tendsto_const_nhds.congr'
        (Eventually.of_forall fun n => (heq n).symm)
    exact tendsto_nhds_unique hlimit hlimit_r
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    let x : UniversalReducedObservation :=
      ⟨(r, q), hr0, hr1, hqpos⟩
    simpa only [x, UniversalReducedObservation.r,
      UniversalReducedObservation.q] using congrFun hfun x

end

end GraybillDeal
