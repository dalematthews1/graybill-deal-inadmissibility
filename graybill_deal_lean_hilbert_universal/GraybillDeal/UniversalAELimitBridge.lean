import GraybillDeal.UniversalEndpointReweighting
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# From an almost-everywhere limiting Bayes identity to an everywhere identity

The legal observation coordinates are `0 < r < 1` and `0 ≤ q`.  For a
fixed probability measure on the compactified parameter interval, both
the universal posterior action and the baseline action `r` are continuous
on this observation space.

Consequently, if a reference measure charges every nonempty open set,
almost-everywhere equality of these two actions upgrades to equality
everywhere.  Combining this fact with endpoint reweighting and compactness
of probability measures gives the posterior identity required by the
universal argument.
-/

namespace GraybillDeal

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- Legal values of the reduced mean coordinate. -/
abbrev UniversalObservationR := Set.Ioo (0 : ℝ) 1

/-- Legal values of the nonnegative ancillary coordinate. -/
abbrev UniversalObservationQ := Set.Ici (0 : ℝ)

/-- The legal reduced observation space `(r,q)`. -/
abbrev UniversalObservation :=
  UniversalObservationR × UniversalObservationQ

instance universalObservationRLocallyCompact :
    LocallyCompactSpace UniversalObservationR :=
  isOpen_Ioo.isLocallyClosed.locallyCompactSpace

instance universalObservationQLocallyCompact :
    LocallyCompactSpace UniversalObservationQ :=
  isClosed_Ici.isLocallyClosed.locallyCompactSpace

/-- The `r` coordinate of a legal observation. -/
def universalObservation_r (z : UniversalObservation) : ℝ :=
  z.1.1

/-- The `q` coordinate of a legal observation. -/
def universalObservation_q (z : UniversalObservation) : ℝ :=
  z.2.1

@[simp]
theorem universalObservation_r_pos (z : UniversalObservation) :
    0 < universalObservation_r z :=
  z.1.2.1

@[simp]
theorem universalObservation_r_lt_one (z : UniversalObservation) :
    universalObservation_r z < 1 :=
  z.1.2.2

@[simp]
theorem universalObservation_q_nonneg (z : UniversalObservation) :
    0 ≤ universalObservation_q z :=
  z.2.2

theorem continuous_universalObservation_r :
    Continuous universalObservation_r := by
  unfold universalObservation_r
  fun_prop

theorem continuous_universalObservation_q :
    Continuous universalObservation_q := by
  unfold universalObservation_q
  fun_prop

theorem continuous_universalKernel_observation_theta
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous
      (fun zθ : UniversalObservation × UniversalTheta =>
        universalKernel a b
          (universalObservation_r zθ.1)
          (universalObservation_q zθ.1)
          zθ.2) := by
  unfold universalKernel
  have hB :
      Continuous
        (fun zθ : UniversalObservation × UniversalTheta =>
          universalB a b
            (universalObservation_r zθ.1)
            (universalObservation_q zθ.1)
            zθ.2) := by
    unfold universalB universalObservation_r universalObservation_q
    fun_prop
  exact hB.rpow_const (fun zθ =>
    Or.inl (ne_of_gt
      (universalB_pos ha hb
        (universalObservation_r_pos zθ.1)
        (universalObservation_r_lt_one zθ.1)
        (universalObservation_q_nonneg zθ.1)
        zθ.2)))

theorem continuous_universalNumeratorKernel_observation_theta
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous
      (fun zθ : UniversalObservation × UniversalTheta =>
        (zθ.2 : ℝ) *
          universalKernel a b
            (universalObservation_r zθ.1)
            (universalObservation_q zθ.1)
            zθ.2) := by
  exact (continuous_subtype_val.comp continuous_snd).mul
    (continuous_universalKernel_observation_theta ha hb)

theorem continuous_universalPosteriorDenominator_observation
    (ν : ProbabilityMeasure UniversalTheta)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous
      (fun z : UniversalObservation =>
        universalPosteriorDenominator
          (ν : Measure UniversalTheta) a b
          (universalObservation_r z)
          (universalObservation_q z)) := by
  have h :=
    continuous_parametric_integral_of_continuous
      (μ := (ν : Measure UniversalTheta))
      (f := fun z : UniversalObservation =>
        fun θ : UniversalTheta =>
          universalKernel a b
            (universalObservation_r z)
            (universalObservation_q z) θ)
      (continuous_universalKernel_observation_theta ha hb)
      (s := Set.univ) isCompact_univ
  simpa [universalPosteriorDenominator] using h

theorem continuous_universalPosteriorNumerator_observation
    (ν : ProbabilityMeasure UniversalTheta)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous
      (fun z : UniversalObservation =>
        universalPosteriorNumerator
          (ν : Measure UniversalTheta) a b
          (universalObservation_r z)
          (universalObservation_q z)) := by
  have h :=
    continuous_parametric_integral_of_continuous
      (μ := (ν : Measure UniversalTheta))
      (f := fun z : UniversalObservation =>
        fun θ : UniversalTheta =>
          (θ : ℝ) *
            universalKernel a b
              (universalObservation_r z)
              (universalObservation_q z) θ)
      (continuous_universalNumeratorKernel_observation_theta ha hb)
      (s := Set.univ) isCompact_univ
  simpa [universalPosteriorNumerator] using h

/-- The limiting posterior action is continuous throughout the legal
observation space. -/
theorem continuous_universalPosteriorAction_observation
    (ν : ProbabilityMeasure UniversalTheta)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous
      (fun z : UniversalObservation =>
        universalPosteriorAction
          (ν : Measure UniversalTheta) a b
          (universalObservation_r z)
          (universalObservation_q z)) := by
  unfold universalPosteriorAction
  exact
    (continuous_universalPosteriorNumerator_observation ν ha hb).div
      (continuous_universalPosteriorDenominator_observation ν ha hb)
      (fun z =>
        ne_of_gt
          (universalPosteriorDenominator_pos
            (ν : Measure UniversalTheta) ha hb
            (universalObservation_r_pos z)
            (universalObservation_r_lt_one z)
            (universalObservation_q_nonneg z)))

/-- A version of the continuous a.e.-equality theorem with positivity on
nonempty open sets supplied as an ordinary hypothesis rather than a
typeclass. -/
theorem continuous_eq_of_ae_eq_of_open_pos
    {ρ : Measure UniversalObservation}
    {f g : UniversalObservation → ℝ}
    (hopen :
      ∀ U : Set UniversalObservation,
        IsOpen U → U.Nonempty → 0 < ρ U)
    (hae : f =ᵐ[ρ] g)
    (hf : Continuous f) (hg : Continuous g) :
    f = g := by
  letI : ρ.IsOpenPosMeasure :=
    ⟨fun U hU hUne => ne_of_gt (hopen U hU hUne)⟩
  exact Measure.eq_of_ae_eq hae hf hg

/-- Endpoint reweighting, weak compactness, and an almost-everywhere
finite-prior limit produce one probability measure satisfying the
universal posterior identity at every legal observation. -/
theorem exists_universalPosteriorIdentity_of_ae_finitePrior_tendsto
    (πs : ℕ → UniversalInteriorFinitePrior)
    (ρ : Measure UniversalObservation)
    {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hopen :
      ∀ U : Set UniversalObservation,
        IsOpen U → U.Nonempty → 0 < ρ U)
    (haction :
      ∀ᵐ z ∂ρ,
        Tendsto
          (fun n =>
            (πs n).fullReducedPosteriorAction a b
              (universalObservation_r z)
              (universalObservation_q z))
          atTop (𝓝 (universalObservation_r z))) :
    ∃ ν : ProbabilityMeasure UniversalTheta,
      UniversalPosteriorIdentity
        (ν : Measure UniversalTheta) a b := by
  let τs : ℕ → UniversalFinitePrior :=
    fun n => (πs n).endpointReweightedPrior a b
  obtain ⟨ν, φ, hφ, hν⟩ :=
    exists_universalFinitePrior_tendsto_subseq τs
  have hae_identity :
      (fun z : UniversalObservation =>
        universalPosteriorAction
          (ν : Measure UniversalTheta) a b
          (universalObservation_r z)
          (universalObservation_q z))
        =ᵐ[ρ]
      (fun z : UniversalObservation => universalObservation_r z) := by
    filter_upwards [haction] with z hz
    apply universalPosteriorAction_eq_of_finitePrior_tendsto
      hν ha hb
      (universalObservation_r_pos z)
      (universalObservation_r_lt_one z)
      (universalObservation_q_nonneg z)
    have hz_sub :=
      hz.comp hφ.tendsto_atTop
    exact hz_sub.congr'
      (Eventually.of_forall fun j =>
        (UniversalInteriorFinitePrior.fullReducedPosteriorAction_eq_reweighted
          (πs (φ j)) ha hb
          (universalObservation_r_pos z)
          (universalObservation_r_lt_one z)
          (universalObservation_q_nonneg z)))
  have hfun :
      (fun z : UniversalObservation =>
        universalPosteriorAction
          (ν : Measure UniversalTheta) a b
          (universalObservation_r z)
          (universalObservation_q z))
        =
      (fun z : UniversalObservation => universalObservation_r z) :=
    continuous_eq_of_ae_eq_of_open_pos
      hopen hae_identity
      (continuous_universalPosteriorAction_observation ν ha hb)
      continuous_universalObservation_r
  refine ⟨ν, ?_⟩
  constructor
  intro r q hr0 hr1 hq
  let z : UniversalObservation :=
    (⟨r, hr0, hr1⟩, ⟨q, hq⟩)
  exact congrFun hfun z

end

end GraybillDeal
