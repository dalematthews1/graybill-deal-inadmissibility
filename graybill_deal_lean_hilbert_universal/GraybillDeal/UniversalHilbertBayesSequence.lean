import GraybillDeal.UniversalHilbertAdmissibleIdentification
import Mathlib.Topology.Sequences

/-!
# Sequential extraction from the finite-Bayes witness closure

The clipped weak `L²` action set is compact and metrizable.  Therefore,
membership in the weak closure of the finite-Bayes witness set supplies
an actual sequence of witnesses.  Because the witness-set definition
retains the existential prior, classical choice then selects a matching
positive finite prior at every index.
-/

namespace GraybillDeal

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

noncomputable section

/-- A weakly convergent sequence can be selected from the canonical
finite-Bayes witness set. -/
theorem exists_sequence_in_universalHilbertFiniteBayesWitnessSet
    {ν₁ ν₂ : ℕ}
    [IsFiniteMeasure
      (universalHilbertProbabilityMeasure ν₁ ν₂)]
    (d₀ :
      WeakSpace ℝ
        (Lp ℝ 2
          (universalHilbertProbabilityMeasure ν₁ ν₂)))
    (hd₀ :
      d₀ ∈ closure
        (universalHilbertFiniteBayesWitnessSet ν₁ ν₂ d₀)) :
    ∃ b : ℕ →
        WeakSpace ℝ
          (Lp ℝ 2
            (universalHilbertProbabilityMeasure ν₁ ν₂)),
      (∀ n, b n ∈
        universalHilbertFiniteBayesWitnessSet ν₁ ν₂ d₀) ∧
      Tendsto b atTop (𝓝 d₀) := by
  let μ := universalHilbertProbabilityMeasure ν₁ ν₂
  let K : Set (WeakSpace ℝ (Lp ℝ 2 μ)) :=
    weakHilbertActionSet μ
  let B : Set (WeakSpace ℝ (Lp ℝ 2 μ)) :=
    universalHilbertFiniteBayesWitnessSet ν₁ ν₂ d₀
  have hBK : B ⊆ K :=
    universalHilbertFiniteBayesWitnessSet_subset_action ν₁ ν₂ d₀
  have hd₀K : d₀ ∈ K :=
    (closure_minimal hBK
      (isClosed_weakHilbertActionSet μ)) hd₀
  let dK : K := ⟨d₀, hd₀K⟩
  let BK : Set K :=
    {d | (d : WeakSpace ℝ (Lp ℝ 2 μ)) ∈ B}
  have himage :
      ((fun d : K =>
        (d : WeakSpace ℝ (Lp ℝ 2 μ))) '' BK) = B := by
    ext d
    constructor
    · rintro ⟨e, he, rfl⟩
      exact he
    · intro hd
      exact ⟨⟨d, hBK hd⟩, hd, rfl⟩
  have hdKclosure : dK ∈ closure BK := by
    rw [closure_subtype, himage]
    exact hd₀
  letI : TopologicalSpace.MetrizableSpace K :=
    metrizable_weakHilbertActionSet μ
  obtain ⟨u, huB, hu⟩ :=
    mem_closure_iff_seq_limit.mp hdKclosure
  refine
    ⟨fun n => (u n : WeakSpace ℝ (Lp ℝ 2 μ)), ?_, ?_⟩
  · intro n
    exact huB n
  · exact tendsto_subtype_rng.mp hu

/-- Select both a weakly convergent witness sequence and the positive
finite prior representing each term. -/
theorem exists_sequence_with_selected_universalFinitePriors
    {ν₁ ν₂ : ℕ}
    [IsFiniteMeasure
      (universalHilbertProbabilityMeasure ν₁ ν₂)]
    (d₀ :
      WeakSpace ℝ
        (Lp ℝ 2
          (universalHilbertProbabilityMeasure ν₁ ν₂)))
    (hd₀ :
      d₀ ∈ closure
        (universalHilbertFiniteBayesWitnessSet ν₁ ν₂ d₀)) :
    ∃ (b : ℕ →
          WeakSpace ℝ
            (Lp ℝ 2
              (universalHilbertProbabilityMeasure ν₁ ν₂)))
        (π : ℕ → PositiveFinitePrior UniversalInteriorTheta),
      Tendsto b atTop (𝓝 d₀) ∧
      ∀ n,
        b n ∈ universalHilbertFiniteBayesWitnessSet ν₁ ν₂ d₀ ∧
        (fun x =>
          ((toWeakSpace ℝ
              (Lp ℝ 2
                (universalHilbertProbabilityMeasure ν₁ ν₂))).symm
            (b n)) x)
          =ᵐ[universalHilbertDominatingMeasure ν₁ ν₂]
        (π n).bayesAction
          (universalReducedLikelihood
            ((ν₁ : ℝ) / 2) ((ν₂ : ℝ) / 2))
          (fun θ : UniversalInteriorTheta => (θ : ℝ)) := by
  obtain ⟨b, hbB, hb⟩ :=
    exists_sequence_in_universalHilbertFiniteBayesWitnessSet d₀ hd₀
  let π : ℕ → PositiveFinitePrior UniversalInteriorTheta :=
    fun n => Classical.choose (hbB n).2.2
  refine ⟨b, π, hb, ?_⟩
  intro n
  exact ⟨hbB n, Classical.choose_spec (hbB n).2.2⟩

end

end GraybillDeal
