import GraybillDeal.UniversalReferenceMeasure
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Extending reduced rules to total raw-coordinate rules

Decision theory naturally returns a measurable rule on the genuine
observation space `(0,1) × (0,∞)`.  The raw estimator is more convenient
to state using a total function on `ℝ × ℝ`.  Since the genuine observation
space is a measurable embedded subtype, every measurable reduced rule has
a measurable total extension.
-/

namespace GraybillDeal

open MeasureTheory Set Topology

noncomputable section

theorem universalReducedObservation_measurableEmbedding :
    MeasurableEmbedding
      (Subtype.val : UniversalReducedObservation → ℝ × ℝ) :=
  universalReducedObservation_isOpenEmbedding.measurableEmbedding

/-- Every measurable rule on the open reduced observation subtype has a
measurable total extension to `ℝ × ℝ`. -/
theorem exists_measurable_universalReducedRule_extension
    {δ : UniversalReducedObservation → ℝ}
    (hδ : Measurable δ) :
    ∃ δ' : ℝ × ℝ → ℝ,
      Measurable δ' ∧
      ∀ x : UniversalReducedObservation, δ' x.1 = δ x := by
  obtain ⟨δ', hδ', heq⟩ :=
    universalReducedObservation_measurableEmbedding
      |>.exists_measurable_extend hδ (fun _ => ⟨(0 : ℝ)⟩)
  refine ⟨δ', hδ', ?_⟩
  intro x
  exact congr_fun heq x

/-- Functional form of the extension identity. -/
theorem exists_measurable_universalReducedRule_extension_comp
    {δ : UniversalReducedObservation → ℝ}
    (hδ : Measurable δ) :
    ∃ δ' : ℝ × ℝ → ℝ,
      Measurable δ' ∧
      δ' ∘ (Subtype.val : UniversalReducedObservation → ℝ × ℝ) = δ := by
  obtain ⟨δ', hδ', heq⟩ :=
    universalReducedObservation_measurableEmbedding
      |>.exists_measurable_extend hδ (fun _ => ⟨(0 : ℝ)⟩)
  exact ⟨δ', hδ', heq⟩

end

end GraybillDeal
