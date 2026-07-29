import GraybillDeal.UniversalReducedDensity
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Defs.Induced

/-!
# Regularity of the universal reduced reference measure

The universal complete-class argument is carried out on

`UniversalReducedObservation = (0,1) × (0,∞)`.

This file verifies that the canonical Lebesgue measure on that open
subspace, and the measure obtained after absorbing the strictly positive
observation factor, have the two properties used downstream:

* sigma-finiteness;
* strictly positive mass on every nonempty open set.

Thus these conditions need not be left as hypotheses when the abstract
complete-class result is specialized to the universal reduced experiment.
-/

namespace GraybillDeal

open MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

/-- The set underlying the universal reduced observation subtype is open
in `ℝ × ℝ`. -/
theorem universalReducedObservation_set_isOpen :
    IsOpen {x : ℝ × ℝ | 0 < x.1 ∧ x.1 < 1 ∧ 0 < x.2} := by
  exact
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt continuous_const continuous_snd))

/-- The subtype inclusion of the reduced observation space is an open
embedding. -/
theorem universalReducedObservation_isOpenEmbedding :
    IsOpenEmbedding
      (Subtype.val : UniversalReducedObservation → ℝ × ℝ) :=
  universalReducedObservation_set_isOpen.isOpenEmbedding_subtypeVal

noncomputable instance universalReducedObservation_locallyCompact :
    LocallyCompactSpace UniversalReducedObservation :=
  universalReducedObservation_isOpenEmbedding.locallyCompactSpace

noncomputable instance
    universalReducedLebesgueMeasure_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts universalReducedLebesgueMeasure := by
  unfold universalReducedLebesgueMeasure
  exact
    IsFiniteMeasureOnCompacts.comap'
      (volume : Measure (ℝ × ℝ))
      continuous_subtype_val
      universalReducedObservation_isOpenEmbedding.measurableEmbedding

noncomputable instance
    universalReducedLebesgueMeasure_isLocallyFinite :
    IsLocallyFiniteMeasure universalReducedLebesgueMeasure :=
  inferInstance

noncomputable instance universalReducedLebesgueMeasure_sigmaFinite :
    SigmaFinite universalReducedLebesgueMeasure :=
  inferInstance

noncomputable instance universalReducedLebesgueMeasure_openPos :
    Measure.IsOpenPosMeasure universalReducedLebesgueMeasure := by
  unfold universalReducedLebesgueMeasure
  exact
    Measure.IsOpenPosMeasure.comap
      (volume : Measure (ℝ × ℝ))
      universalReducedObservation_isOpenEmbedding

theorem universalReducedLebesgueMeasure_open_pos
    (U : Set UniversalReducedObservation)
    (hU : IsOpen U) (hne : U.Nonempty) :
    0 < universalReducedLebesgueMeasure U :=
  hU.measure_pos universalReducedLebesgueMeasure hne

noncomputable instance universalReducedObservationReference_sigmaFinite
    (a b : ℝ) :
    SigmaFinite
      (universalReducedObservationReference
        universalReducedLebesgueMeasure a b) := by
  unfold universalReducedObservationReference
  infer_instance

/-- A strictly positive density has the same null sets as the underlying
Lebesgue reference measure. -/
theorem universalReducedLebesgue_absolutelyContinuous_reference
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    universalReducedLebesgueMeasure ≪
      universalReducedObservationReference
        universalReducedLebesgueMeasure a b := by
  intro s hs
  rw [measure_eq_zero_iff_ae_notMem] at hs ⊢
  exact
    (ae_universalReducedObservationReference_iff
      ha hb universalReducedLebesgueMeasure
      (fun x => x ∉ s)).mp hs

noncomputable instance universalReducedObservationReference_openPos
    (a b : ℝ) [Fact (0 < a)] [Fact (0 < b)] :
    Measure.IsOpenPosMeasure
      (universalReducedObservationReference
        universalReducedLebesgueMeasure a b) :=
  (universalReducedLebesgue_absolutelyContinuous_reference
    (a := a) (b := b) (Fact.out) (Fact.out)).isOpenPosMeasure

theorem universalReducedObservationReference_open_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (U : Set UniversalReducedObservation)
    (hU : IsOpen U) (hne : U.Nonempty) :
    0 <
      universalReducedObservationReference
        universalReducedLebesgueMeasure a b U := by
  letI : Fact (0 < a) := ⟨ha⟩
  letI : Fact (0 < b) := ⟨hb⟩
  exact
    hU.measure_pos
      (universalReducedObservationReference
        universalReducedLebesgueMeasure a b)
      hne

end

end GraybillDeal
