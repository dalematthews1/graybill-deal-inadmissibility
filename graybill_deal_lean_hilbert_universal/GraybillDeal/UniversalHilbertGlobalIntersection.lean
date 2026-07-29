import GraybillDeal.UniversalHilbertRisk

/-!
# Global weak-risk bounds from finite intersections

This file packages the compact finite-intersection step used by the
Hilbert-space complete-class argument.

Let `B` be any family of clipped weak `L²` rules.  Its weak closure is
compact because it is contained in the weakly compact clipped action set.
For each parameter, the corresponding squared-risk sublevel is weakly
closed.  Consequently, if `closure B` meets every finite collection of
the prescribed risk sublevels, then it meets all of them simultaneously.
-/

namespace GraybillDeal

open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

variable {X ι : Type*} [MeasurableSpace X]
variable {μ : Measure X} [IsFiniteMeasure μ]

/-- The weak closure of any subset of the clipped Hilbert action set is
compact. -/
theorem isCompact_closure_of_subset_weakHilbertActionSet
    (B : Set (WeakSpace ℝ (Lp ℝ 2 μ)))
    (hB : B ⊆ weakHilbertActionSet μ) :
    IsCompact (closure B) :=
  IsCompact.of_isClosed_subset
    (isCompact_weakHilbertActionSet μ)
    isClosed_closure
    (closure_minimal hB (isClosed_weakHilbertActionSet μ))

/-- Compact finite-intersection wrapper for weak squared-risk sublevels.

If the weak closure of `B` meets the risk constraints indexed by every
finite set of parameters, then one point of that closure satisfies all
parameter-indexed constraints at once. -/
theorem exists_global_weakHilbertRisk_below_of_fip
    {P : ι → Measure X} (hPμ : ∀ i, P i ≪ μ)
    (target : ι → ℝ) (bound : ι → ℝ≥0∞)
    (B : Set (WeakSpace ℝ (Lp ℝ 2 μ)))
    (hB : B ⊆ weakHilbertActionSet μ)
    (hfip :
      ∀ F : Finset ι,
        (closure B ∩
          ⋂ i ∈ F,
            {f |
              weakLpSquaredRisk (P i) (target i) f
                ≤ bound i}).Nonempty) :
    ∃ d ∈ closure B, ∀ i,
      weakLpSquaredRisk (P i) (target i) d ≤ bound i := by
  have hcompact :
      IsCompact (closure B) :=
    isCompact_closure_of_subset_weakHilbertActionSet
      (μ := μ) B hB
  obtain ⟨d, hdB, hdall⟩ :=
    hcompact.inter_iInter_nonempty
      (fun i =>
        {f |
          weakLpSquaredRisk (P i) (target i) f ≤ bound i})
      (fun i =>
        isClosed_weakLpSquaredRisk_sublevel
          (hPμ i) (target i) (bound i))
      hfip
  refine ⟨d, hdB, ?_⟩
  intro i
  exact mem_iInter.mp hdall i

end

end GraybillDeal
