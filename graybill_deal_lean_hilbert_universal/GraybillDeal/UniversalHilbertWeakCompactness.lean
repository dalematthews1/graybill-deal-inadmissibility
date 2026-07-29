import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Weak compactness for bounded Hilbert decision rules

This file isolates the first functional-analytic ingredient in the
specialized complete-class argument.  The public decision space is the
weak topology on `L²`; Banach--Alaoglu is used internally after transporting
the weak-star closed ball through the real Fréchet--Riesz equivalence.
-/

namespace GraybillDeal

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Topology

noncomputable section

section RealHilbert

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The inverse real Riesz map, with weak-star topology on the domain and
weak topology on the codomain. -/
private def weakDualRieszInv (φ : WeakDual ℝ H) : WeakSpace ℝ H :=
  toWeakSpace ℝ H
    ((InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual φ))

/-- The inverse Riesz map is weak-star-to-weak continuous. -/
private theorem continuous_weakDualRieszInv :
    Continuous (weakDualRieszInv (H := H)) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro g
  let y : H := (InnerProductSpace.toDual ℝ H).symm g
  have heq :
      (fun φ : WeakDual ℝ H =>
          (topDualPairing ℝ H).flip (weakDualRieszInv φ) g)
        =
      fun φ : WeakDual ℝ H => φ y := by
    funext φ
    let x : H :=
      (InnerProductSpace.toDual ℝ H).symm
        (WeakDual.toStrongDual φ)
    change g x = φ y
    calc
      g x = inner ℝ y x := by
        exact
          (InnerProductSpace.toDual_symm_apply
            (x := x) (y := g)).symm
      _ = inner ℝ x y := real_inner_comm x y
      _ = (WeakDual.toStrongDual φ) y := by
        exact
          InnerProductSpace.toDual_symm_apply
            (x := y) (y := WeakDual.toStrongDual φ)
      _ = φ y :=
        WeakDual.toStrongDual_apply φ y
  rw [heq]
  exact WeakDual.eval_continuous y

/-- A norm-closed ball in a real Hilbert space, regarded as a subset of
the same vector space carrying its weak topology. -/
def weakHilbertClosedBall (r : ℝ) : Set (WeakSpace ℝ H) :=
  toWeakSpace ℝ H '' Metric.closedBall (0 : H) r

private theorem weakDualRieszInv_image_closedBall (r : ℝ) :
    weakDualRieszInv ''
        (WeakDual.toStrongDual ⁻¹'
          Metric.closedBall (0 : StrongDual ℝ H) r)
      =
    weakHilbertClosedBall (H := H) r := by
  ext z
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    let x : H :=
      (InnerProductSpace.toDual ℝ H).symm
        (WeakDual.toStrongDual φ)
    refine ⟨x, ?_, rfl⟩
    apply mem_closedBall_zero_iff.mpr
    have hφnorm :
        ‖WeakDual.toStrongDual φ‖ ≤ r :=
      mem_closedBall_zero_iff.mp hφ
    simpa only
        [x, LinearIsometryEquiv.norm_map] using hφnorm
  · rintro ⟨x, hx, rfl⟩
    let φ : WeakDual ℝ H :=
      StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H x)
    refine ⟨φ, ?_, ?_⟩
    · apply mem_closedBall_zero_iff.mpr
      simpa only
          [φ, StrongDual.toStrongDual_toWeakDual,
            LinearIsometryEquiv.norm_map] using
        (mem_closedBall_zero_iff.mp hx)
    · simp only
        [φ, weakDualRieszInv,
          StrongDual.toStrongDual_toWeakDual,
          LinearIsometryEquiv.symm_apply_apply]

/-- Closed balls in a real Hilbert space are compact in the weak topology. -/
theorem isCompact_weakHilbertClosedBall (r : ℝ) :
    IsCompact (weakHilbertClosedBall (H := H) r) := by
  rw [← weakDualRieszInv_image_closedBall (H := H) r]
  exact
    (WeakDual.isCompact_closedBall
      (𝕜 := ℝ) (E := H) (0 : StrongDual ℝ H) r).image
      continuous_weakDualRieszInv

/-- Closed balls in a separable real Hilbert space are sequentially
compact in the weak topology. -/
theorem isSeqCompact_weakHilbertClosedBall
    [TopologicalSpace.SeparableSpace H] (r : ℝ) :
    IsSeqCompact (weakHilbertClosedBall (H := H) r) := by
  rw [← weakDualRieszInv_image_closedBall (H := H) r]
  exact
    (WeakDual.isSeqCompact_closedBall
      (𝕜 := ℝ) (E := H) (0 : StrongDual ℝ H) r).image
      continuous_weakDualRieszInv.seqContinuous

/-- In a separable real Hilbert space, a compact set for the weak topology
is metrizable. -/
theorem weakHilbert_metrizable_of_isCompact
    [TopologicalSpace.SeparableSpace H]
    (K : Set (WeakSpace ℝ H)) (hK : IsCompact K) :
    TopologicalSpace.MetrizableSpace K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let gs : ℕ → WeakSpace ℝ H → ℝ := fun n x =>
    (InnerProductSpace.toDual ℝ H (denseSeq H n))
      ((toWeakSpace ℝ H).symm x)
  have hgs_cont : ∀ n, Continuous (gs n) := by
    intro n
    let g : StrongDual ℝ (WeakSpace ℝ H) :=
      { toLinearMap :=
          (InnerProductSpace.toDual ℝ H (denseSeq H n)).toLinearMap.comp
            ((toWeakSpace ℝ H).symm : WeakSpace ℝ H →ₗ[ℝ] H)
        cont :=
          WeakBilin.eval_continuous
            (topDualPairing ℝ H).flip
            (InnerProductSpace.toDual ℝ H (denseSeq H n)) }
    change Continuous (fun x : WeakSpace ℝ H => g x)
    exact g.continuous
  have hgs_sep :
      ∀ ⦃x y : WeakSpace ℝ H⦄, x ≠ y →
        ∃ n, gs n x ≠ gs n y := by
    intro x y hxy
    contrapose! hxy
    apply (toWeakSpace ℝ H).symm.injective
    apply (InnerProductSpace.toDual ℝ H).injective
    exact
      DFunLike.ext'_iff.mpr <|
        (map_continuous
          (InnerProductSpace.toDual ℝ H
            ((toWeakSpace ℝ H).symm x))).ext_on
          (denseRange_denseSeq H)
          (map_continuous
            (InnerProductSpace.toDual ℝ H
              ((toWeakSpace ℝ H).symm y)))
          (Set.eqOn_range.mpr (funext fun n => by
            have hn := hxy n
            change
              inner ℝ (denseSeq H n) ((toWeakSpace ℝ H).symm x)
                =
              inner ℝ (denseSeq H n) ((toWeakSpace ℝ H).symm y)
              at hn
            change
              inner ℝ ((toWeakSpace ℝ H).symm x) (denseSeq H n)
                =
              inner ℝ ((toWeakSpace ℝ H).symm y) (denseSeq H n)
            exact
              (real_inner_comm (denseSeq H n)
                ((toWeakSpace ℝ H).symm x)).trans
                (hn.trans
                  (real_inner_comm
                    ((toWeakSpace ℝ H).symm y) (denseSeq H n)))))
  exact
    Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
      (fun n k => gs n k)
      (fun n => (hgs_cont n).comp continuous_subtype_val)
      fun x y hxy =>
        hgs_sep (Subtype.val_injective.ne hxy)

end RealHilbert

section L2Action

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

/-- The order interval of `L²(μ)` procedures taking values in `[0,1]`
almost everywhere. -/
def hilbertActionSet : Set (Lp ℝ 2 μ) :=
  Set.Icc 0 (Lp.const 2 μ 1)

@[simp]
theorem mem_hilbertActionSet {f : Lp ℝ 2 μ} :
    f ∈ hilbertActionSet μ ↔
      0 ≤ f ∧ f ≤ Lp.const 2 μ 1 :=
  Iff.rfl

/-- Pointwise-a.e. characterization of the Hilbert action interval. -/
theorem mem_hilbertActionSet_iff_ae {f : Lp ℝ 2 μ} :
    f ∈ hilbertActionSet μ ↔
      ∀ᵐ x ∂μ, f x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rintro ⟨h0, h1⟩
    have h0ae : 0 ≤ᵐ[μ] f :=
      (Lp.coeFn_nonneg f).2 h0
    have h1ae :
        f ≤ᵐ[μ] (Lp.const 2 μ 1 : X → ℝ) :=
      (Lp.coeFn_le f (Lp.const 2 μ 1)).2 h1
    filter_upwards
      [h0ae, h1ae, Lp.coeFn_const (p := (2 : ℝ≥0∞))
          (μ := μ) (c := (1 : ℝ))]
      with x hx0 hx1 hconst
    exact ⟨hx0, hx1.trans_eq hconst⟩
  · intro h
    constructor
    · rw [← Lp.coeFn_nonneg]
      exact h.mono fun x hx => hx.1
    · rw [← Lp.coeFn_le]
      filter_upwards
          [h, Lp.coeFn_const (p := (2 : ℝ≥0∞))
            (μ := μ) (c := (1 : ℝ))]
        with x hx hconst
      exact hx.2.trans_eq hconst.symm

theorem convex_hilbertActionSet :
    Convex ℝ (hilbertActionSet μ) := by
  intro f hf g hg a b ha hb hab
  rw [mem_hilbertActionSet_iff_ae] at hf hg ⊢
  have hmix :
      (fun x => (a • f + b • g) x)
        =ᵐ[μ]
      (fun x => a * f x + b * g x) := by
    filter_upwards
        [Lp.coeFn_add (a • f) (b • g),
         Lp.coeFn_smul a f,
         Lp.coeFn_smul b g]
      with x hadd hfa hgb
    calc
      (a • f + b • g) x = (a • f) x + (b • g) x := hadd
      _ = a * f x + b * g x := by
        rw [hfa, hgb]
        simp only [Pi.smul_apply, smul_eq_mul]
  filter_upwards [hf, hg, hmix] with x hfx hgx hmixx
  rw [hmixx]
  constructor
  · exact add_nonneg
      (mul_nonneg ha hfx.1)
      (mul_nonneg hb hgx.1)
  · calc
      a * f x + b * g x
          ≤ a * 1 + b * 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hfx.2 ha)
          (mul_le_mul_of_nonneg_left hgx.2 hb)
      _ = 1 := by rw [mul_one, mul_one, hab]

theorem isClosed_hilbertActionSet :
    IsClosed (hilbertActionSet μ) :=
  isClosed_Icc

/-- The weak-topology version of the clipped `L²` action interval. -/
def weakHilbertActionSet :
    Set (WeakSpace ℝ (Lp ℝ 2 μ)) :=
  toWeakSpace ℝ (Lp ℝ 2 μ) '' hilbertActionSet μ

theorem convex_weakHilbertActionSet :
    Convex ℝ (weakHilbertActionSet μ) := by
  exact
    (convex_hilbertActionSet μ).linear_image
      (toWeakSpace ℝ (Lp ℝ 2 μ)).toLinearMap

theorem isClosed_weakHilbertActionSet :
    IsClosed (weakHilbertActionSet μ) := by
  rw [← closure_eq_iff_isClosed]
  rw [weakHilbertActionSet,
    ← (convex_hilbertActionSet μ).toWeakSpace_closure ℝ,
    (isClosed_hilbertActionSet μ).closure_eq]

theorem norm_le_const_one_of_mem_hilbertActionSet
    {f : Lp ℝ 2 μ} (hf : f ∈ hilbertActionSet μ) :
    ‖f‖ ≤ ‖Lp.const 2 μ (1 : ℝ)‖ := by
  apply norm_le_norm_of_abs_le_abs
  have hconst : 0 ≤ (Lp.const 2 μ (1 : ℝ)) := by
    rw [← Lp.coeFn_nonneg]
    filter_upwards
        [Lp.coeFn_const (p := (2 : ℝ≥0∞))
          (μ := μ) (c := (1 : ℝ))]
      with x hx
    change (0 : ℝ) ≤ (Lp.const 2 μ (1 : ℝ)) x
    rw [hx]
    exact zero_le_one
  simpa only [abs_of_nonneg hf.1, abs_of_nonneg hconst] using hf.2

theorem weakHilbertActionSet_subset_closedBall :
    weakHilbertActionSet μ ⊆
      weakHilbertClosedBall (H := Lp ℝ 2 μ)
        ‖Lp.const 2 μ (1 : ℝ)‖ := by
  rintro z ⟨f, hf, rfl⟩
  refine ⟨f, ?_, rfl⟩
  exact mem_closedBall_zero_iff.mpr
    (norm_le_const_one_of_mem_hilbertActionSet μ hf)

/-- The clipped `L²` action interval is compact in the weak topology. -/
theorem isCompact_weakHilbertActionSet :
    IsCompact (weakHilbertActionSet μ) :=
  IsCompact.of_isClosed_subset
    (isCompact_weakHilbertClosedBall
      (H := Lp ℝ 2 μ) ‖Lp.const 2 μ (1 : ℝ)‖)
    (isClosed_weakHilbertActionSet μ)
    (weakHilbertActionSet_subset_closedBall μ)

/-- Under the standard separability hypothesis on the measure, the clipped
weak `L²` action interval is metrizable. -/
theorem metrizable_weakHilbertActionSet
    [IsSeparable μ] :
    TopologicalSpace.MetrizableSpace
      (weakHilbertActionSet μ) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : SecondCountableTopology (Lp ℝ 2 μ) := inferInstance
  letI : TopologicalSpace.SeparableSpace (Lp ℝ 2 μ) := inferInstance
  exact
    weakHilbert_metrizable_of_isCompact
      (weakHilbertActionSet μ)
      (isCompact_weakHilbertActionSet μ)

/-- Under the standard separability hypothesis on the measure, every
sequence of clipped `L²` rules has a weakly convergent subsequence whose
limit is still clipped. -/
theorem isSeqCompact_weakHilbertActionSet
    [IsSeparable μ] :
    IsSeqCompact (weakHilbertActionSet μ) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : SecondCountableTopology (Lp ℝ 2 μ) := inferInstance
  letI : TopologicalSpace.SeparableSpace (Lp ℝ 2 μ) := inferInstance
  intro u hu
  have huball :
      ∀ n,
        u n ∈
          weakHilbertClosedBall (H := Lp ℝ 2 μ)
            ‖Lp.const 2 μ (1 : ℝ)‖ :=
    fun n => weakHilbertActionSet_subset_closedBall μ (hu n)
  obtain ⟨a, ha, φ, hφ, htendsto⟩ :=
    isSeqCompact_weakHilbertClosedBall
      (H := Lp ℝ 2 μ) ‖Lp.const 2 μ (1 : ℝ)‖ huball
  refine ⟨a, ?_, φ, hφ, htendsto⟩
  exact
    (isClosed_weakHilbertActionSet μ).isSeqClosed
      (fun n => hu (φ n)) htendsto

end L2Action

end

end GraybillDeal
