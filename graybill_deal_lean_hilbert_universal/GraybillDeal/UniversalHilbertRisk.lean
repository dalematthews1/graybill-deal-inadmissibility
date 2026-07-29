import GraybillDeal.UniversalHilbertWeakCompactness
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weakly closed squared-risk sublevels

This file isolates the second functional-analytic ingredient in the
specialized complete-class argument.

Let `μ` be the Hilbert reference measure and let `P ≪ μ` be any model
measure.  Squared risk is defined on `L²(μ)` by integrating the chosen
representative against `P`.  Absolute continuity makes this independent
of `μ`-a.e. choices.

The key point is that no bounded Radon--Nikodym derivative is needed.
Norm convergence in `L²(μ)` has an almost-everywhere convergent
subsequence; absolute continuity transfers that convergence to `P`, and
Fatou's lemma makes every extended-real squared-risk sublevel norm
closed.  Convexity is the elementary convexity of squared loss.

Finally, `Convex.toWeakSpace_closure` says that a norm-closed convex set
has the same closure in the weak topology.  Hence the risk sublevels are
closed subsets of `WeakSpace ℝ (Lp ℝ 2 μ)`.
-/

namespace GraybillDeal

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X]
variable {μ P : Measure X}

/-- The pointwise nonnegative squared loss of an `L²(μ)` rule. -/
def lpSquaredLoss
    (target : ℝ) (f : Lp ℝ 2 μ) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal ((f x - target) ^ 2)

/-- Extended-real squared risk under `P`, for a rule represented in
`L²(μ)`.

When `P ≪ μ`, changing the representative of `f` on a `μ`-null set
cannot change this integral. -/
def lpSquaredRisk
    (P : Measure X) (target : ℝ) (f : Lp ℝ 2 μ) : ℝ≥0∞ :=
  ∫⁻ x, lpSquaredLoss target f x ∂P

/-- The squared-loss integrand is a.e. measurable under every measure
absolutely continuous with respect to the `L²` reference measure. -/
theorem aemeasurable_lpSquaredLoss
    (hPμ : P ≪ μ) (target : ℝ) (f : Lp ℝ 2 μ) :
    AEMeasurable (lpSquaredLoss target f) P := by
  unfold lpSquaredLoss
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    (((Lp.aestronglyMeasurable f).aemeasurable.mono_ac hPμ
      |>.sub aemeasurable_const).pow_const (2 : ℕ))

/-- Elementary convexity of scalar squared loss. -/
theorem squaredLoss_mix_le
    (a b u v target : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * u + b * v - target) ^ 2
      ≤ a * (u - target) ^ 2 + b * (v - target) ^ 2 := by
  have hgap :
      a * (u - target) ^ 2 + b * (v - target) ^ 2
          - (a * u + b * v - target) ^ 2
        =
      a * b * (u - v) ^ 2 := by
    have hb' : b = 1 - a := by linarith
    rw [hb']
    ring
  have hnonneg : 0 ≤ a * b * (u - v) ^ 2 := by positivity
  linarith

/-- Squared risk is convex under pointwise mixing of `L²` rules.

This is valid even when one or both risks are infinite. -/
theorem lpSquaredRisk_mix_le
    (hPμ : P ≪ μ)
    (target : ℝ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (f g : Lp ℝ 2 μ) :
    lpSquaredRisk P target (a • f + b • g)
      ≤
    ENNReal.ofReal a * lpSquaredRisk P target f
      + ENNReal.ofReal b * lpSquaredRisk P target g := by
  have hmixμ :
      (fun x => (a • f + b • g) x)
        =ᵐ[μ]
      (fun x => a * f x + b * g x) := by
    filter_upwards
      [Lp.coeFn_add (a • f) (b • g),
       Lp.coeFn_smul a f,
       Lp.coeFn_smul b g]
      with x hadd hfa hgb
    calc
      (a • f + b • g) x
          = (a • f) x + (b • g) x := hadd
      _ = a * f x + b * g x := by
        rw [hfa, hgb]
        simp only [Pi.smul_apply, smul_eq_mul]
  have hmixP :
      (fun x => (a • f + b • g) x)
        =ᵐ[P]
      (fun x => a * f x + b * g x) :=
    hPμ.ae_le hmixμ
  have hfmeas := aemeasurable_lpSquaredLoss
    (μ := μ) hPμ target f
  have hgmeas := aemeasurable_lpSquaredLoss
    (μ := μ) hPμ target g
  calc
    lpSquaredRisk P target (a • f + b • g)
        =
      ∫⁻ x,
        ENNReal.ofReal
          ((a * f x + b * g x - target) ^ 2) ∂P := by
            unfold lpSquaredRisk lpSquaredLoss
            exact lintegral_congr_ae
              (hmixP.fun_comp
                (fun z : ℝ => ENNReal.ofReal ((z - target) ^ 2)))
    _ ≤
      ∫⁻ x,
        ENNReal.ofReal
          (a * (f x - target) ^ 2
            + b * (g x - target) ^ 2) ∂P := by
              apply lintegral_mono
              intro x
              exact ENNReal.ofReal_le_ofReal
                (squaredLoss_mix_le
                  a b (f x) (g x) target ha hb hab)
    _ =
      ∫⁻ x,
        (ENNReal.ofReal a
            * ENNReal.ofReal ((f x - target) ^ 2)
          + ENNReal.ofReal b
            * ENNReal.ofReal ((g x - target) ^ 2)) ∂P := by
              apply lintegral_congr
              intro x
              rw [ENNReal.ofReal_add
                (mul_nonneg ha (sq_nonneg _))
                (mul_nonneg hb (sq_nonneg _))]
              rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
    _ =
      ENNReal.ofReal a * lpSquaredRisk P target f
        + ENNReal.ofReal b * lpSquaredRisk P target g := by
          change
            (∫⁻ x,
              ENNReal.ofReal a * lpSquaredLoss target f x
                + ENNReal.ofReal b * lpSquaredLoss target g x ∂P)
              =
            ENNReal.ofReal a * lpSquaredRisk P target f
              + ENNReal.ofReal b * lpSquaredRisk P target g
          rw [lintegral_add_left'
            (hfmeas.const_mul (ENNReal.ofReal a))]
          rw [lintegral_const_mul'' _ hfmeas,
            lintegral_const_mul'' _ hgmeas]
          rfl

/-- Every extended-real squared-risk sublevel is convex. -/
theorem convex_lpSquaredRisk_sublevel
    (hPμ : P ≪ μ) (target : ℝ) (c : ℝ≥0∞) :
    Convex ℝ {f : Lp ℝ 2 μ | lpSquaredRisk P target f ≤ c} := by
  intro f hf g hg a b ha hb hab
  change lpSquaredRisk P target (a • f + b • g) ≤ c
  calc
    lpSquaredRisk P target (a • f + b • g)
        ≤
      ENNReal.ofReal a * lpSquaredRisk P target f
        + ENNReal.ofReal b * lpSquaredRisk P target g :=
      lpSquaredRisk_mix_le hPμ target a b ha hb hab f g
    _ ≤ ENNReal.ofReal a * c + ENNReal.ofReal b * c :=
      add_le_add
        (mul_le_mul_left' hf (ENNReal.ofReal a))
        (mul_le_mul_left' hg (ENNReal.ofReal b))
    _ = c := by
      rw [← add_mul, ← ENNReal.ofReal_add ha hb, hab]
      simp

/-- Norm convergence in `L²(μ)` makes squared risk lower
semicontinuous under every `P ≪ μ`.

The proof uses an a.e.-convergent subsequence and Fatou's lemma, so no
uniform bound on `dP/dμ` is assumed. -/
theorem isClosed_lpSquaredRisk_sublevel
    (hPμ : P ≪ μ) (target : ℝ) (c : ℝ≥0∞) :
    IsClosed {f : Lp ℝ 2 μ | lpSquaredRisk P target f ≤ c} := by
  apply isSeqClosed_iff_isClosed.mp
  intro u f hu huf
  obtain ⟨ns, _hns, hpointμ⟩ :
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        ∀ᵐ x ∂μ,
          Tendsto (fun i => u (ns i) x) atTop (𝓝 (f x)) :=
    (tendstoInMeasure_of_tendsto_Lp huf).exists_seq_tendsto_ae
  have hpointP :
      ∀ᵐ x ∂P,
        Tendsto (fun i => u (ns i) x) atTop (𝓝 (f x)) :=
    hPμ.ae_le hpointμ
  have hloss_cont :
      Continuous
        (fun z : ℝ =>
          ENNReal.ofReal ((z - target) ^ 2)) :=
    ENNReal.continuous_ofReal.comp
      ((continuous_id.sub continuous_const).pow 2)
  have hloss_limit :
      ∀ᵐ x ∂P,
        Tendsto
          (fun i => lpSquaredLoss target (u (ns i)) x)
          atTop
          (𝓝 (lpSquaredLoss target f x)) := by
    filter_upwards [hpointP] with x hx
    exact hloss_cont.continuousAt.tendsto.comp hx
  calc
    lpSquaredRisk P target f
        =
      ∫⁻ x,
        liminf
          (fun i => lpSquaredLoss target (u (ns i)) x)
          atTop ∂P := by
            unfold lpSquaredRisk
            apply lintegral_congr_ae
            exact hloss_limit.mono
              (fun _ hx => hx.liminf_eq.symm)
    _ ≤
      liminf
        (fun i => lpSquaredRisk P target (u (ns i)))
        atTop := by
          unfold lpSquaredRisk
          exact lintegral_liminf_le'
            (fun i =>
              aemeasurable_lpSquaredLoss
                (μ := μ) hPμ target (u (ns i)))
    _ ≤ c :=
      liminf_le_of_frequently_le'
        (Frequently.of_forall fun i => hu (ns i))

/-- Squared risk is lower semicontinuous in the norm topology of
`L²(μ)`. -/
theorem lowerSemicontinuous_lpSquaredRisk
    (hPμ : P ≪ μ) (target : ℝ) :
    LowerSemicontinuous
      (lpSquaredRisk P target : Lp ℝ 2 μ → ℝ≥0∞) :=
  lowerSemicontinuous_iff_isClosed_preimage.mpr
    (fun c => isClosed_lpSquaredRisk_sublevel hPμ target c)

/-- Squared risk transported to the weak topology on `L²(μ)`. -/
def weakLpSquaredRisk
    (P : Measure X) (target : ℝ)
    (f : WeakSpace ℝ (Lp ℝ 2 μ)) : ℝ≥0∞ :=
  lpSquaredRisk P target
    ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f)

/-- A weak squared-risk sublevel is the image of its norm-topology
counterpart under the canonical linear equivalence. -/
theorem weakLpSquaredRisk_sublevel_eq_image
    (P : Measure X) (target : ℝ) (c : ℝ≥0∞) :
    {f : WeakSpace ℝ (Lp ℝ 2 μ) |
        weakLpSquaredRisk P target f ≤ c}
      =
    (toWeakSpace ℝ (Lp ℝ 2 μ)) ''
      {f : Lp ℝ 2 μ | lpSquaredRisk P target f ≤ c} := by
  ext f
  constructor
  · intro hf
    refine
      ⟨(toWeakSpace ℝ (Lp ℝ 2 μ)).symm f, hf, ?_⟩
    exact (toWeakSpace ℝ (Lp ℝ 2 μ)).apply_symm_apply f
  · rintro ⟨f, hf, rfl⟩
    simpa [weakLpSquaredRisk] using hf

/-- Every squared-risk sublevel is closed in the weak topology on
`L²(μ)`, assuming only `P ≪ μ`. -/
theorem isClosed_weakLpSquaredRisk_sublevel
    (hPμ : P ≪ μ) (target : ℝ) (c : ℝ≥0∞) :
    IsClosed
      {f : WeakSpace ℝ (Lp ℝ 2 μ) |
        weakLpSquaredRisk P target f ≤ c} := by
  rw [weakLpSquaredRisk_sublevel_eq_image]
  apply closure_eq_iff_isClosed.mp
  calc
    closure
        ((toWeakSpace ℝ (Lp ℝ 2 μ)) ''
          {f : Lp ℝ 2 μ | lpSquaredRisk P target f ≤ c})
        =
      (toWeakSpace ℝ (Lp ℝ 2 μ)) ''
        closure
          {f : Lp ℝ 2 μ | lpSquaredRisk P target f ≤ c} :=
      (convex_lpSquaredRisk_sublevel
        hPμ target c).toWeakSpace_closure ℝ |>.symm
    _ =
      (toWeakSpace ℝ (Lp ℝ 2 μ)) ''
        {f : Lp ℝ 2 μ | lpSquaredRisk P target f ≤ c} := by
          rw [(isClosed_lpSquaredRisk_sublevel
            hPμ target c).closure_eq]

/-- Every squared-risk sublevel remains convex after transport to the
weak topology. -/
theorem convex_weakLpSquaredRisk_sublevel
    (hPμ : P ≪ μ) (target : ℝ) (c : ℝ≥0∞) :
    Convex ℝ
      {f : WeakSpace ℝ (Lp ℝ 2 μ) |
        weakLpSquaredRisk P target f ≤ c} := by
  rw [weakLpSquaredRisk_sublevel_eq_image]
  exact
    (convex_lpSquaredRisk_sublevel hPμ target c).linear_image
      (toWeakSpace ℝ (Lp ℝ 2 μ)).toLinearMap

/-- Squared risk is also lower semicontinuous in the weak topology. -/
theorem lowerSemicontinuous_weakLpSquaredRisk
    (hPμ : P ≪ μ) (target : ℝ) :
    LowerSemicontinuous
      (weakLpSquaredRisk P target :
        WeakSpace ℝ (Lp ℝ 2 μ) → ℝ≥0∞) :=
  lowerSemicontinuous_iff_isClosed_preimage.mpr
    (fun c => isClosed_weakLpSquaredRisk_sublevel hPμ target c)

section ClippedAction

variable (μ : Measure X) [IsFiniteMeasure μ]

/-- The weakly topologized clipped action interval, additionally
restricted by one squared-risk upper bound. -/
def weakHilbertActionRiskSublevel
    (P : Measure X) (target : ℝ) (c : ℝ≥0∞) :
    Set (WeakSpace ℝ (Lp ℝ 2 μ)) :=
  weakHilbertActionSet μ ∩
    {f | weakLpSquaredRisk P target f ≤ c}

/-- A clipped one-parameter risk constraint is weakly closed. -/
theorem isClosed_weakHilbertActionRiskSublevel
    {P : Measure X} (hPμ : P ≪ μ)
    (target : ℝ) (c : ℝ≥0∞) :
    IsClosed
      (weakHilbertActionRiskSublevel μ P target c) :=
  (isClosed_weakHilbertActionSet μ).inter
    (isClosed_weakLpSquaredRisk_sublevel hPμ target c)

/-- A clipped one-parameter risk constraint is convex. -/
theorem convex_weakHilbertActionRiskSublevel
    {P : Measure X} (hPμ : P ≪ μ)
    (target : ℝ) (c : ℝ≥0∞) :
    Convex ℝ
      (weakHilbertActionRiskSublevel μ P target c) :=
  (convex_weakHilbertActionSet μ).inter
    (convex_weakLpSquaredRisk_sublevel hPμ target c)

/-- A clipped one-parameter risk constraint is weakly compact. -/
theorem isCompact_weakHilbertActionRiskSublevel
    {P : Measure X} (hPμ : P ≪ μ)
    (target : ℝ) (c : ℝ≥0∞) :
    IsCompact
      (weakHilbertActionRiskSublevel μ P target c) :=
  IsCompact.of_isClosed_subset
    (isCompact_weakHilbertActionSet μ)
    (isClosed_weakHilbertActionRiskSublevel μ hPμ target c)
    inter_subset_left

/-- The clipped feasible set cut out by an arbitrary family of
squared-risk upper bounds.  Finite parameter grids are the main
downstream use, but closedness does not require finiteness of the
indexing type. -/
def weakHilbertRiskFeasibleSet
    {ι : Type*}
    (P : ι → Measure X) (target : ι → ℝ)
    (bound : ι → ℝ≥0∞) :
    Set (WeakSpace ℝ (Lp ℝ 2 μ)) :=
  weakHilbertActionSet μ ∩
    ⋂ i, {f | weakLpSquaredRisk (P i) (target i) f ≤ bound i}

/-- An arbitrary intersection of clipped risk constraints is weakly
closed. -/
theorem isClosed_weakHilbertRiskFeasibleSet
    {ι : Type*}
    {P : ι → Measure X} (hPμ : ∀ i, P i ≪ μ)
    (target : ι → ℝ) (bound : ι → ℝ≥0∞) :
    IsClosed
      (weakHilbertRiskFeasibleSet μ P target bound) :=
  (isClosed_weakHilbertActionSet μ).inter
    (isClosed_iInter fun i =>
      isClosed_weakLpSquaredRisk_sublevel
        (hPμ i) (target i) (bound i))

/-- An arbitrary intersection of clipped risk constraints is convex. -/
theorem convex_weakHilbertRiskFeasibleSet
    {ι : Type*}
    {P : ι → Measure X} (hPμ : ∀ i, P i ≪ μ)
    (target : ι → ℝ) (bound : ι → ℝ≥0∞) :
    Convex ℝ
      (weakHilbertRiskFeasibleSet μ P target bound) :=
  (convex_weakHilbertActionSet μ).inter
    (convex_iInter fun i =>
      convex_weakLpSquaredRisk_sublevel
        (hPμ i) (target i) (bound i))

/-- Every clipped feasible set cut out by risk upper bounds is weakly
compact. -/
theorem isCompact_weakHilbertRiskFeasibleSet
    {ι : Type*}
    {P : ι → Measure X} (hPμ : ∀ i, P i ≪ μ)
    (target : ι → ℝ) (bound : ι → ℝ≥0∞) :
    IsCompact
      (weakHilbertRiskFeasibleSet μ P target bound) :=
  IsCompact.of_isClosed_subset
    (isCompact_weakHilbertActionSet μ)
    (isClosed_weakHilbertRiskFeasibleSet
      μ hPμ target bound)
    inter_subset_left

end ClippedAction

end

end GraybillDeal
