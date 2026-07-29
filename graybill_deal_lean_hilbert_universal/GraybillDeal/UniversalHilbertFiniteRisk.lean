import GraybillDeal.UniversalHilbertFiniteGrid
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Finite real risks on the clipped Hilbert action set

The finite-dimensional separation theorem is formulated for real-valued
risk vectors, while the measure-theoretic Hilbert layer naturally uses
`ℝ≥0∞`.  On the clipped action set this distinction is harmless: if the
target lies in `[0,1]` and the model measure is a probability measure, the
squared risk is at most one.

This file proves that bound, defines the corresponding real risk, transports
order and strict order through `ENNReal.toReal`, and packages convex mixing
inside the clipped action subtype.  These are the conversion lemmas needed
before applying the existing finite supporting-prior theorem.
-/

namespace GraybillDeal

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X]
variable {μ P : Measure X} [IsFiniteMeasure μ]

/-- Two points of `[0,1]` have squared distance at most one. -/
theorem sq_sub_le_one_of_mem_Icc
    {u target : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (htarget : target ∈ Set.Icc (0 : ℝ) 1) :
    (u - target) ^ 2 ≤ 1 := by
  rcases hu with ⟨hu0, hu1⟩
  rcases htarget with ⟨ht0, ht1⟩
  have hlo : -1 ≤ u - target := by linarith
  have hhi : u - target ≤ 1 := by linarith
  have hprod :
      0 ≤ (1 - (u - target)) * (1 + (u - target)) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- A weakly represented clipped rule is `[0,1]`-valued almost everywhere
for the Hilbert reference measure. -/
theorem ae_mem_Icc_of_mem_weakHilbertActionSet
    {f : WeakSpace ℝ (Lp ℝ 2 μ)}
    (hf : f ∈ weakHilbertActionSet μ) :
    ∀ᵐ x ∂μ,
      ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x
        ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨g, hg, rfl⟩ := hf
  simpa using
    (mem_hilbertActionSet_iff_ae (μ := μ)).mp hg

/-- A clipped rule has extended-real squared risk at most one under any
absolutely continuous probability model with target in `[0,1]`. -/
theorem weakLpSquaredRisk_le_one_of_mem_action
    (hPμ : P ≪ μ) [IsProbabilityMeasure P]
    {target : ℝ} (htarget : target ∈ Set.Icc (0 : ℝ) 1)
    {f : WeakSpace ℝ (Lp ℝ 2 μ)}
    (hf : f ∈ weakHilbertActionSet μ) :
    weakLpSquaredRisk P target f ≤ 1 := by
  have hfP :
      ∀ᵐ x ∂P,
        ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x
          ∈ Set.Icc (0 : ℝ) 1 :=
    hPμ.ae_le
      (ae_mem_Icc_of_mem_weakHilbertActionSet
        (μ := μ) hf)
  have hloss :
      ∀ᵐ x ∂P,
        lpSquaredLoss target
            ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x
          ≤ 1 := by
    filter_upwards [hfP] with x hx
    exact ENNReal.ofReal_le_one.mpr
      (sq_sub_le_one_of_mem_Icc hx htarget)
  calc
    weakLpSquaredRisk P target f
        =
      ∫⁻ x,
        lpSquaredLoss target
          ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f) x ∂P := rfl
    _ ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂P :=
      lintegral_mono_ae hloss
    _ = 1 := by simp

/-- In particular, every clipped squared risk in the normalized experiment
is finite. -/
theorem weakLpSquaredRisk_ne_top_of_mem_action
    (hPμ : P ≪ μ) [IsProbabilityMeasure P]
    {target : ℝ} (htarget : target ∈ Set.Icc (0 : ℝ) 1)
    {f : WeakSpace ℝ (Lp ℝ 2 μ)}
    (hf : f ∈ weakHilbertActionSet μ) :
    weakLpSquaredRisk P target f ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (weakLpSquaredRisk_le_one_of_mem_action
      (μ := μ) hPμ htarget hf)

/-- The finite real counterpart of weak extended-real squared risk. -/
def weakLpSquaredRiskReal
    (P : Measure X) (target : ℝ)
    (f : WeakSpace ℝ (Lp ℝ 2 μ)) : ℝ :=
  (weakLpSquaredRisk P target f).toReal

/-- On clipped rules, comparison of real risks is exactly comparison of
extended-real risks. -/
theorem weakLpSquaredRiskReal_le_iff
    (hPμ : P ≪ μ) [IsProbabilityMeasure P]
    {target : ℝ} (htarget : target ∈ Set.Icc (0 : ℝ) 1)
    {f g : WeakSpace ℝ (Lp ℝ 2 μ)}
    (hf : f ∈ weakHilbertActionSet μ)
    (hg : g ∈ weakHilbertActionSet μ) :
    weakLpSquaredRiskReal P target f
        ≤ weakLpSquaredRiskReal P target g
      ↔
    weakLpSquaredRisk P target f
        ≤ weakLpSquaredRisk P target g := by
  exact ENNReal.toReal_le_toReal
    (weakLpSquaredRisk_ne_top_of_mem_action
      (μ := μ) hPμ htarget hf)
    (weakLpSquaredRisk_ne_top_of_mem_action
      (μ := μ) hPμ htarget hg)

/-- The analogous strict-order conversion. -/
theorem weakLpSquaredRiskReal_lt_iff
    (hPμ : P ≪ μ) [IsProbabilityMeasure P]
    {target : ℝ} (htarget : target ∈ Set.Icc (0 : ℝ) 1)
    {f g : WeakSpace ℝ (Lp ℝ 2 μ)}
    (hf : f ∈ weakHilbertActionSet μ)
    (hg : g ∈ weakHilbertActionSet μ) :
    weakLpSquaredRiskReal P target f
        < weakLpSquaredRiskReal P target g
      ↔
    weakLpSquaredRisk P target f
        < weakLpSquaredRisk P target g := by
  exact ENNReal.toReal_lt_toReal
    (weakLpSquaredRisk_ne_top_of_mem_action
      (μ := μ) hPμ htarget hf)
    (weakLpSquaredRisk_ne_top_of_mem_action
      (μ := μ) hPμ htarget hg)

/-- The clipped weak Hilbert action space as a procedure type. -/
abbrev WeakHilbertAction
    (μ : Measure X) [IsFiniteMeasure μ] :=
  {f : WeakSpace ℝ (Lp ℝ 2 μ) // f ∈ weakHilbertActionSet μ}

/-- Total pointwise mixing on the clipped action subtype.

For convex coefficients it is the actual affine combination.  For other
coefficients it returns the first rule; the supporting-prior theorem only
uses the convex-coefficient branch. -/
def weakHilbertActionMix
    (μ : Measure X) [IsFiniteMeasure μ]
    (a b : ℝ)
    (f g : WeakHilbertAction μ) :
    WeakHilbertAction μ :=
  if h : 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 then
    ⟨a • f.1 + b • g.1,
      convex_weakHilbertActionSet μ
        f.2 g.2 h.1 h.2.1 h.2.2⟩
  else
    f

/-- On convex coefficients, the total subtype mixer is the expected affine
combination. -/
theorem weakHilbertActionMix_coe
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1)
    (f g : WeakHilbertAction μ) :
    (weakHilbertActionMix μ a b f g :
      WeakSpace ℝ (Lp ℝ 2 μ))
      =
    a • (f : WeakSpace ℝ (Lp ℝ 2 μ))
      + b • (g : WeakSpace ℝ (Lp ℝ 2 μ)) := by
  simp [weakHilbertActionMix, ha, hb, hab]

/-- Convexity of extended-real weak squared risk, stated directly in the
weak topology. -/
theorem weakLpSquaredRisk_mix_le
    (hPμ : P ≪ μ)
    (target : ℝ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1)
    (f g : WeakSpace ℝ (Lp ℝ 2 μ)) :
    weakLpSquaredRisk P target (a • f + b • g)
      ≤
    ENNReal.ofReal a * weakLpSquaredRisk P target f
      + ENNReal.ofReal b * weakLpSquaredRisk P target g := by
  simpa [weakLpSquaredRisk] using
    lpSquaredRisk_mix_le
      (μ := μ) hPμ target a b ha hb hab
      ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f)
      ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm g)

/-- Real squared risk is convex on the clipped action subtype. -/
theorem weakLpSquaredRiskReal_actionMix_le
    (hPμ : P ≪ μ) [IsProbabilityMeasure P]
    {target : ℝ} (htarget : target ∈ Set.Icc (0 : ℝ) 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1)
    (f g : WeakHilbertAction μ) :
    weakLpSquaredRiskReal P target
        (weakHilbertActionMix μ a b f g :
          WeakSpace ℝ (Lp ℝ 2 μ))
      ≤
    a * weakLpSquaredRiskReal P target
        (f : WeakSpace ℝ (Lp ℝ 2 μ))
      + b * weakLpSquaredRiskReal P target
        (g : WeakSpace ℝ (Lp ℝ 2 μ)) := by
  let Rf := weakLpSquaredRisk P target (f : WeakSpace ℝ (Lp ℝ 2 μ))
  let Rg := weakLpSquaredRisk P target (g : WeakSpace ℝ (Lp ℝ 2 μ))
  have hRf : Rf ≠ ∞ :=
    weakLpSquaredRisk_ne_top_of_mem_action
      (μ := μ) hPμ htarget f.2
  have hRg : Rg ≠ ∞ :=
    weakLpSquaredRisk_ne_top_of_mem_action
      (μ := μ) hPμ htarget g.2
  have hright :
      ENNReal.ofReal a * Rf + ENNReal.ofReal b * Rg ≠ ∞ := by
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRf,
       ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRg⟩
  rw [weakHilbertActionMix_coe
    (μ := μ) a b ha hb hab f g]
  change
    (weakLpSquaredRisk P target
      (a • (f : WeakSpace ℝ (Lp ℝ 2 μ))
        + b • (g : WeakSpace ℝ (Lp ℝ 2 μ)))).toReal
      ≤
    a * Rf.toReal + b * Rg.toReal
  calc
    (weakLpSquaredRisk P target
      (a • (f : WeakSpace ℝ (Lp ℝ 2 μ))
        + b • (g : WeakSpace ℝ (Lp ℝ 2 μ)))).toReal
        ≤
      (ENNReal.ofReal a * Rf
        + ENNReal.ofReal b * Rg).toReal :=
      ENNReal.toReal_mono hright
        (weakLpSquaredRisk_mix_le
          (μ := μ) hPμ target a b ha hb hab f g)
    _ =
      a * Rf.toReal + b * Rg.toReal := by
        rw [ENNReal.toReal_add
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRf)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRg)]
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
        simp [ENNReal.toReal_ofReal ha,
          ENNReal.toReal_ofReal hb]

end

end GraybillDeal
