import GraybillDeal.UniversalHilbertFiniteRisk
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Strict midpoint improvement for Hilbert squared risk

When the model measure is the Hilbert reference measure, real squared
risk is the squared `L²` distance from the constant target.  The
parallelogram law therefore gives an exact midpoint identity, with a
strictly positive gap whenever the two weak rules are distinct.  In
particular, this applies to distinct members of the clipped weak action
set.
-/

namespace GraybillDeal

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X]
variable {μ : Measure X} [IsFiniteMeasure μ]

/-- The integral of squared distance from a constant is the squared
`L²` norm of the corresponding translated vector. -/
theorem integral_sq_sub_eq_norm_sub_const_sq
    (f : Lp ℝ 2 μ) (target : ℝ) :
    (∫ x, (f x - target) ^ 2 ∂μ)
      = ‖f - Lp.const 2 μ target‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [Lp.coeFn_sub f (Lp.const 2 μ target),
      Lp.coeFn_const (p := (2 : ℝ≥0∞)) (μ := μ) (c := target)]
    with x hsub hconst
  rw [hsub]
  change
    (f x - target) ^ 2
      =
    inner ℝ
      (f x - (Lp.const 2 μ target) x)
      (f x - (Lp.const 2 μ target) x)
  rw [hconst]
  simp [pow_two]

/-- Real weak squared risk under the Hilbert reference measure is a
squared Hilbert-space distance. -/
theorem weakLpSquaredRiskReal_self_eq_norm_sub_const_sq
    (f : WeakSpace ℝ (Lp ℝ 2 μ)) (target : ℝ) :
    weakLpSquaredRiskReal μ target f
      =
    ‖(toWeakSpace ℝ (Lp ℝ 2 μ)).symm f
        - Lp.const 2 μ target‖ ^ 2 := by
  let g : Lp ℝ 2 μ :=
    (toWeakSpace ℝ (Lp ℝ 2 μ)).symm f
  calc
    weakLpSquaredRiskReal μ target f
        =
      (∫ x, (g x - target) ^ 2 ∂μ) := by
        unfold weakLpSquaredRiskReal weakLpSquaredRisk
          lpSquaredRisk lpSquaredLoss
        symm
        exact integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall
            (fun x => sq_nonneg (g x - target)))
          ((((Lp.stronglyMeasurable g).measurable.sub
            measurable_const).pow_const 2).aestronglyMeasurable)
    _ = ‖g - Lp.const 2 μ target‖ ^ 2 :=
      integral_sq_sub_eq_norm_sub_const_sq g target

/-- Exact squared-norm midpoint identity in a real Hilbert space. -/
theorem norm_midpoint_sq_eq
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b : H) :
    ‖(1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b‖ ^ 2
      =
    (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2
      - ‖a - b‖ ^ 2 / 4 := by
  have hpar := parallelogram_law_with_norm ℝ a b
  rw [← smul_add, norm_smul]
  norm_num
  nlinarith

/-- Exact midpoint identity for real weak squared risk under the
Hilbert reference measure. -/
theorem weakLpSquaredRiskReal_midpoint_eq
    (f g : WeakSpace ℝ (Lp ℝ 2 μ)) (target : ℝ) :
    weakLpSquaredRiskReal μ target
        ((1 / 2 : ℝ) • f + (1 / 2 : ℝ) • g)
      =
    (weakLpSquaredRiskReal μ target f
        + weakLpSquaredRiskReal μ target g) / 2
      -
    ‖(toWeakSpace ℝ (Lp ℝ 2 μ)).symm f
        - (toWeakSpace ℝ (Lp ℝ 2 μ)).symm g‖ ^ 2 / 4 := by
  rw [weakLpSquaredRiskReal_self_eq_norm_sub_const_sq,
    weakLpSquaredRiskReal_self_eq_norm_sub_const_sq,
    weakLpSquaredRiskReal_self_eq_norm_sub_const_sq]
  let ef := (toWeakSpace ℝ (Lp ℝ 2 μ)).symm f
  let eg := (toWeakSpace ℝ (Lp ℝ 2 μ)).symm g
  let c := Lp.const 2 μ target
  have hvec :
      (toWeakSpace ℝ (Lp ℝ 2 μ)).symm
            ((1 / 2 : ℝ) • f + (1 / 2 : ℝ) • g) - c
        =
      (1 / 2 : ℝ) • (ef - c)
        + (1 / 2 : ℝ) • (eg - c) := by
    dsimp [ef, eg, c]
    simp only [map_add, map_smul]
    module
  rw [hvec, norm_midpoint_sq_eq]
  dsimp [ef, eg, c]
  congr 2
  abel

/-- Distinct weak `L²` rules have midpoint squared risk strictly below
the average of their squared risks under the Hilbert reference measure.
This is the strict midpoint lemma used on the clipped weak action set. -/
theorem weakLpSquaredRiskReal_midpoint_lt_average
    (f g : WeakSpace ℝ (Lp ℝ 2 μ)) (target : ℝ)
    (hne : f ≠ g) :
    weakLpSquaredRiskReal μ target
        ((1 / 2 : ℝ) • f + (1 / 2 : ℝ) • g)
      <
    (weakLpSquaredRiskReal μ target f
        + weakLpSquaredRiskReal μ target g) / 2 := by
  have hefg :
      (toWeakSpace ℝ (Lp ℝ 2 μ)).symm f
        ≠
      (toWeakSpace ℝ (Lp ℝ 2 μ)).symm g :=
    (toWeakSpace ℝ (Lp ℝ 2 μ)).symm.injective.ne hne
  have hnorm :
      0 <
      ‖(toWeakSpace ℝ (Lp ℝ 2 μ)).symm f
          - (toWeakSpace ℝ (Lp ℝ 2 μ)).symm g‖ ^ 2 := by
    exact sq_pos_of_pos
      (norm_pos_iff.mpr (sub_ne_zero.mpr hefg))
  rw [weakLpSquaredRiskReal_midpoint_eq]
  nlinarith

/-- If the first rule has no larger risk than the second, their
midpoint strictly improves the second whenever the rules are distinct. -/
theorem weakLpSquaredRiskReal_midpoint_lt_right
    (f g : WeakSpace ℝ (Lp ℝ 2 μ)) (target : ℝ)
    (hne : f ≠ g)
    (hle :
      weakLpSquaredRiskReal μ target f
        ≤ weakLpSquaredRiskReal μ target g) :
    weakLpSquaredRiskReal μ target
        ((1 / 2 : ℝ) • f + (1 / 2 : ℝ) • g)
      <
    weakLpSquaredRiskReal μ target g := by
  have hmid :=
    weakLpSquaredRiskReal_midpoint_lt_average
      (μ := μ) f g target hne
  linarith

end

end GraybillDeal
