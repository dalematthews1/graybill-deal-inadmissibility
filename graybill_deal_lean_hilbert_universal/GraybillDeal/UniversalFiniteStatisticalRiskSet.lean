import GraybillDeal.UniversalFinitePriorCleanup
import GraybillDeal.UniversalFiniteSeparation

/-!
# A statistical wrapper around finite-dimensional risk separation

`UniversalFiniteSeparation` proves the geometric supporting-hyperplane
lemma needed by a complete-class argument.  This file turns that geometric
statement into a reusable statistical statement.

For a finite parameter set `ι`, a procedure type `D`, and real risk vectors
`risk d : ι → ℝ`, form the *upper risk set*

```
{y | ∃ d, risk d ≤ y}.
```

If pointwise mixtures of procedures have risk no larger than the
corresponding mixture of risks, this upper risk set is convex.  Therefore
a procedure which cannot be improved strictly at every parameter is
supported by a probability vector on the finite parameter set.

The final section verifies the mixture hypothesis for an entirely finite
squared-loss experiment.  Thus every admissible rule in a finite
parameter, finite sample-space experiment minimizes Bayes risk for some
(possibly boundary) finite prior.

This is not the Brown complete-class theorem.  It formalizes the exact
finite risk-set step which Brown's local compactness and closure argument
must feed into.
-/

namespace GraybillDeal

open Set
open scoped BigOperators NNReal

noncomputable section

namespace FiniteStatisticalRiskSet

variable {ι D : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinatewise upper closure of the attainable risk vectors. -/
def upperRiskSet (risk : D → ι → ℝ) : Set (ι → ℝ) :=
  {y | ∃ d : D, ∀ i, risk d i ≤ y i}

theorem riskVector_mem_upperRiskSet
    (risk : D → ι → ℝ) (d : D) :
    risk d ∈ upperRiskSet risk :=
  ⟨d, fun _ => le_rfl⟩

/-- A pointwise mixture operation whose risks satisfy the usual convexity
inequality makes the upper risk set convex. -/
theorem upperRiskSet_convex
    (risk : D → ι → ℝ)
    (mix : ℝ → ℝ → D → D → D)
    (hmix :
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        ∀ d e i,
          risk (mix a b d e) i
            ≤ a * risk d i + b * risk e i) :
    Convex ℝ (upperRiskSet risk) := by
  intro y hy z hz a b ha hb hab
  obtain ⟨d, hd⟩ := hy
  obtain ⟨e, he⟩ := hz
  refine ⟨mix a b d e, ?_⟩
  intro i
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul]
  calc
    risk (mix a b d e) i
        ≤ a * risk d i + b * risk e i :=
      hmix a b ha hb hab d e i
    _ ≤ a * y i + b * z i :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hd i) ha)
        (mul_le_mul_of_nonneg_left (he i) hb)

/-- Finite-parameter statistical supporting-prior theorem.

The assumption on `d₀` is the weak Pareto consequence of ordinary
admissibility: no procedure is strictly better at *every* parameter.
The conclusion says that `d₀` minimizes weighted risk for a genuine
probability vector on the finite parameter set. -/
theorem exists_probability_supporting_risk_weights
    (risk : D → ι → ℝ)
    (mix : ℝ → ℝ → D → D → D)
    (hmix :
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        ∀ d e i,
          risk (mix a b d e) i
            ≤ a * risk d i + b * risk e i)
    (d₀ : D)
    (hpareto : ∀ d : D, ¬ ∀ i, risk d i < risk d₀ i) :
    ∃ w : ι → ℝ≥0,
      (∑ i, w i = 1) ∧
      ∀ d : D,
        (∑ i, (w i : ℝ) * risk d₀ i)
          ≤
        ∑ i, (w i : ℝ) * risk d i := by
  let S : Set (ι → ℝ) := upperRiskSet risk
  have hS : Convex ℝ S :=
    upperRiskSet_convex risk mix hmix
  have hd₀ : risk d₀ ∈ S :=
    riskVector_mem_upperRiskSet risk d₀
  have hno :
      ∀ y ∈ S, ¬ ∀ i, y i < risk d₀ i := by
    intro y hy hylt
    obtain ⟨d, hd⟩ := hy
    apply hpareto d
    intro i
    exact (hd i).trans_lt (hylt i)
  obtain ⟨w, hw_sum, hw_support⟩ :=
    FiniteCompleteClass.exists_probability_supporting_weights
      hS hd₀ hno
  refine ⟨w, hw_sum, ?_⟩
  intro d
  exact hw_support (risk d)
    (riskVector_mem_upperRiskSet risk d)

/-! ## From a probability vector to a positive finite prior -/

/-- Present a probability vector on a finite type as a possibly
zero-redundant finite prior. -/
def nonnegativeFinitePriorOfWeights
    (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) :
    NonnegativeFinitePrior ι where
  card := Fintype.card ι
  point j := (Fintype.equivFin ι).symm j
  weight j := w ((Fintype.equivFin ι).symm j)
  weight_sum := by
    calc
      (∑ j : Fin (Fintype.card ι),
          w ((Fintype.equivFin ι).symm j))
          = ∑ i : ι, w i :=
            (Fintype.equivFin ι).symm.sum_comp w
      _ = 1 := hw

/-- Deleting the zero weights from a finite probability vector preserves
every weighted sum. -/
theorem positivePartOfWeights_sum
    (w : ι → ℝ≥0) (hw : ∑ i, w i = 1)
    (f : ι → ℝ) :
    (∑ j :
        Fin (nonnegativeFinitePriorOfWeights w hw).positivePart.card,
      ((nonnegativeFinitePriorOfWeights w hw).positivePart.weight j : ℝ)
        * f ((nonnegativeFinitePriorOfWeights w hw).positivePart.point j))
      =
    ∑ i : ι, (w i : ℝ) * f i := by
  let π₀ := nonnegativeFinitePriorOfWeights w hw
  calc
    (∑ j : Fin π₀.positivePart.card,
      (π₀.positivePart.weight j : ℝ)
        * f (π₀.positivePart.point j))
        =
      ∑ k : Fin π₀.card,
        (π₀.weight k : ℝ) * f (π₀.point k) := by
          simpa [NonnegativeFinitePrior.positivePart] using
            π₀.positivePart_sum_weight_mul
              (fun k => f (π₀.point k))
    _ =
      ∑ i : ι, (w i : ℝ) * f i := by
        change
          (∑ k : Fin (Fintype.card ι),
            (w ((Fintype.equivFin ι).symm k) : ℝ)
              * f ((Fintype.equivFin ι).symm k))
            =
          ∑ i : ι, (w i : ℝ) * f i
        exact
          (Fintype.equivFin ι).symm.sum_comp
            (fun i => (w i : ℝ) * f i)

/-- Supporting probability weights can be represented by an actual
`PositiveFinitePrior`; all displayed prior masses are strictly positive.
This is the finite-support format consumed by the later Bayes-action
modules. -/
theorem exists_positiveFinitePrior_supporting_risk
    (risk : D → ι → ℝ)
    (mix : ℝ → ℝ → D → D → D)
    (hmix :
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        ∀ d e i,
          risk (mix a b d e) i
            ≤ a * risk d i + b * risk e i)
    (d₀ : D)
    (hpareto : ∀ d : D, ¬ ∀ i, risk d i < risk d₀ i) :
    ∃ π : PositiveFinitePrior ι,
      ∀ d : D,
        (∑ j, (π.weight j : ℝ)
          * risk d₀ (π.point j))
          ≤
        ∑ j, (π.weight j : ℝ)
          * risk d (π.point j) := by
  obtain ⟨w, hw, hsupport⟩ :=
    exists_probability_supporting_risk_weights
      risk mix hmix d₀ hpareto
  let π₀ := nonnegativeFinitePriorOfWeights w hw
  let π : PositiveFinitePrior ι := π₀.positivePart
  refine ⟨π, ?_⟩
  intro d
  have hs := hsupport d
  have hleft :=
    positivePartOfWeights_sum w hw (risk d₀)
  have hright :=
    positivePartOfWeights_sum w hw (risk d)
  change
    (∑ j, (π₀.positivePart.weight j : ℝ)
      * risk d₀ (π₀.positivePart.point j))
      ≤
    ∑ j, (π₀.positivePart.weight j : ℝ)
      * risk d (π₀.positivePart.point j)
  rwa [hleft, hright]

/-! ## A finite squared-loss experiment -/

variable {X : Type*} [Fintype X] [DecidableEq X]
variable [Nonempty ι]

/-- Squared-error risk in a finite sample-space dominated experiment.

`mass x` is the mass of the dominating measure and `density i x` is the
density at parameter `i`.  Nonnegativity is imposed in the theorems that
use this definition rather than built into its type.
-/
def finiteSquaredRisk
    (mass : X → ℝ)
    (density : ι → X → ℝ)
    (target : ι → ℝ)
    (estimator : X → ℝ)
    (i : ι) : ℝ :=
  ∑ x, mass x * density i x
    * (estimator x - target i) ^ 2

/-- Pointwise convex combination of two deterministic procedures. -/
def mixProcedure
    (a b : ℝ) (d e : X → ℝ) : X → ℝ :=
  fun x => a * d x + b * e x

/-- The elementary squared-loss convexity identity. -/
theorem squaredLoss_mix_gap
    (a b u v t : ℝ) (hab : a + b = 1) :
    a * (u - t) ^ 2 + b * (v - t) ^ 2
      - (a * u + b * v - t) ^ 2
      =
    a * b * (u - v) ^ 2 := by
  have hb : b = 1 - a := by linarith
  rw [hb]
  ring

theorem finiteSquaredRisk_mix_le
    {mass : X → ℝ}
    {density : ι → X → ℝ}
    (hmass : ∀ x, 0 ≤ mass x)
    (hdensity : ∀ i x, 0 ≤ density i x)
    (target : ι → ℝ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1)
    (d e : X → ℝ) (i : ι) :
    finiteSquaredRisk mass density target
        (mixProcedure a b d e) i
      ≤
    a * finiteSquaredRisk mass density target d i
      + b * finiteSquaredRisk mass density target e i := by
  unfold finiteSquaredRisk mixProcedure
  calc
    (∑ x,
        mass x * density i x
          * (a * d x + b * e x - target i) ^ 2)
      ≤
      ∑ x,
        mass x * density i x
          * (a * (d x - target i) ^ 2
            + b * (e x - target i) ^ 2) := by
        apply Finset.sum_le_sum
        intro x hx
        apply mul_le_mul_of_nonneg_left
        · have hgap :=
            squaredLoss_mix_gap
              a b (d x) (e x) (target i) hab
          have hnonneg :
              0 ≤ a * b * (d x - e x) ^ 2 := by positivity
          linarith
        · exact mul_nonneg (hmass x) (hdensity i x)
    _ =
      a * (∑ x,
        mass x * density i x * (d x - target i) ^ 2)
        +
      b * (∑ x,
        mass x * density i x * (e x - target i) ^ 2) := by
        simp_rw [mul_add, ← mul_assoc]
        rw [Finset.sum_add_distrib, Finset.mul_sum,
          Finset.mul_sum]
        apply congrArg₂ (· + ·)
        · apply Finset.sum_congr rfl
          intro x hx
          ring
        · apply Finset.sum_congr rfl
          intro x hx
          ring

/-- Ordinary admissibility for the finite squared-risk experiment. -/
def IsFiniteSquaredRiskAdmissible
    (mass : X → ℝ)
    (density : ι → X → ℝ)
    (target : ι → ℝ)
    (estimator : X → ℝ) : Prop :=
  ¬ ∃ candidate : X → ℝ,
    (∀ i,
      finiteSquaredRisk mass density target candidate i
        ≤ finiteSquaredRisk mass density target estimator i)
      ∧
    ∃ i,
      finiteSquaredRisk mass density target candidate i
        < finiteSquaredRisk mass density target estimator i

/-- Finite sample-space complete-class core: every admissible procedure
is supported by a probability prior on the finite parameter set.

The weights may vanish.  Passing from these boundary priors to strictly
positive finite priors, uniformly on an exhaustion, is one of the genuine
additional steps in Brown's theorem.
-/
theorem exists_probability_supporting_weights_of_finite_admissible
    {mass : X → ℝ}
    {density : ι → X → ℝ}
    (hmass : ∀ x, 0 ≤ mass x)
    (hdensity : ∀ i x, 0 ≤ density i x)
    (target : ι → ℝ)
    (estimator : X → ℝ)
    (hadmissible :
      IsFiniteSquaredRiskAdmissible
        mass density target estimator) :
    ∃ w : ι → ℝ≥0,
      (∑ i, w i = 1) ∧
      ∀ candidate : X → ℝ,
        (∑ i, (w i : ℝ)
          * finiteSquaredRisk mass density target estimator i)
          ≤
        ∑ i, (w i : ℝ)
          * finiteSquaredRisk mass density target candidate i := by
  apply exists_probability_supporting_risk_weights
    (risk := finiteSquaredRisk mass density target)
    (mix := mixProcedure)
  · intro a b ha hb hab d e i
    exact finiteSquaredRisk_mix_le
      hmass hdensity target a b ha hb hab d e i
  · intro candidate hstrict
    apply hadmissible
    refine ⟨candidate, ?_, ?_⟩
    · intro i
      exact (hstrict i).le
    · let i0 : ι := Classical.choice inferInstance
      exact ⟨i0, hstrict i0⟩

/-- The same finite-experiment result in the exact positive finite-prior
format used by the universal Bayes-action machinery.  Zero supporting
weights have been deleted, so every displayed mass is strictly positive. -/
theorem exists_positiveFinitePrior_supporting_finite_admissible
    {mass : X → ℝ}
    {density : ι → X → ℝ}
    (hmass : ∀ x, 0 ≤ mass x)
    (hdensity : ∀ i x, 0 ≤ density i x)
    (target : ι → ℝ)
    (estimator : X → ℝ)
    (hadmissible :
      IsFiniteSquaredRiskAdmissible
        mass density target estimator) :
    ∃ π : PositiveFinitePrior ι,
      ∀ candidate : X → ℝ,
        (∑ j, (π.weight j : ℝ)
          * finiteSquaredRisk mass density target estimator
              (π.point j))
          ≤
        ∑ j, (π.weight j : ℝ)
          * finiteSquaredRisk mass density target candidate
              (π.point j) := by
  apply exists_positiveFinitePrior_supporting_risk
    (risk := finiteSquaredRisk mass density target)
    (mix := mixProcedure)
  · intro a b ha hb hab d e i
    exact finiteSquaredRisk_mix_le
      hmass hdensity target a b ha hb hab d e i
  · intro candidate hstrict
    apply hadmissible
    refine ⟨candidate, fun i => (hstrict i).le, ?_⟩
    let i0 : ι := Classical.choice inferInstance
    exact ⟨i0, hstrict i0⟩

end FiniteStatisticalRiskSet

end

end GraybillDeal
