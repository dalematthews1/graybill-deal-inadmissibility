import GraybillDeal.UniversalFinitePriorRisk
import Mathlib.Data.Fintype.EquivFin

/-!
# Removing zero masses from finite priors

The printed complete-class theorem produces prior distributions with
finite support.  A finite presentation may nevertheless contain redundant
zero-mass entries.  The universal limiting-Bayes bridge uses
`PositiveFinitePrior`, whose displayed entries all have strictly positive
mass.

This file proves that the distinction is harmless: deleting zero entries
and reindexing by a `Fin` type preserves normalization and every
finite-prior posterior mean exactly.
-/

namespace GraybillDeal

open scoped BigOperators NNReal

noncomputable section

variable {Θ X : Type*}

/-- A generic finite probability prior whose presentation may contain
zero-mass entries. -/
structure NonnegativeFinitePrior (Θ : Type*) where
  card : ℕ
  point : Fin card → Θ
  weight : Fin card → ℝ≥0
  weight_sum : ∑ i, weight i = 1

namespace NonnegativeFinitePrior

/-- Indices carrying genuine support mass. -/
abbrev SupportIndex (π : NonnegativeFinitePrior Θ) :=
  {i : Fin π.card // π.weight i ≠ 0}

/-- Delete zero masses and reindex the remaining support by a `Fin` type. -/
def positivePart
    (π : NonnegativeFinitePrior Θ) :
    PositiveFinitePrior Θ where
  card := Fintype.card π.SupportIndex
  point j :=
    π.point ((Fintype.equivFin π.SupportIndex).symm j).1
  weight j :=
    π.weight ((Fintype.equivFin π.SupportIndex).symm j).1
  weight_pos j :=
    (pos_iff_ne_zero.mpr
      ((Fintype.equivFin π.SupportIndex).symm j).2)
  weight_sum := by
    change
      (∑ j,
        π.weight ((Fintype.equivFin π.SupportIndex).symm j).1) = 1
    calc
      (∑ j,
          π.weight ((Fintype.equivFin π.SupportIndex).symm j).1)
          = ∑ i : π.SupportIndex, π.weight i.1 :=
              (Fintype.equivFin π.SupportIndex).symm.sum_comp
                (fun i : π.SupportIndex => π.weight i.1)
      _
          = ∑ i : Fin π.card, π.weight i := by
              rw [← Finset.sum_filter_ne_zero
                (Finset.univ : Finset (Fin π.card))]
              simpa using
                (Finset.sum_subtype_eq_sum_filter
                  (s := (Finset.univ : Finset (Fin π.card)))
                  (p := fun i => π.weight i ≠ 0)
                  π.weight)
      _ = 1 := π.weight_sum

/-- A weighted sum is unchanged when zero prior entries are deleted. -/
theorem positivePart_sum_weight_mul
    (π : NonnegativeFinitePrior Θ)
    (f : Fin π.card → ℝ) :
    (∑ j : Fin π.positivePart.card,
        (π.positivePart.weight j : ℝ)
          * f ((Fintype.equivFin π.SupportIndex).symm j).1)
      =
    ∑ i : Fin π.card, (π.weight i : ℝ) * f i := by
  change
    (∑ j,
      (π.weight ((Fintype.equivFin π.SupportIndex).symm j).1 : ℝ)
        * f ((Fintype.equivFin π.SupportIndex).symm j).1)
      =
    ∑ i : Fin π.card, (π.weight i : ℝ) * f i
  calc
    (∑ j,
      (π.weight ((Fintype.equivFin π.SupportIndex).symm j).1 : ℝ)
        * f ((Fintype.equivFin π.SupportIndex).symm j).1)
        =
      ∑ i : π.SupportIndex, (π.weight i.1 : ℝ) * f i.1 :=
        (Fintype.equivFin π.SupportIndex).symm.sum_comp
          (fun i : π.SupportIndex => (π.weight i.1 : ℝ) * f i.1)
    _
        =
      ∑ i ∈ (Finset.univ : Finset (Fin π.card)) with
          π.weight i ≠ 0,
        (π.weight i : ℝ) * f i := by
          simpa using
            (Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset (Fin π.card)))
              (p := fun i => π.weight i ≠ 0)
              (fun i => (π.weight i : ℝ) * f i))
    _ = ∑ i : Fin π.card, (π.weight i : ℝ) * f i := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hnot
      have hzero : π.weight i = 0 := by
        simpa using hnot
      simp [hzero]

/-- Unnormalized posterior weight for a possibly redundant presentation. -/
def posteriorWeight
    (π : NonnegativeFinitePrior Θ)
    (density : Θ → X → ℝ) (x : X)
    (i : Fin π.card) : ℝ :=
  (π.weight i : ℝ) * density (π.point i) x

/-- Posterior mean for a possibly redundant finite presentation. -/
def bayesAction
    (π : NonnegativeFinitePrior Θ)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ) (x : X) : ℝ :=
  finiteWeightedMean Finset.univ
    (π.posteriorWeight density x)
    (fun i => target (π.point i))

/-- Removing zero masses preserves the posterior denominator. -/
theorem positivePart_posteriorWeight_sum
    (π : NonnegativeFinitePrior Θ)
    (density : Θ → X → ℝ) (x : X) :
    (∑ j,
      π.positivePart.posteriorWeight density x j)
      =
    ∑ i, π.posteriorWeight density x i := by
  simpa [positivePart, PositiveFinitePrior.posteriorWeight,
    posteriorWeight] using
    π.positivePart_sum_weight_mul
      (fun i => density (π.point i) x)

/-- Removing zero masses preserves the posterior numerator. -/
theorem positivePart_posteriorNumerator_sum
    (π : NonnegativeFinitePrior Θ)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ) (x : X) :
    (∑ j,
      π.positivePart.posteriorWeight density x j
        * target (π.positivePart.point j))
      =
    ∑ i,
      π.posteriorWeight density x i
        * target (π.point i) := by
  have h :=
    π.positivePart_sum_weight_mul
      (fun i => density (π.point i) x * target (π.point i))
  simpa [positivePart, PositiveFinitePrior.posteriorWeight, posteriorWeight,
    mul_assoc] using h

/-- Removing zero masses preserves the finite-prior Bayes rule exactly. -/
theorem positivePart_bayesAction
    (π : NonnegativeFinitePrior Θ)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ) (x : X) :
    π.positivePart.bayesAction density target x
      =
    π.bayesAction density target x := by
  unfold PositiveFinitePrior.bayesAction bayesAction
    finiteWeightedMean finiteWeightTotal
  rw [π.positivePart_posteriorNumerator_sum density target x,
    π.positivePart_posteriorWeight_sum density x]

end NonnegativeFinitePrior

end

end GraybillDeal
