import GraybillDeal.UniversalFinitePriorBayesRisk

/-!
# Mapping positive finite priors

Finite-dimensional risk separation naturally produces a prior on a finite
index type.  The complete-class proof then regards its support points as
parameters in the full open interval.  This file records that elementary
pushforward operation and its definitional compatibility with Bayes actions.
-/

namespace GraybillDeal

noncomputable section

variable {ι Θ X : Type*}

namespace PositiveFinitePrior

/-- Push a positive finite prior forward along a map of parameter types. -/
def map (π : PositiveFinitePrior ι) (f : ι → Θ) :
    PositiveFinitePrior Θ where
  card := π.card
  point i := f (π.point i)
  weight := π.weight
  weight_pos := π.weight_pos
  weight_sum := π.weight_sum

@[simp]
theorem map_card (π : PositiveFinitePrior ι) (f : ι → Θ) :
    (π.map f).card = π.card :=
  rfl

@[simp]
theorem map_point (π : PositiveFinitePrior ι) (f : ι → Θ)
    (i : Fin π.card) :
    (π.map f).point i = f (π.point i) :=
  rfl

@[simp]
theorem map_weight (π : PositiveFinitePrior ι) (f : ι → Θ)
    (i : Fin π.card) :
    (π.map f).weight i = π.weight i :=
  rfl

/-- Mapping a prior and then forming its posterior mean is definitionally
the same as first reindexing the likelihood and target. -/
theorem bayesAction_map
    (π : PositiveFinitePrior ι) (f : ι → Θ)
    (density : Θ → X → ℝ) (target : Θ → ℝ) (x : X) :
    (π.map f).bayesAction density target x =
      π.bayesAction
        (fun i x => density (f i) x)
        (fun i => target (f i)) x :=
  rfl

end PositiveFinitePrior

end

end GraybillDeal
