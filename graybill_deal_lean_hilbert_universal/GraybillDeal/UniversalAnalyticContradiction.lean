import GraybillDeal.UniversalEqualQBridge
import GraybillDeal.UniversalSampleSizes
import GraybillDeal.UniversalUnequalQBridge
import GraybillDeal.UniversalWeakLimit

/-!
# The universal analytic contradiction

This module joins the equal- and unequal-shape branches.

The input is the posterior identity forced by the limiting-Bayes argument:

`universalPosteriorAction ν a b r q = r`

for every `0 < r < 1` and `q ≥ 0`.  The preceding analytic modules prove
that this identity is impossible:

* if `a ≠ b`, the first `q` derivative at the balanced point is both zero
  and a nonzero explicit cubic moment;
* if `a = b`, a mixed `(r,q)` coefficient is both zero and strictly
  positive.

Consequently no probability measure on the compactified parameter
interval can satisfy the identity for any positive shape pair.  The last
two theorems translate this statement to arbitrary normal-sample sizes
`n₁,n₂ ≥ 2`.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

/-- No probability measure can satisfy the universal posterior identity at
any pair of positive shapes. -/
theorem no_universalPosteriorIdentity
    (ν : Measure UniversalTheta) [IsProbabilityMeasure ν]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ¬ UniversalPosteriorIdentity ν a b := by
  intro H
  by_cases hab : a = b
  · subst b
    exact H.equal_impossible ν ha
  · exact H.unequal_false ha hb hab

/-- Existential form convenient for the limiting-Bayes endgame. -/
theorem not_exists_probabilityMeasure_universalPosteriorIdentity
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ¬ ∃ ν : ProbabilityMeasure UniversalTheta,
        UniversalPosteriorIdentity
          (ν : Measure UniversalTheta) a b := by
  rintro ⟨ν, H⟩
  exact no_universalPosteriorIdentity
    (ν : Measure UniversalTheta) ha hb H

/-- The analytic posterior identity is impossible for the gamma shapes
associated with any pair of normal samples of sizes at least two. -/
theorem no_universalPosteriorIdentity_sampleSizes
    (ν : Measure UniversalTheta) [IsProbabilityMeasure ν]
    {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) :
    ¬ UniversalPosteriorIdentity ν
      (universalShape n₁) (universalShape n₂) :=
  no_universalPosteriorIdentity ν
    (universalShape_pos hn₁)
    (universalShape_pos hn₂)

/-- Probability-measure existential form at arbitrary sample sizes. -/
theorem not_exists_probabilityMeasure_universalPosteriorIdentity_sampleSizes
    {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) :
    ¬ ∃ ν : ProbabilityMeasure UniversalTheta,
        UniversalPosteriorIdentity
          (ν : Measure UniversalTheta)
          (universalShape n₁) (universalShape n₂) :=
  not_exists_probabilityMeasure_universalPosteriorIdentity
    (universalShape_pos hn₁)
    (universalShape_pos hn₂)

end

end GraybillDeal
