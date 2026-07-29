# v24 completion status

## Result

The v24 Hilbert-space route is complete and machine checked.

For arbitrary positive residual degrees of freedom `ν₁,ν₂`, arbitrary
measurable sample coordinates, and any family of laws satisfying the
two-independent-normal-sample specification, Lean proves

```lean
theorem GraybillDeal.universalRawGraybillDeal_not_admissible
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : ℝ → NNReal → NNReal → Measure Ω}
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hfamily : IsUniversalTwoNormalSampleFamily ν₁ ν₂ X Y P) :
    ¬ IsUniversallyMeasurablyAdmissibleRawGraybillDeal
      ν₁ ν₂ X Y P
```

The companion theorem
`GraybillDeal.exists_universalRaw_dominator` constructs the precise
existential conclusion used here: one measurable total reduced rule whose
induced raw estimator has no larger squared-error risk for every common
mean and every positive variance pair, and strictly smaller risk at some
parameter point.

The strongest interface is
`GraybillDeal.universalRawGraybillDeal_not_admissible_among_all_measurableEstimators`.
It quantifies over the ordinary decision class of all measurable
raw-sample estimators, not just the syntactic subclass induced by reduced
rules.  Its concrete witness theorem is
`GraybillDeal.exists_universalRaw_measurableEstimator_dominator`.

Since the actual sample sizes are `ν₁ + 1` and `ν₂ + 1`, this covers every
pair of sample sizes at least two.

## Complete-class chain

The former Brown--Lehmann--Casella hypothesis is discharged by a
problem-specific deterministic Hilbert-space proof:

1. `UniversalHilbertReference.lean` fixes the anchor model
   `θ₀ = 1/2` and proves equivalence of its null sets with the canonical
   sigma-finite dominating measure.
2. `UniversalHilbertRisk.lean` and
   `UniversalHilbertWeakCompactness.lean` establish weak lower
   semicontinuity of fixed-parameter risk and compact metrizability of the
   clipped weak `L²` action set.
3. `UniversalHilbertFiniteGrid.lean`,
   `UniversalHilbertFiniteGridBayes.lean`,
   `UniversalHilbertBayesRiskBridge.lean`, and
   `UniversalHilbertFiniteGridPosterior.lean` construct a positive
   finite-prior posterior-mean witness on each finite parameter grid.
4. `UniversalHilbertUniversalFiniteGrid.lean`,
   `UniversalHilbertGlobalIntersection.lean`, and
   `UniversalHilbertCanonicalIntersection.lean` apply the compact
   finite-intersection property to obtain a global weak-closure
   dominator.
5. `UniversalHilbertStrictMidpoint.lean` and
   `UniversalHilbertAdmissibleIdentification.lean` use strict convexity
   at the anchor model to identify that dominator with the assumed
   admissible rule.
6. `UniversalHilbertBayesSequence.lean` selects a weakly convergent
   sequence together with an actual positive finite prior at every index.
7. `UniversalHilbertStrongConvergence.lean` turns weak convergence plus
   the anchor-risk bound into strong `L²` convergence.
8. `UniversalHilbertBayesExtraction.lean` uses convergence in measure
   and an almost-everywhere convergent subsequence to produce the exact
   finite-Bayes approximation property.
9. `UniversalHilbertCompleteClass.lean` proves
   `universalMeasurableFiniteBayesCompleteClassProperty_halfShapes`.
10. `UniversalHilbertUnconditionalTheorem.lean` rewrites the residual
    shapes, feeds the complete-class result into the already checked raw
    density and risk-transport stack, and exposes the resulting reduced
    rule as an ordinary measurable estimator on the raw sample space.

## Verification

The pinned toolchain is Lean 4.32.0 with Mathlib v4.32.0.

The following commands pass:

```sh
lake build
lake env lean \
  GraybillDeal/UniversalHilbertUnconditionalTheoremAxiomAudit.lean
```

The aggregate build reports:

```text
Build completed successfully (3444 jobs).
```

The final axiom audit reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

This is true for the weak-to-strong lemma, the closure-to-Bayes
approximation theorem, the complete-class theorem, the dominator theorem,
and the final raw inadmissibility theorem.  A source scan finds no
`sorry`, `admit`, `opaque`, or project-defined `axiom` declaration in the
proof chain.

## Checkpoints

The v23 checkpoint remains useful as a verified fallback and historical
record of the conditional route.  The v24 directory name still contains
`wip` for provenance, but its imported theorem stack is no longer
work-in-progress.
