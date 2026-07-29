# Brown--Lehmann--Casella bridge

## Exact source theorem

The remaining decision-theoretic input is Lehmann and Casella,
*Theory of Point Estimation*, second edition, Section 5.7, Theorem 7.15
(printed pages 382--383).  Their theorem is explicitly identified as a
specialization of Brown, *Fundamentals of Statistical Exponential
Families with Applications in Statistical Decision Theory*, Appendix to
Chapter 4, Theorem 4A.12 (printed pages 254--268).

Primary source records:

- <https://link.springer.com/book/10.1007/b98854>
- <https://projecteuclid.org/ebooks/institute-of-mathematical-statistics-lecture-notes-monograph-series/Fundamentals-of-statistical-exponential-families-with-applications-in-statistical-decision/Chapter/Appendix-to-Chapter-4-Pointwise-Limits-of-Bayes-Procedures/lnms/1215466766>

In the real-action specialization used here, the result says:

> For a dominated experiment with a sigma-finite reference measure and
> everywhere-positive probability densities, if the loss is continuous,
> strictly convex in the action, and coercive, then every admissible
> measurable procedure is the reference-a.e. pointwise limit of Bayes
> procedures for finite-support probability priors.

This is exactly the implication represented in Lean by
`MeasurablePositiveFiniteBayesCompleteClassProperty`.

## Match to the universal reduced experiment

| Printed hypothesis | Universal reduced instance |
|---|---|
| sigma-finite dominating measure | `universalReducedObservationReference universalReducedLebesgueMeasure a b` |
| measurable likelihood sections | `measurable_universalReducedLikelihood_observation` |
| likelihood strictly positive at every observation and parameter | `universalReducedLikelihood_pos` |
| each likelihood is a probability density | proved separately by the canonical likelihood-normalization module |
| real, closed, convex action space | either `ℝ`, using coercivity, or the compact interval `[0,1]` after clipping |
| continuous, strictly convex loss | `universalInteriorSquaredLoss` and its continuity/strict-convexity lemmas |
| coercivity on `ℝ` | `universalInteriorSquaredLoss_coercive` |
| measurable admissible procedure | `IsMeasurablyAdmissibleDensitySquared` |
| finite-support Bayes procedures converging a.e. | `HasPositiveFiniteBayesApproximation` |

Neither source requires the parameter space or sample space to be closed
or compact.  Thus the open spaces `(0,1)` and
`(0,1) × (0,∞)` are not an obstruction.

Under squared loss, every finite-support Bayes procedure is the posterior
mean.  The project already proves positivity of its denominator,
measurability, the posterior square decomposition, pointwise uniqueness,
and deletion of zero prior weights.  Consequently the source theorem's
finite-support priors match `PositiveFinitePrior`.

## Honest Lean target

A reusable squared-loss specialization should have the following shape.
This is a target signature, not an axiom or a declaration currently made
by the project.

```lean
theorem lehmannCasella_finiteSupport_ae_posteriorMean
    {Θ X : Type*} [Nonempty Θ] [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν]
    (density : Θ → X → ℝ) (target : Θ → ℝ)
    (hdensity_measurable : ∀ θ, Measurable (density θ))
    (hdensity_pos : ∀ θ x, 0 < density θ x)
    (hdensity_probability :
      ∀ θ, IsProbabilityMeasure
        (ν.withDensity fun x => ENNReal.ofReal (density θ x))) :
    MeasurablePositiveFiniteBayesCompleteClassProperty
      ν density target
```

For the universal contradiction, the still smaller baseline-only
conclusion would suffice:

```lean
IsMeasurablyAdmissibleDensitySquared
    ρ likelihood target universalReducedBaseline →
  HasPositiveFiniteBayesApproximation
    ρ likelihood target universalReducedBaseline
```

## Architecture correction

`UniversalLocalCompleteClassRiskSet.lean` proves a valid downstream
implication: zero in the closure of the scalar attainable local-gap range
gives small local gaps, Markov bounds, and ultimately an a.e.-convergent
diagonal sequence.  It does **not** prove Brown's separation theorem.

In particular, `ClosedConvexLocalFiniteBayesRiskSet.hasZeroInGapClosure`
uses only:

- `gap_ne_top`;
- `riskSet_eq_closure`;
- `zero_mem`.

Its `riskSet_closed` and `riskSet_convex` fields are bookkeeping fields,
not a derivation of `riskSet_eq_closure` or `zero_mem`.  Moreover, the
one-dimensional range of posterior-mean `L¹` gaps is not evidently
convex: mixing priors produces observation-dependent mixtures of
posterior means, while distance is not affine.  Therefore
`MeasurableClosedConvexLocalRiskSetProperty` should be treated as a
strong sufficient hypothesis, not as the intended formal statement of
Brown 4A.12.

The direct Brown--Lehmann--Casella conclusion is the preferred proof
target.  The local-gap modules remain useful, checked alternative
downstream machinery if a compatible local approximation theorem is
proved independently.

## Completed prerequisites

1. Every canonical sample-size likelihood is normalized as a probability
   density.
2. Every admissible real-valued procedure is `[0,1]`-valued almost
   everywhere by measurable clipping, and every positive finite-prior
   posterior mean already lies in `[0,1]`.

These facts are checked in
`UniversalReducedLikelihoodNormalization.lean` and
`UniversalCompactAction.lean`.

## Remaining formalization layers

1. Formalize the compact-procedure topology used in Brown Appendix 4A,
   including randomized procedures if following Brown literally.
2. Prove the closure/complete-class result for finite-support Bayes
   procedures and remove randomization using strict convexity and
   Jensen's inequality.
3. Extract the sequence with reference-a.e. pointwise convergence and
   identify its members with `PositiveFinitePrior.bayesAction`.

These three layers are the substantive Brown theorem; they should not be
replaced by an unproved local closure field.

## Brown's proof map

Brown's Appendix 4A makes the required topology explicit.  For the compact
action space `A*`, a randomized procedure is a measurable probability
kernel `δ(da | x)`.  If `f ∈ L¹(ν)` and `c ∈ C(A*)`, define

\[
\beta_\delta(f,c)
  = \int_X\int_{A^*}c(a)\,\delta(da\mid x)\,f(x)\,\nu(dx).
\]

The procedure topology is the weakest topology making all these
functionals continuous.  Brown's proof then proceeds through the
following results.

1. The randomized-procedure space is compact in this topology.
2. Every parameterwise risk is lower semicontinuous.
3. A convergent net of nonrandomized procedures has a subnet converging
   in measure, and then a subsequence converging almost everywhere.
4. On each finite parameter subset, finite-dimensional risk-set
   separation produces a finite-support Bayes procedure.
5. Direct the finite parameter subsets by inclusion.  Compactness gives
   an accumulation procedure of the corresponding restricted Bayes
   procedures, showing that the closure of finite-support Bayes
   procedures is essentially complete.
6. Strict convexity and Jensen's inequality show that randomized
   admissible procedures are nonrandomized and that two admissible
   procedures with the same risk function agree almost everywhere.
7. The unique minimal complete class is therefore contained in the
   nonrandomized part of the closure of the finite-support Bayes class.
   The convergence result extracts the desired almost-everywhere
   pointwise sequence.

The existing finite-dimensional separation modules cover the local
ingredient in item 4.  The new work is chiefly items 1--3 and the
topological assembly in items 5--7.
