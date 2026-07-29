# Universal Graybill--Deal formalization status

## Current theorem boundary

The universal theorem is complete and unconditional.

For every pair of positive residual degrees of freedom
\(\nu_1,\nu_2>0\)—equivalently every pair of sample sizes
\(n_1,n_2\ge2\)—Lean proves

```lean
GraybillDeal.universalRawGraybillDeal_not_admissible
```

for every family satisfying the two-independent-normal-sample
specification.  No complete-class or density-law proposition is supplied
to this theorem.

The stronger existential entry point

```lean
GraybillDeal.exists_universalRaw_dominator
```

supplies one measurable total reduced rule whose induced raw estimator
has no larger squared-error risk for every common mean and every positive
variance pair, and strictly smaller risk at some parameter point.

The strongest theorem,
`universalRawGraybillDeal_not_admissible_among_all_measurableEstimators`,
states the consequence in the ordinary class of all measurable
raw-sample estimators.  The corresponding concrete witness is
`exists_universalRaw_measurableEstimator_dominator`.

The former continuous complete-class boundary is discharged by the
problem-specific Hilbert-space proof in the `UniversalHilbert*.lean`
modules.  It works in \(L^2(P_{1/2})\), constructs positive finite-prior
Bayes witnesses on every finite parameter set, applies compact finite
intersections in the clipped weak action set, identifies the global
closure dominator by strict midpoint improvement, upgrades weak
convergence to strong \(L^2\) convergence using the anchor-risk bound,
and extracts an almost-everywhere convergent Bayes subsequence.

The complete mathematical blueprint remains in
`HILBERT_COMPLETE_CLASS_PROOF.md`; the checked implementation and audit
are summarized in `V24_COMPLETION_STATUS.md`.

## Fully machine-checked parts

- The universal equal- and unequal-shape analytic posterior-identity
  contradictions.
- Specialization of the contradiction to all \(n_1,n_2\ge2\).
- Endpoint reweighting, weak compactness of finite priors, and the
  almost-everywhere-to-pointwise limiting-Bayes bridge.
- The measurable decision-theory interface, finite-prior posterior
  square decomposition, strict Bayes optimality, and cleanup of
  zero-weight atoms.
- The exact continuous-sample-space finite-prior Bayes-risk identity:
  finite prior sums equal integrated posterior loss, the posterior mean
  minimizes the resulting real Bayes risk, and equality forces any
  measurable competitor to equal that posterior mean almost everywhere
  whenever the posterior denominator is positive almost everywhere.
- Finite-dimensional Hahn--Banach separation and normalized
  nonnegative supporting weights.
- The statistical upper-risk-set version of that separation theorem,
  including the finite-parameter, finite-sample-space squared-loss
  specialization and deletion of zero weights to obtain a genuine
  positive finite prior.
- The exact finite-parameter, finite-sample-space complete-class theorem:
  an admissible squared-loss rule is the posterior mean for a positive
  finite prior.
- The local-gap closure interface, arbitrarily small local-gap
  extraction, and the exact Markov estimate
  \[
  \text{gap}\le\varepsilon^2
  \quad\Longrightarrow\quad
  m\{d(\delta_\pi,\delta)\ge\varepsilon\}\le\varepsilon.
  \]
- Sigma-finite finite-measure exhaustion, Borel--Cantelli
  diagonalization, and extraction of one global a.e.-convergent
  finite-Bayes sequence from compatible local approximants.
- Sigma-finiteness and positivity on nonempty open sets of the canonical
  reduced reference measure.
- Exact normalization of the canonical rebased likelihood for every
  positive pair of residual degrees of freedom: its `withDensity`
  measure is a probability measure and its `lintegral` is one.
- Compact-action reduction: every positive finite-prior posterior mean
  lies in `[0,1]`; measurable clipping weakly decreases risk and strictly
  decreases it whenever a finite-risk rule leaves `[0,1]` on a set of
  positive reference mass.  Consequently every measurably admissible
  canonical rule is `[0,1]`-valued almost everywhere.
- Extraction of a measurable reduced dominator and its measurable
  extension to all of \(\mathbb R^2\).
- Exact rebasing between dominated `ENNReal` risk, finite weighted
  reduced risk, and literal raw real-valued risk.
- The literal arbitrary-sample-size Graybill--Deal estimator, the oracle
  risk decomposition, and weak/strict raw-risk transport.
- Exact component laws from the two normal samples:
  \(V=D^2/\tau\sim\Gamma(1/2,1/2)\),
  \(U_i=\mathrm{RSS}_i/v_i\sim\Gamma(\nu_i/2,1/2)\), together with their
  joint independence.
- Exact \(D^2\)-size biasing of the component law: the first Gamma shape
  is raised from \(1/2\) to \(3/2\), and the only scalar is \(\tau\).
- Exact raw-to-component coordinate algebra and the equality
  \[
  Q_{\rm raw}=\tau\,\operatorname{map}(F,M_{\rm tilted}),
  \]
  where every symbol is an explicit Lean definition.
- Assembly of the pointwise reduced-density law into a single
  all-positive-variance law family and then into the all-parameter raw
  admissibility predicate.
- A single total measurable reduced rule that works simultaneously for
  all finite positive reference scalings.
- Explicit positive variances
  \(v_1=(\nu_1+1)\theta\) and
  \(v_2=(\nu_2+1)(1-\theta)\), proving that every
  \(\theta\in(0,1)\) is realized by the raw oracle parameter.
- Almost-everywhere positivity of both residual sums of squares, the
  variance-component sum, and the reduced coordinates; construction of
  an everywhere-defined measurable reduced observation agreeing with
  the literal coordinates almost everywhere.
- The positive-coordinate partial homeomorphism
  \((r,q,t)\leftrightarrow(g_1,g_2,w)\), its Fréchet derivative,
  determinant \(-t^2\), absolute Jacobian \(t^2\), and the full
  three-dimensional Lebesgue `lintegral` substitution theorem.
- Measurability, integrability, and exact evaluation of the radial
  Gamma kernel for all \(a,b>0\), together with the exact identity
  “canonical weighted triple density \(\times t^2\), integrated over
  \(t>0\), equals `universalFullReducedDensity`.”
- The full nested-triple measure theorem: the canonical density
  restricted to the positive orthant pushes exactly to reduced Lebesgue
  measure with density `universalFullReducedDensity`, together with an
  adapter for any raw projection agreeing on that orthant.
- Strict positivity of every positive-shape Gamma law, including shape
  \(1/2\), and of all three oracle-scaled components almost everywhere.
- The exact positive scaling formula
  \(c^{-1}f(x/c)\) for Gamma densities and the product-density law for
  \[
  (V,U_1,U_2)\mapsto
  \left(\theta U_1/\nu_1,\,
    (1-\theta)U_2/\nu_2,\,V\right).
  \]
- Symbolic identification of that scaled product density with the
  canonical weighted triple density, including
  \(\Gamma(3/2)=\sqrt{\pi}/2\).
- The unconditional deterministic identity
  `universalRiskTiltedComponentReducedDensityIdentity`, and hence the
  all-positive-variance raw reduced-law family with no extra density
  hypothesis.
- Finite-grid compact minimization, supporting positive finite priors,
  posterior-mean identification, and pushforward to priors on the full
  interior parameter space.
- Compact finite intersections of weakly closed fixed-parameter risk
  sublevels in the clipped weak `L²` action set.
- Strict-midpoint identification of a global Hilbert dominator with any
  measurably admissible rule.
- Metrizable weak-closure sequence extraction retaining an actual prior
  witness at every index.
- The anchor-risk weak-to-strong `L²` convergence theorem and direct
  convergence-in-measure/almost-everywhere subsequence extraction.
- The unconditional complete-class theorem
  `universalMeasurableFiniteBayesCompleteClassProperty_halfShapes`.
- The final dominator and inadmissibility theorems
  `exists_universalRaw_dominator` and
  `universalRawGraybillDeal_not_admissible`.
- The all-measurable-estimator interface
  `exists_universalRaw_measurableEstimator_dominator` and the resulting
  unrestricted measurable inadmissibility theorem.

## Remaining mathematical obligation

None for the stated universal theorem.  The aggregate 3444-job build
passes, and the final axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.  The proof chain contains no
`sorry`, `admit`, or project-defined `axiom`.

## Main entry points

- `GraybillDeal/UniversalTheorem.lean`
- `GraybillDeal/UniversalAnalyticContradiction.lean`
- `GraybillDeal/UniversalCanonicalReducedTheorem.lean`
- `GraybillDeal/UniversalCompactAction.lean`
- `GraybillDeal/UniversalReducedLikelihoodNormalization.lean`
- `GraybillDeal/UniversalCompleteClassExhaustion.lean`
- `GraybillDeal/UniversalLocalCompleteClassRiskSet.lean`
- `GraybillDeal/UniversalClosedConvexLocalTheorem.lean`
- `GraybillDeal/UniversalFinitePriorBayesRisk.lean`
- `GraybillDeal/UniversalFiniteStatisticalCompleteClass.lean`
- `GraybillDeal/UniversalRawCoordinateLift.lean`
- `GraybillDeal/UniversalRawComponentLaws.lean`
- `GraybillDeal/UniversalCanonicalComponentDensity.lean`
- `GraybillDeal/UniversalGammaPositiveSupport.lean`
- `GraybillDeal/UniversalRawReducedDensityLaw.lean`
- `GraybillDeal/UniversalRawDensityIdentity.lean`
- `GraybillDeal/UniversalRawAdmissibility.lean`
- `GraybillDeal/UniversalRawLawFamily.lean`
- `GraybillDeal/UniversalRawLawUnconditional.lean`
- `GraybillDeal/UniversalHilbertReference.lean`
- `GraybillDeal/UniversalHilbertWeakCompactness.lean`
- `GraybillDeal/UniversalHilbertFiniteGrid.lean`
- `GraybillDeal/UniversalHilbertFiniteGridPosterior.lean`
- `GraybillDeal/UniversalHilbertCanonicalIntersection.lean`
- `GraybillDeal/UniversalHilbertAdmissibleIdentification.lean`
- `GraybillDeal/UniversalHilbertBayesSequence.lean`
- `GraybillDeal/UniversalHilbertStrongConvergence.lean`
- `GraybillDeal/UniversalHilbertBayesExtraction.lean`
- `GraybillDeal/UniversalHilbertCompleteClass.lean`
- `GraybillDeal/UniversalHilbertUnconditionalTheorem.lean`
- `GraybillDeal/UniversalHilbertUnconditionalTheoremAxiomAudit.lean`
- `GraybillDeal/UniversalReducedChangeOfVariables.lean`
- `GraybillDeal/UniversalRadialGammaIntegral.lean`
- `GraybillDeal/UniversalNestedDensityBridge.lean`
- `GraybillDeal/UniversalConditionalRawTheorem.lean`
- `GraybillDeal/UniversalRawDecisionBridge.lean`
- `GraybillDeal/UniversalTheoremAxiomAudit.lean`
- `BROWN_LEHMANN_CASELLA_BRIDGE.md`
