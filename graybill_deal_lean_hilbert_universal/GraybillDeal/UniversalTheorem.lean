import GraybillDeal.UniversalCanonicalReducedTheorem
import GraybillDeal.UniversalCanonicalComponentDensity
import GraybillDeal.UniversalClosedConvexLocalTheorem
import GraybillDeal.UniversalCompactAction
import GraybillDeal.UniversalCompleteClassConvergence
import GraybillDeal.UniversalCompleteClassExhaustion
import GraybillDeal.UniversalConditionalRawTheorem
import GraybillDeal.UniversalFiniteStatisticalCompleteClass
import GraybillDeal.UniversalFiniteStatisticalRiskSet
import GraybillDeal.UniversalFinitePriorBayesRisk
import GraybillDeal.UniversalFinitePriorCleanup
import GraybillDeal.UniversalFinitePriorRisk
import GraybillDeal.UniversalGammaPositiveSupport
import GraybillDeal.UniversalHilbertUnconditionalTheorem
import GraybillDeal.UniversalNestedDensityBridge
import GraybillDeal.UniversalRawAdmissibility
import GraybillDeal.UniversalRawComponentLaws
import GraybillDeal.UniversalRawCoordinateLift
import GraybillDeal.UniversalRawDecisionBridge
import GraybillDeal.UniversalRawDensityIdentity
import GraybillDeal.UniversalRawLawFamily
import GraybillDeal.UniversalRawLawUnconditional
import GraybillDeal.UniversalRadialGammaIntegral
import GraybillDeal.UniversalReducedDominator
import GraybillDeal.UniversalReducedChangeOfVariables
import GraybillDeal.UniversalReducedLikelihoodNormalization
import GraybillDeal.UniversalReducedRiskRebase
import GraybillDeal.UniversalRiskScaling

/-!
# Universal Graybill--Deal inadmissibility formalization

This is the umbrella module for the sample-size-universal proof.

The following parts are machine checked without project-specific axioms:

* the equal- and unequal-shape posterior-identity contradictions;
* the sample-size specialization for every `n₁,n₂ ≥ 2`;
* endpoint reweighting, weak compactness, and the a.e.-to-pointwise
  limiting-Bayes bridge;
* sigma-finite exhaustion and diagonal extraction from compatible local
  positive finite-Bayes approximants;
* the finite-parameter finite-sample-space statistical risk-set theorem,
  including supporting positive finite priors and exact identification of
  an admissible rule with its finite-prior posterior mean;
* the exact finite-prior Bayes-risk decomposition on an arbitrary
  measurable sample space, including posterior-mean minimization and
  the equality-implies-almost-everywhere-identity conclusion;
* the local closed-risk-set-to-geometric-bad-set argument, including the
  Markov bound which feeds the sigma-finite diagonal extraction;
* the measurability-correct conditional complete-class endgame;
* sigma-finiteness and full open support of the canonical reference
  measure;
* normalization of every canonical sample-size likelihood as a
  probability density;
* reduction of admissible real-valued rules to the compact action
  interval `[0,1]` by measurable clipping, together with the fact that
  every positive finite-prior posterior mean already lies in `[0,1]`;
* extraction and total measurable extension of a reduced dominator;
* almost-everywhere transport of literal raw sufficient statistics into
  the open reduced observation space;
* the three-dimensional positive-coordinate change of variables and its
  exact absolute Jacobian;
* the exact all-positive-shape radial Gamma integration, including the
  identification with the full reduced density;
* transport of the three-dimensional Jacobian theorem to native nested
  triples and the exact canonical-triple-to-reduced measure pushforward;
* exact rebasing between `ENNReal` dominated risk and real weighted risk;
* exact raw normal-sample oracle risk transport;
* the exact independent Gamma-component law and its `D²`-tilted
  pushforward;
* arbitrary-positive-shape Gamma support, including the half-shape
  boundary case;
* exact positive scaling of the tilted Gamma product, identification
  with the canonical weighted triple density, and its unrestricted
  raw-to-reduced pushforward;
* realization of every interior reduced parameter by explicit positive
  raw variances and the assembled all-parameter raw-risk theorem.
* the Hilbert-space complete-class argument: finite-grid supporting
  positive priors, compact finite intersections in the clipped weak
  `L²` action set, identification of the closure dominator by strict
  midpoint improvement, weak-to-strong convergence at the anchor model,
  and almost-everywhere subsequence extraction;
* the unconditional conclusion that the literal raw Graybill--Deal
  estimator is not universally measurably admissible for every pair of
  sample sizes at least two.

The final theorem is
`GraybillDeal.universalRawGraybillDeal_not_admissible`.  It has no
complete-class, density-law, or other project-specific theorem hypothesis:
those layers are all discharged by the imported modules.

The stronger
`GraybillDeal.universalRawGraybillDeal_not_admissible_among_all_measurableEstimators`
states the conclusion in the ordinary class of all measurable functions
on the raw sample space.
-/
