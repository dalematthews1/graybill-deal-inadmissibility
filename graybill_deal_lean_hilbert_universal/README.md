# Graybill–Deal counterexample: Lean formalization

This project formalizes a counterexample to admissibility of the
Graybill–Deal estimator for every equal sample size $n\geq10$ in Lean
4.32.0 and Mathlib v4.32.0.  It includes the explicit fixed-$n=13$
construction with perturbation coefficient $1/2000$, as well as the
sample-size-generic analytic, probabilistic, almost-everywhere coordinate,
and literal raw-estimator arguments.

## Machine-checked so far

- `Algebra.lean`: exact rational inequalities, completed-square certificate,
  and positivity of the fixed and general tail polynomials.
- `Elementary.lean`: clipping to $[0,1]$, pointwise contraction of squared
  error, perturbation identities, and weighted-estimator algebra.
- `Risk.lean`: the integral-level squared-risk decomposition under explicit
  integrability and orthogonality hypotheses.
- `Coordinates.lean`: the $(s,x)$ coordinate formulas and denominator bounds.
- `AnalyticKernel.lean`: the exact $x/-x$ paired numerator and kernel identity.
- `IntegralPairing.lean`: passage from the integral on $[-1,1]$ to the paired
  integral on $[0,1]$.
- `GeometricSeries.lean`: Mathlib's absolutely convergent order-four binomial
  series specialized to $(1-s^2x^2)^{-5}$.
- `PointwiseSeries.lean` and `SeriesIntegration.lean`: the pointwise
  negative-binomial expansion, the explicit summable majorant
  $60\binom{m+4}{4}(s^2)^m$, and termwise interval integration.
- `ShiftedBinomialSeries.lean` and `CollectedPointwise.lean`: the finite
  shifts needed to collect equal powers of $s^2$, and their exact pointwise
  sum as the paired rational kernel.
- `Coefficients.lean` and `SeriesCoefficients.lean`: the initial coefficients,
  positive tail, and a proof that the coefficients derived from the paired
  kernel equal the advertised $Q_m$ for every $m$.
- `Moments.lean` and `MomentRecurrence.lean`: exact evaluations of
  $M_1,M_2,M_3$, the recurrence
  $(2j+1)M_j=(2j+15)M_{j+1}$, and positivity of every $M_j$.
- `SeriesCertificate.lean`: conditional only on summability, the formal
  series is at least $M_1(1489/5610)>0$.
- `IntegratedCoefficients.lean` and `CollectedIntegration.lean`: the
  coefficient-by-coefficient integral identity, dominated-convergence
  assembly, and the unconditional analytic theorem
  $$
  I_{13}(s)=\sum_{m=0}^{\infty}M_{m+1}Q_m(s^2)^m
  \ge M_1\frac{1489}{5610}>0
  \qquad (|s|<1).
  $$
  The corresponding Lean declarations are
  `hasSum_seriesTerm13_sq_eq_I13`, `I13_eq_seriesSum13_sq`,
  `certificate_le_I13`, and `I13_pos`.
- `QuadraticBounds.lean`: pairing and algebraic monotonicity of the two
  quadratic kernels, exact endpoint-polynomial integration, and
  $$
  \mathcal J_4(s)\le\frac{256}{165},\qquad
  \mathcal J_6(s)\le\frac{64}{9},\qquad
  \mathcal J_4(s)+\frac{15}{4}\frac{18}{55}\mathcal J_6(s)
  \le\frac{1696}{165}.
  $$
  These are `integral_quadraticKernel4_le`,
  `integral_quadraticKernel6_le`, and `n13_quadratic_integrals_le`.
- `Reduced.lean`: the exact $n=13$ formulas for $B_g,C_g,B_\theta,C_\theta$,
  the pointwise and integrated bound
  $$
  C_\theta(s)\le
  K_a(1-s^2)^2\frac{1696}{165},
  $$
  and the ratio-free strict inequality
  $$
  2\varepsilon B_\theta(s)+\varepsilon^2C_\theta(s)<0.
  $$
  `reducedRiskDifference13_neg_of_epsilon` proves this for every positive
  $\varepsilon$ below the certified uniform threshold, and
  `reducedRiskDifference13_neg` specializes it to
  $\varepsilon=1/2000$.
- `GammaMoments.lean`: the Mellin moment formula for Mathlib's gamma
  distribution, including integrability, and the five exact values
  $$
  E[V]=1,\quad E[V^2]=3,\quad E[V^3]=15,\qquad
  E[L^{-1}]=\frac1{22},\quad E[L^{-2}]=\frac1{440}.
  $$
- `BetaBridge.lean`: the exact centered pushforward of `Beta(6,6)`,
  $$
  \int f(p)\,d\operatorname{Beta}(6,6)(p)
  =\frac{693}{512}\int_{-1}^{1}
    f\!\left(\frac{1+x}{2}\right)(1-x^2)^5\,dx,
  $$
  and its two specializations to the linear and quadratic canonical
  integrands.
- `CanonicalProduct.lean`: factorization of the mixed moments using
  independence, integrability of the full linear and quadratic risk
  integrands, and construction of `CanonicalMomentBridge13` from the gamma
  laws.
- `CanonicalLaws.lean`: automatic integrability of all five rational
  $P$-factors under the beta law and the law-only theorem
  `canonicalMomentBridge13_of_component_laws`.  Its corollary
  `canonicalNormalizedRiskDifference13_neg_of_component_laws` proves the
  strict normalized risk inequality assuming only
  $$
  P\sim\operatorname{Beta}(6,6),\quad
  L\sim\operatorname{Gamma}(12,\tfrac12),\quad
  V\sim\operatorname{Gamma}(\tfrac12,\tfrac12),
  $$
  together with $P\perp(L,V)$ and $V\perp L$.
- `Canonical.lean` and `CanonicalClipping.lean`: conversion of the two
  canonical expectations to the reduced coefficients, scaling to ordinary
  squared risk, and the theorem that clipping the perturbed weight to
  $[0,1]$ preserves strict improvement.
- `CanonicalSummary.lean`: the estimator-level theorem
  `canonicalClippedEstimatorRiskDifference13_neg_of_summary_laws`.  From the
  three component laws, their required independence, and a measurable
  square-integrable mean-zero centered error independent of $(D,P,L)$, it
  derives every cross-term and individual-risk integrability obligation and
  concludes strict risk improvement for the clipped estimator.
- `NormalSquare.lean`: the exact pushforward
  $Z^2\sim\operatorname{Gamma}(1/2,1/2)$ for a standard normal, common-rate
  gamma convolution and finite-sum laws, and the
  $\operatorname{Gamma}(6,1/2)$ law for a sum of twelve independent
  standard-normal squares.
- `BetaGamma.lean`: the two-dimensional change of variables
  $(p,\ell)\mapsto(p\ell,(1-p)\ell)$, including its Jacobian, and the exact
  theorem that two independent $\operatorname{Gamma}(6,1/2)$ variables give
  an independent
  $P\sim\operatorname{Beta}(6,6)$ and
  $L\sim\operatorname{Gamma}(12,1/2)$.
- `NormalSample.lean` and `Cochran13.lean`: the raw two-sample normal model,
  sample-mean and mean-difference laws, Gaussian mean/residual block
  independence, the twelve-dimensional residual-hyperplane decomposition,
  and
  $$
  \frac{\operatorname{RSS}_g}{\sigma_g^2}
  =\frac{12S_g^2}{\sigma_g^2}
  \sim\operatorname{Gamma}(6,\tfrac12).
  $$
- `GaussianMeanBridge.lean`, `SummaryTransform.lean`, and
  `RawNormalSummary.lean`: the squared standardized mean-difference law,
  centered-error moments, beta–gamma independence transport, and the direct
  theorem `rawNormalSummaryLaws13_of_normal_samples`.  The latter derives the
  component laws and genuine four-way mutual independence of $(C,D,P,L)$
  from the raw samples.
- `RawRiskBridge.lean`: the theorem
  `canonicalClippedEstimatorRiskDifference13_neg_of_raw_normal`, which
  combines the raw-sample laws with the completed analytic argument and
  proves strict risk improvement for the corresponding canonical
  expressions.
- `RawPositivity.lean`: strict positivity almost everywhere of each scaled
  residual sum, residual sum of squares, and sample variance.  In particular,
  it proves
  $$
  S_1^2+S_2^2>0
  $$
  almost everywhere, together with nonvanishing of every denominator used
  by the canonical coordinates.
- `RawEstimatorCoordinates.lean`: literal definitions of the ordinary
  Graybill--Deal estimator and its clipped perturbation, followed by exact
  pointwise identification of `canonicalR`, `canonicalQ13`, the clipped
  weight, and both full estimator expressions whenever the denominators are
  nonzero.
- `RawEstimatorRisk.lean`: almost-everywhere transport of those pointwise
  identities and the final theorem
  `rawGraybillDealEstimator13_strictly_dominated`, with both estimators
  expanded directly in terms of the two sample means and sample variances.

All checked modules contain no `sorry` declarations or custom axioms.

## Generalization to every equal sample size $n\geq10$

Write $\nu=n-1$, so the target range is $\nu\geq9$.  The following generic
pieces now compile:

- `GeneralAnalytic.lean` proves the first-three-term certificate
  $L_\nu(z)>0$ for every natural $\nu\geq9$ and $0\leq z\leq1$, both in
  residual-df and sample-size form.  It also constructs a positive
  sample-size-dependent perturbation once the generalized linear and
  quadratic integral bounds are supplied.
- `GeneralMoments.lean`, `GeneralCoefficients.lean`, and
  `GeneralSeriesCoefficients.lean` prove the beta-moment recurrence
  $$
  (2j+1)M_{\nu,j}=(2j+\nu+3)M_{\nu,j+1},
  $$
  derive the first three coefficient/moment products, assemble the five
  positive tail polynomials, and prove that the coefficients obtained from
  the paired kernel equal the advertised closed sequence for every index.
- `GeneralSeriesCertificate.lean` proves, conditional only on summability,
  that the generalized formal series is strictly positive.
- `GeneralKernel.lean` and `GeneralIntegralPairing.lean` prove the exact
  $x/-x$ identity with the real-power factor $(1-x^2)^{\nu/2}$ and lift it
  to the symmetric integral $I_\nu(s)$.
- `GeneralMomentIntegral.lean` identifies the beta-defined moment with
  $$
  M_{\nu,j}=\int_0^1x^{2j}(1-x^2)^{\nu/2}\,dx,
  $$
  including the real-power endpoint and integrability facts.
- `GeneralSeriesIntegration.lean`, `GeneralCollectedPointwise.lean`, and
  `GeneralCollectedBounds.lean` establish the pointwise negative-binomial
  expansion, exact target-power collection, and the summable uniform
  majorant
  $$
  65\binom{m+4}{4}(s^2)^m.
  $$
- `GeneralIntegratedCoefficients.lean`,
  `GeneralCollectedIntegration.lean`, and
  `GeneralCentralAnalytic.lean` prove
  $$
  I_\nu(s)
    =\sum_{m=0}^{\infty}M_{\nu,m+1}Q_{\nu,m}(s^2)^m
    \ge M_{\nu,1}L_\nu(s^2)>0
  $$
  for every natural $\nu\geq9$ and $|s|<1$.  The declarations
  `general_certificate_le_generalI_sampleSize` and
  `generalI_pos_sampleSize` state the result directly for every equal
  sample size $n\geq10$.
- `GeneralQuadratic.lean` proves the parameter-generic pointwise quadratic
  bound by the two kernels whose endpoint integrals give $J_4$ and $J_6$.
- `GeneralQuadraticEndpoint4.lean` and
  `GeneralQuadraticEndpoint6.lean` evaluate those endpoint integrals:
  $$
  J_4(\nu)=2^{\nu-1}B(\nu/2+2,\nu/2-2),\qquad
  J_6(\nu)=2^{\nu-3}B(\nu/2+2,\nu/2-4).
  $$
  They also prove that these values uniformly bound the corresponding
  kernels for every $\nu\geq9$ and $|s|<1$.  The $J_6$ proof includes the
  integrable endpoint singularity at $\nu=9$.
- `GeneralReduced.lean` and `GeneralQuadraticBounds.lean` combine the
  endpoint values into
  $$
  H_\nu=J_4(\nu)
    +\frac{15\nu^2}{16(\nu-1)(\nu-2)}J_6(\nu)
  $$
  and prove that, for every natural $\nu\geq9$ and every positive
  normalizing constant $K_a$, there is a single $\varepsilon_\nu>0$ such
  that
  $$
  2\varepsilon_\nu B_\theta(s)
    +\varepsilon_\nu^2C_\theta(s)<0
  \qquad\text{for every }|s|<1.
  $$
- `GeneralBetaBridge.lean`, `GeneralCanonicalAlgebra.lean`, and
  `GeneralCanonicalProduct.lean` prove the arbitrary-shape centered-beta
  formula and the generic product-moment reductions.  In particular,
  $$
  E[V^2/L]=\frac{3}{2(\nu-1)},\qquad
  E[V^3/L^2]=\frac{15}{4(\nu-1)(\nu-2)}.
  $$
- `GeneralCanonical.lean`, `GeneralCanonicalClipping.lean`, and
  `GeneralCanonicalLaws.lean` connect the reduced inequality to normalized
  squared risk.  The law-only theorem
  `exists_generalCanonicalRisk_epsilon_of_component_laws` assumes exactly
  $$
  P\sim\operatorname{Beta}(\nu/2,\nu/2),\quad
  L\sim\operatorname{Gamma}(\nu,1/2),\quad
  V\sim\operatorname{Gamma}(1/2,1/2),
  $$
  together with $P\perp(L,V)$ and $V\perp L$, and returns one positive
  $\varepsilon_\nu$ whose normalized risk difference is negative
  simultaneously for all $|s|<1$.
- `GeneralGammaMoments.lean` proves
  $$
  E[L^{-1}]=\frac1{2(\nu-1)},\qquad
  E[L^{-2}]=\frac1{4(\nu-1)(\nu-2)}
  $$
  for $L\sim\operatorname{Gamma}(\nu,\tfrac12)$, including integrability.
- `GeneralBetaGamma.lean` proves for arbitrary admissible shape $a$ and
  rate $r$ that two independent $\operatorname{Gamma}(a,r)$ variables
  yield an independent beta ratio and gamma sum.
- `GeneralNormalSample.lean` parameterizes each raw sample by
  `Fin (ν + 1)` and proves the generic sample-mean and mean-difference laws,
  mean/residual independence, residual-sum independence, and Cochran law
  $$
  \operatorname{RSS}_g/\sigma_g^2
    \sim\operatorname{Gamma}(\nu/2,\tfrac12).
  $$
- `GeneralGaussianMeanBridge.lean` proves the generic standardized
  mean-difference law
  $$
  \frac{(\nu+1)D^2}{\sigma_1^2+\sigma_2^2}
    \sim\operatorname{Gamma}(1/2,1/2),
  $$
  its first three integrability consequences, and independence from the
  pair of (raw or variance-scaled) residual sums of squares.
- `GeneralGraybillDealEpsilon.lean` chooses, for each $\nu\geq9$, a fixed
  coefficient
  $$
  \varepsilon_\nu=\texttt{generalGraybillDealEpsilon }\nu>0
  $$
  from the uniform reduced-risk theorem.  It depends only on $\nu$, not on
  $\mu$ or either population variance, and its certified reduced-risk
  inequality holds simultaneously for every $|s|<1$.
- `GeneralCanonicalSummary.lean` packages the generic component laws,
  clipping, finite-risk obligations, centered-error orthogonality, and the
  fixed $\varepsilon_\nu$ into an estimator-level strict-risk theorem.  Its
  `iIndepFun` wrapper is the interface used by the raw normal-sample proof.
- `GeneralSummaryTransform.lean`, `GeneralSummaryIndependence.lean`, and
  `GeneralRawNormalSummary.lean` assemble the generic beta and gamma laws,
  centered-error moments, and genuine four-way mutual independence of
  $(C,D,P,L)$ directly from the two raw normal samples.
- `GeneralRawCoordinates.lean` and `GeneralRawPositivity.lean` prove the
  arbitrary-$\nu$ coordinate identities and almost-everywhere positivity
  of each sample variance, their sum, and the canonical residual coordinate
  $L$.
- `GeneralRawEstimatorCoordinates.lean` and
  `GeneralRawEstimatorAE.lean` identify the canonical base and clipped
  estimator expressions almost everywhere with the literal
  Graybill–Deal estimator and its literal clipped perturbation.
- `GeneralRawRiskBridge.lean` combines the raw summary laws with the
  canonical fixed-coefficient theorem.
  `GeneralRawEstimatorRisk.lean` completes the almost-everywhere risk
  transport and proves
  `rawGraybillDealEstimatorN_strictly_dominated`.

Thus the analytic theorem, quadratic endpoint bounds, ratio-free reduced
comparison, raw probability-law assembly, and almost-everywhere transport
to the literal estimators are complete for every equal sample size
$n\geq10$.  The coefficient supplied by the generic theorem depends on
$n$; the formalization does not assert that the explicit $1/2000$ used at
$n=13$ works uniformly over all sample sizes.

## Final theorems

### Every equal sample size $n\geq10$

Let $\nu=n-1\geq9$.  For two independent measurable samples of size
$\nu+1$ from $N(\mu,\sigma_i^2)$ with $\sigma_i^2>0$, put

$$
D=\bar X_2-\bar X_1,\qquad
r=\frac{S_1^2}{S_1^2+S_2^2},\qquad
q=\frac{(\nu+1)D^2}{S_1^2+S_2^2}.
$$

The formalization fixes a number $\varepsilon_\nu>0$ depending only on
$\nu$ and defines

$$
w_\nu=\operatorname{clip}_{[0,1]}
  \left(r+\varepsilon_\nu r(1-r)(1-2r)(4-q)\right).
$$

The declaration `rawGraybillDealEstimatorN_strictly_dominated` proves

$$
R(\mu,\bar X_1+w_\nu D)
<
R(\mu,\bar X_1+rD)
$$

for every common mean and every pair of positive population variances in
the formalized two-sample normal model.  Consequently, for every fixed
equal sample size $n\geq10$, the ordinary Graybill–Deal estimator is
inadmissible under squared-error loss in that model.  This all-$n$ theorem
is an equal-size result; the separate fixed unequal-size theorem below
covers $(n_1,n_2)=(13,17)$.  No result here covers equal sizes below ten.

### Explicit $n=13$ theorem

For two independent measurable samples of size thirteen from
$N(\mu,\sigma_i^2)$ with $\sigma_i^2>0$, put

$$
D=\bar X_2-\bar X_1,\qquad
r=\frac{S_1^2}{S_1^2+S_2^2},\qquad
q=\frac{13D^2}{S_1^2+S_2^2},
$$

and

$$
w_*=\operatorname{clip}_{[0,1]}
  \left(r+\frac1{2000}r(1-r)(1-2r)(4-q)\right).
$$

The declaration `rawGraybillDealEstimator13_strictly_dominated` proves

$$
R(\mu,\bar X_1+w_*D)
<
R(\mu,\bar X_1+rD)
$$

for every $\mu\in\mathbb R$ and every pair of positive population
variances.  Thus the fixed-$n=13$ construction is a machine-checked
counterexample to admissibility of the Graybill--Deal estimator under the
formalized model.

### Explicit unequal-size $(13,17)$ theorem

For independent measurable normal samples of sizes $13$ and $17$, define

$$
D=\bar Y-\bar X,\qquad
A_1=\frac{S_1^2}{13},\qquad
A_2=\frac{S_2^2}{17},
$$

$$
r=\frac{A_1}{A_1+A_2},\qquad
q=\frac{D^2}{A_1+A_2},
$$

and

$$
\phi(r)=r(1-r)
\left(\frac37-r+\frac{1045}{5439}r(1-r)\right).
$$

The fixed competitor is

$$
\widehat\mu_*=
\bar X+
\operatorname{clip}_{[0,1]}
\left[
r+\frac1{2{,}000{,}000}\,
\phi(r)\left(\frac{601}{182}-q\right)
\right]D.
$$

The declaration `rawGraybillDealEstimator13_17_strictly_dominated`
proves

$$
R_{\mu,\sigma_1^2,\sigma_2^2}(\widehat\mu_*)
<
R_{\mu,\sigma_1^2,\sigma_2^2}
  \left(\bar X+rD\right)
$$

for every $\mu\in\mathbb R$ and every
$\sigma_1^2,\sigma_2^2>0$ in the raw two-sample normal model.  The same
numerical perturbation coefficient is used for every variance ratio.

The unequal proof is split across the `UnequalDamped*.lean` modules:
the exact one-sided series certificate, the two global beta charts, the
canonical product-law bridge, the estimator-level integrability and
orthogonality bridge, and the almost-everywhere transport to the literal
estimators.  `UnequalDampedAxiomAudit.lean` records that the final theorem
uses only Lean/Mathlib's standard `propext`, `Classical.choice`, and
`Quot.sound` axioms; the project contains no added axiom or proof
placeholder in this chain.

The direct raw-sample theorems currently take the standard explicit
regularity hypothesis `∀ g i, Measurable (X g i)`.  The `HasLaw` fields in
the model provide only almost-everywhere measurability, so retaining this
hypothesis keeps the independence transport stated for the original
coordinate functions rather than measurable modifications.

### Fixed-difference-four unequal family: raw-estimator dominance theorem

There is now also a machine-checked reduced analytic certificate for the
infinite unequal-size family

$$
(n_1,n_2)=(2m-1,2m+3),\qquad m\geq7.
$$

The `UnequalFixedDifferenceFour*.lean` modules prove the exact asymmetric
Beta moment formulas, identify every integrated series coefficient with its
certified negative coefficient (including the six exceptional head
coefficients), evaluate the inverse-Beta quadratic envelopes, and assemble
one sample-size-dependent coefficient
`unequalFixedDifferenceFourEpsilon m` for which

$$
2\varepsilon_m B_\pm(m,s)+\varepsilon_m^2 C_\pm(m,s)<0,
\qquad 0\leq s<1,
$$

on both variance-ratio charts.  The reduced declarations are
`unequalFixedDifferenceFourPlusReducedRisk_neg` and
`unequalFixedDifferenceFourMinusReducedRisk_neg`.

The formalization also derives the asymmetric Beta/Gamma component laws
from the two raw normal samples, proves the required independence and
integrability statements, and identifies the canonical estimators almost
everywhere with the literal sample-mean/sample-variance formulas.  The
declaration
`unequalFixedDifferenceFourRawClippedPerturbedEstimator_sqRisk_lt_rawGraybillDealEstimator`
therefore proves, for every $m\geq7$ and every pair of positive population
variances, that the clipped perturbation with coefficient
`unequalFixedDifferenceFourEpsilon m` has strictly smaller squared-error
risk than the ordinary Graybill--Deal estimator.  Thus every member of the
family $(2m-1,2m+3)$ is formally supplied with a fixed strict dominator;
the perturbation depends on the known sample sizes but not on the unknown
mean or variances.

The next extension targets the full diagonal

$$
(n_1,n_2)=(n,n+4),\qquad n\geq13.
$$

Writing $m=(n+1)/2$ reduces this to the same certificate for real
$m\geq7$; even $n$ corresponds to half-integral $m$.  The new modules
`UnequalFixedDifferenceFourRealAlgebra.lean` and
`UnequalFixedDifferenceFourRealMoments.lean`,
`UnequalFixedDifferenceFourRealSeriesSign.lean`, and
`UnequalFixedDifferenceFourAllNAlgebra.lean` already machine-check the
real-parameter algebraic endgame, exact real-shape Beta moments, interval
moment identities, and strict negativity of every coefficient in both
one-sided series.  The sample-size wrapper also verifies the first missing
parameter $m=15/2$ for $(14,18)$ and its exact perturbation coefficient.
The modules `UnequalFixedDifferenceFourRealSeriesBridge.lean`,
`UnequalFixedDifferenceFourRealCollectedAlgebra.lean`,
`UnequalFixedDifferenceFourRealEnvelopeIntegrals.lean`, and
`UnequalFixedDifferenceFourRealReduced.lean` now go further: they identify
every integrated coefficient with its certified negative coefficient,
evaluate both inverse-Beta quadratic envelopes, and prove

$$
2\varepsilon_m B_\pm(m,s)+\varepsilon_m^2C_\pm(m,s)<0
$$

for every real $m\geq7$ and $0\leq s<1$.  Thus the entire two-chart reduced
analytic certificate covers every integer and half-integer parameter.

The modules `UnequalFixedDifferenceFourRealCanonical.lean` and
`UnequalFixedDifferenceFourRealCanonicalReduced.lean` now also transport
those two charts to the direct canonical beta coordinate.  In particular,
`unequalFixedDifferenceFourRealCanonicalReducedRisk_neg` proves

$$
2\varepsilon_m B_{\mathrm{can}}(m,\theta)
  +\varepsilon_m^2 C_{\mathrm{can}}(m,\theta)<0
$$

for every real $m\geq7$ and every interior oracle weight
$0<\theta<1$.  This closes the direct real-$m$ canonical reduced-risk
bridge, including both sides of the beta pivot.

The modules
`UnequalFixedDifferenceFourRealCanonicalProduct.lean`,
`UnequalFixedDifferenceFourRealCanonicalLaws.lean`, and
`UnequalFixedDifferenceFourRealCanonicalSummary.lean` now close the
product-moment, component-law, and estimator-summary layers as well.
Under the stated Beta/Gamma laws, independence and measurability
hypotheses, and the square-integrability and mean-zero hypotheses on the
centered error, the theorem
`unequalFixedDifferenceFourRealCanonicalClippedEstimatorRiskDifference_neg_of_summary_laws`
proves strict clipped squared-risk improvement for every real $m\geq7$.

The natural-number-indexed raw layer uses

$$
m_n=\frac{n+1}{2},\qquad
\nu_1=n-1,\qquad \nu_2=n+3.
$$

The exact size lemmas
`unequalFixedDifferenceFourAllNResidualDF1_add_one` and
`unequalFixedDifferenceFourAllNResidualDF2_add_one` state

$$
\nu_1+1=n,\qquad \nu_2+1=n+4.
$$

Thus the internal residual-DF indexing really represents raw samples of
sizes $n$ and $n+4$.  The corresponding summary module derives the
$\operatorname{Beta}(m_n-1,m_n+1)$ and
$\Gamma(2m_n,1/2)$ laws without imposing a parity condition: odd $n$ gives
integral $m_n$, while even $n$ gives half-integral $m_n$.

The final declaration is
`unequalFixedDifferenceFourAllNRawClippedPerturbedEstimator_sqRisk_lt_rawGraybillDealEstimator`.
For every natural $n\geq13$, it has the schematic conclusion

```lean
sqRisk μ
    (unequalFixedDifferenceFourAllNRawClippedPerturbedEstimator
      (unequalFixedDifferenceFourRealEpsilon
        (unequalFixedDifferenceFourSampleM n))
      n X Y) P
  <
sqRisk μ
    (unequalFixedDifferenceFourAllNRawGraybillDealEstimator
      n X Y) P
```

under the stated `TwoNormalSamplesU` model, measurability of the sample
coordinates, and strictly positive population variances.  Its coefficient

$$
\varepsilon_n
=
\operatorname{unequalFixedDifferenceFourRealEpsilon}
  \left(\frac{n+1}{2}\right)
$$

depends only on the known sample size $n$, not on the common mean, the
population variances, or the observations.

This all-$n$ literal raw-estimator theorem is machine-checked: the
all-$n$ almost-everywhere coordinate module, final raw-risk module, and
aggregate 3337-job build all pass.  The axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.  The statement is only for
the positive-variance two-sample normal model just described; no assertion
is made here for zero variances or for other sampling models.

## Universal sample-size program

The `Universal*.lean` modules develop a separate nonconstructive route
intended to cover every pair of sample sizes \(n_1,n_2\geq2\).  The
analytic posterior-identity contradiction, the exact two-normal-sample
component laws, the \(D^2\)-tilted Gamma law, the full positive-coordinate
Jacobian calculation, and the raw-to-reduced density pushforward are now
machine checked for arbitrary positive residual shapes.  In particular,
`UniversalRawDensityIdentity.lean` removes the former component-density
hypothesis, and `UniversalRawLawUnconditional.lean` assembles the raw
normal-sample theorem.

The v24 Hilbert-space route now discharges the continuous-experiment
complete-class statement.  Its main steps are finite-grid supporting
positive priors, compact finite intersections in the clipped weak
`L²` action set, strict-midpoint identification of the global closure
dominator, weak-to-strong convergence at the anchor model, and direct
almost-everywhere subsequence extraction.

The final theorem is
`universalRawGraybillDeal_not_admissible`.  For every pair of positive
residual degrees of freedom (equivalently every pair of sample sizes at
least two), it produces the failure of universal measurable
admissibility for the literal raw Graybill--Deal estimator under the
two-independent-normal-sample family hypotheses.  The companion theorem
`exists_universalRaw_dominator` explicitly supplies a measurable reduced
rule whose induced raw estimator weakly improves risk everywhere and
strictly improves it somewhere.  No complete-class or density-law
hypothesis remains.

The strengthened entry point
`universalRawGraybillDeal_not_admissible_among_all_measurableEstimators`
states the result in the ordinary decision class of all measurable
raw-sample estimators.  Its concrete witness is exposed by
`exists_universalRaw_measurableEstimator_dominator`.

The aggregate 3444-job build passes on Lean/Mathlib v4.32.0.  The final
axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
the source contains no `sorry`, `admit`, or project-defined axioms.  See
`V24_COMPLETION_STATUS.md` and `UNIVERSAL_FORMALIZATION_STATUS.md`.

To build:

```sh
lake update
lake exe cache get
lake build
```

The pinned versions are recorded in `lean-toolchain`, `lakefile.lean`, and
`lake-manifest.json`.
