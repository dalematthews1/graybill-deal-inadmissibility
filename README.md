# A machine-checked counterexample to admissibility of the Graybill–Deal estimator

This repository contains a complete Lean 4 formalization of the following
theorem: for **every equal sample size $n \ge 10$**, there is a fixed
coefficient $\varepsilon_n > 0$, depending only on $n$, such that for two
independent samples of size $n$ from $N(\mu, \sigma_1^2)$ and
$N(\mu, \sigma_2^2)$ with a common mean and positive variances, the
explicit clipped estimator

$$
\hat\mu_* = \bar X_1 + w_* D,
\qquad
w_* = \operatorname{clip}_{[0,1]}
  \Bigl(r + \varepsilon_n\, r(1-r)(1-2r)(4-q)\Bigr),
$$

with $D = \bar X_2 - \bar X_1$, $r = S_1^2/(S_1^2+S_2^2)$, and
$q = n\,D^2/(S_1^2+S_2^2)$, has strictly smaller squared-error risk than
the Graybill–Deal estimator $\hat\mu_{\mathrm{GD}} = \bar X_1 + rD$ at
**every** parameter point $(\mu, \sigma_1^2, \sigma_2^2)$. The
Graybill–Deal estimator is therefore inadmissible under squared-error
loss for every equal sample size $n \ge 10$.

For $n = 13$ the formalization additionally provides the fully explicit
construction with $\varepsilon = 1/2000$. For general $n$ the coefficient
$\varepsilon_n$ is a chosen (noncomputable) witness of the certified
uniform bound; it is fixed **before** the population parameters are
quantified, as inadmissibility requires.

Because the weight $w_*$ depends on the data through $q$ (hence through
$D^2$), the competitor lies outside the class
$\bar X_1 + D\,\varphi(S_1^2, S_2^2)$ in which Duanmu, Roy, and
Schrittesser ([arXiv:2112.14257](https://arxiv.org/abs/2112.14257),
Corollary 5.3) proved the Graybill–Deal estimator admissible; there is no
contradiction. The general admissibility of the Graybill–Deal estimator
was a long-standing open question, which this construction settles in the
negative. Unequal sample sizes and equal sample sizes $n \le 9$ remain
open.

The mathematical write-up is in
[`paper/graybill_deal_reader_edition.pdf`](paper/graybill_deal_reader_edition.pdf).

## How to verify

Install [elan](https://github.com/leanprover/elan), then:

```sh
lake exe cache get   # fetch prebuilt mathlib (no compilation of mathlib needed)
lake build           # compiles all modules; must finish with no errors or sorries
```

`lake build` also compiles the three audit files. To see their output
directly:

```sh
lake env lean CheckAxioms.lean
```

expected output — every listed theorem depends on the three standard
axioms of Lean/mathlib and nothing else (in particular no `sorryAx`, no
custom axioms, no `Lean.ofReduceBool` from `native_decide`):

```
'GraybillDeal.rawGraybillDealEstimatorN_strictly_dominated' depends on axioms:
[propext, Classical.choice, Quot.sound]
...
```

```sh
lake env lean ModelWitness.lean
lake env lean ModelWitnessGeneral.lean
```

compile concrete witnesses of the model hypotheses (the product of the
$2n$ Gaussian laws on `(Fin 2 × Fin (ν+1)) → ℝ`), so the final theorems
are not vacuously true about an empty model.

Do **not** run `lake update`: it would re-resolve dependencies away from
the pinned mathlib commit recorded in `lake-manifest.json`.

## What to read: the trusted surface

The Lean kernel guarantees every proof step, so a human reviewer only
needs to check that the *statements* say what is claimed. That trusted
surface is small:

- [`GraybillDeal/GeneralRawEstimatorRisk.lean`](GraybillDeal/GeneralRawEstimatorRisk.lean) —
  the all-$n$ theorem `rawGraybillDealEstimatorN_strictly_dominated`, with
  both estimators written literally in terms of sample means and sample
  variances.
- [`GraybillDeal/RawEstimatorRisk.lean`](GraybillDeal/RawEstimatorRisk.lean) —
  the explicit $n = 13$, $\varepsilon = 1/2000$ theorem
  `rawGraybillDealEstimator13_strictly_dominated`.
- [`GraybillDeal/GeneralNormalSample.lean`](GraybillDeal/GeneralNormalSample.lean)
  and [`GraybillDeal/NormalSample.lean`](GraybillDeal/NormalSample.lean) —
  the models: all $2n$ observations mutually independent (`iIndepFun`),
  each with law `gaussianReal μ (variance g)` (mathlib's `gaussianReal` is
  parametrized by the **variance**); sample mean, unbiased sample variance
  (divisor $n-1$), and mean difference.
- [`GraybillDeal/GeneralGraybillDealEpsilon.lean`](GraybillDeal/GeneralGraybillDealEpsilon.lean) —
  the fixed coefficient $\varepsilon_\nu$: chosen from the certified
  uniform bound as a function of $\nu$ alone, with its positivity and
  uniform risk-negativity specifications.
- [`GraybillDeal/Risk.lean`](GraybillDeal/Risk.lean) — `sqRisk` is the
  Bochner integral `∫ (estimator ω - μ)^2 ∂P`. (Lean's convention that a
  non-integrable Bochner integral equals 0 cannot manufacture a *strict*
  inequality, so no integrability escape hatch exists.)
- [`GraybillDeal/Elementary.lean`](GraybillDeal/Elementary.lean) —
  `clip01 x = min 1 (max 0 x)`.
- [`GraybillDeal/Reduced.lean`](GraybillDeal/Reduced.lean) —
  `epsilon13 = 1/2000`.

The final theorems take only the model, measurability of the
observations, and positivity of the two variances as hypotheses; every
integrability and orthogonality obligation is discharged inside the
proofs.

## Repository layout

```
lean-toolchain, lakefile.lean, lake-manifest.json
                          pinned Lean 4.32.0 + mathlib v4.32.0
GraybillDeal.lean         root module importing all 81 proof modules
GraybillDeal/             the formalization (see module guide below)
CheckAxioms.lean          axiom audit for the final theorems
ModelWitness.lean         non-vacuity witness, n = 13 model
ModelWitnessGeneral.lean  non-vacuity witness, general model (every ν)
paper/                    the mathematical write-up (PDF)
numerics/                 independent numerical/symbolic cross-checks (Python)
```

## Independent numerical cross-checks (no Lean required)

For readers who want to sanity-check the mathematics without running Lean,
`numerics/` contains three self-contained scripts
(`pip install numpy scipy sympy`):

- `check_symbolic.py` — recomputes, in exact rational arithmetic and
  directly from the integral representation, every constant of the paper's
  certificate: the series coefficients $Q_0, Q_1, Q_2$, the tail-positivity
  formula, the moments $M_j$, the beta integrals $J_4, J_6$, and the final
  bound $23824/40585545 > 1/2000$, plus the general-$n$ claims
  (the $Q_m(\nu)$ and $D_j(\nu)$ formulas symbolically in $\nu$, and
  $\ell_\nu > 0$).
- `check_montecarlo.py` — paired Monte Carlo of the two risks from raw
  normal sampling (including one run from full 13-observation samples),
  plus an independent quadrature of the exact risk-difference formulas.
  The dominance shows up at every tested parameter point with z-scores
  above 70.
- `verify_gd_counterexample.py` — the paper's own check: exact fractions
  of the certificate and a deterministic generalized Gauss–Laguerre
  evaluation of the three-dimensional risk integral over a parameter grid.

## Module guide


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
inadmissible under squared-error loss in that model.  This theorem does not
cover unequal sample sizes or equal sample sizes below ten.

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

The direct raw-sample theorems currently take the standard explicit
regularity hypothesis `∀ g i, Measurable (X g i)`.  The `HasLaw` fields in
the model provide only almost-everywhere measurability, so retaining this
hypothesis keeps the independence transport stated for the original
coordinate functions rather than measurable modifications.

The pinned versions are recorded in `lean-toolchain`, `lakefile.lean`, and
`lake-manifest.json`.

## License

This project is licensed under the Apache License, Version 2.0 — see
[LICENSE](LICENSE).
