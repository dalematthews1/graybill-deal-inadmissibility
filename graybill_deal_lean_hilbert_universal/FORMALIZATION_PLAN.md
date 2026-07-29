# Lean formalization plan for the Graybill–Deal counterexample

## Assessment

The project began with the fixed-$n=13$ counterexample and now proves the
corresponding strict dominance result for every equal sample size
$n\geq10$.  The novel part of the argument—the one-dimensional analytic
inequality and its exact certificate—is well suited to formalization.  The
expensive part was connecting that reduced calculation to raw normal
observations: Mathlib had the constituent measure-theoretic tools, but did
not package the sample-mean/sample-variance decomposition, Cochran's
theorem, or the beta–gamma transformation in the form needed here.

The proof was therefore split into two independently useful layers:

1. a machine-checked strict-risk inequality under a canonical joint law for
   the sufficient statistics;
2. a theorem showing that the sufficient statistics from two independent
   normal samples have that joint law.

The first theorem checks the novel counterexample. The second formalizes the
standard distribution theory needed to transfer it back to the original
statistical model.

## Current machine-checked milestone

The following part of the reduced fixed-$n=13$ proof now compiles:

1. clipping and pointwise perturbation identities;
2. the integral-level risk-difference identity under explicit integrability
   and zero-cross-term hypotheses;
3. the $(s,x)$ coordinate change and all rational denominator identities;
4. the exact $x/-x$ paired kernel identity and symmetric interval pairing;
5. the binomial geometric expansion of $(1-s^2x^2)^{-5}$ for
   $|s|<1$, $|x|\leq1$;
6. exact evaluation of $M_1,M_2,M_3$;
7. derivation of every $Q_m$ from the paired numerator, including equality
   with the positive closed tail formula;
8. the shifted-series reindexing and collection of equal powers of $s^2$;
9. dominated convergence under the summable uniform majorant
   $60\binom{m+4}{4}(s^2)^m$;
10. the exact analytic identity and strict certificate
    $$
    I_{13}(s)=\sum_{m=0}^{\infty}M_{m+1}Q_m(s^2)^m
    \ge M_1\frac{1489}{5610}>0
    \qquad (|s|<1).
    $$
11. the uniform quadratic estimates
    $$
    \mathcal J_4(s)\le\frac{256}{165},\qquad
    \mathcal J_6(s)\le\frac{64}{9},
    $$
    and their fixed-$n=13$ combination
    $$
    \mathcal J_4(s)+\frac{15}{4}\frac{18}{55}\mathcal J_6(s)
    \le\frac{1696}{165}.
    $$
12. the exact reduced $B_g,C_g,B_\theta,C_\theta$ definitions, the
    $C_\theta$ upper bound, and the division-free strict comparison
    $$
    2\varepsilon B_\theta+\varepsilon^2C_\theta<0
    $$
    for every positive $\varepsilon$ below the uniform threshold, in
    particular $\varepsilon=1/2000$.
13. the general gamma Mellin-moment formula and the five exact
    $V,L$ moments needed at $n=13$, with integrability;
14. the exact centered `Beta(6,6)` pushforward formula with normalizing
    constant $693/512$;
15. the two independence-based mixed-moment reductions, automatic
    integrability of their rational beta factors, and the theorem
    `canonicalMomentBridge13_of_component_laws`;
16. the law-level strict inequality
    `canonicalNormalizedRiskDifference13_neg_of_component_laws`, clipping,
    and the fully packaged estimator theorem
    `canonicalClippedEstimatorRiskDifference13_neg_of_summary_laws`, which
    derives the cross-term and finite-risk obligations from a
    square-integrable mean-zero centered error independent of $(D,P,L)$.
17. the exact standard-normal square law, finite common-rate gamma
    additivity, and the beta–gamma ratio/sum change of variables;
18. the two-sample Gaussian mean/residual decomposition, including
    mean–residual block independence and the fixed-size Cochran theorem
    $$
    \operatorname{RSS}_g/\sigma_g^2
      \sim\operatorname{Gamma}(6,\tfrac12);
    $$
19. the raw component-law theorem
    `rawNormalSummaryLaws13_of_normal_samples`, including genuine mutual
    independence of the four summaries $(C,D,P,L)$;
20. the strict canonical risk theorem
    `canonicalClippedEstimatorRiskDifference13_neg_of_raw_normal`, whose
    assumptions are now only the raw normal model, coordinate measurability,
    and positivity of both population variances.
21. almost-everywhere positivity of $S_1^2+S_2^2$, exact identification of
    all canonical coordinates with the literal raw sample formulas, and the
    final theorem `rawGraybillDealEstimator13_strictly_dominated`.
22. the complete residual-df-parameterized extension for every
    $\nu=n-1\geq9$: a coefficient $\varepsilon_\nu>0$ fixed by $\nu$ alone,
    generic raw summary-law assembly, almost-everywhere coordinate
    transport, and the final literal-estimator theorem
    `rawGraybillDealEstimatorN_strictly_dominated`.

There are no `sorry` declarations or custom axioms in these modules. The
analytic argument, probability-law bridge, almost-everywhere denominator
argument, and final raw-estimator identification are complete both for the
explicit $n=13$ construction and for every equal sample size $n\geq10$.

## Explicit $n=13$ end theorem

For two independent samples of size 13 from

$$
X_{ij}\sim N(\mu,\sigma_i^2),\qquad \sigma_i^2>0,
$$

define

$$
D=\bar X_2-\bar X_1,\qquad
r=\frac{S_1^2}{S_1^2+S_2^2},\qquad
q=\frac{13D^2}{S_1^2+S_2^2},
$$

and

$$
\widetilde w
=r+\frac1{2000}r(1-r)(1-2r)(4-q),\qquad
w_*=\operatorname{clip}_{[0,1]}(\widetilde w).
$$

The theorem proves that the estimator

$$
\delta_*=\bar X_1+w_*D
$$

has strictly smaller squared-error risk than the Graybill–Deal estimator

$$
\delta_{\mathrm{GD}}=\bar X_1+rD
$$

for every $\mu\in\mathbb R$ and $\sigma_1^2,\sigma_2^2>0$.

## File and theorem hierarchy

### 1. `Algebra.lean` and `Elementary.lean`

Status: implemented and compiled.

- Exact comparison
  $$
  \frac1{2000}<\frac{23824}{40585545}.
  $$
- Ratio-free final arithmetic comparison.
- Completed-square identity
  $$
  \frac4{11}-\frac{116}{187}z+\frac{3480}{3553}z^2
  =
  \frac{1489}{5610}
  +\frac{3480}{3553}\left(z-\frac{19}{60}\right)^2.
  $$
- Positivity of the $n=13$ tail numerator.
- Positivity of the five general-$\nu$ coefficient polynomials for
  $\nu\ge8$.

`Elementary.lean` now contains `clip01`, its interval lemmas, squared-error
contraction, the perturbation identity, and the corresponding weighted
estimator identity.

### 2. `Risk.lean`

Status: implemented and compiled.

Real-valued squared risk is defined with explicit integrability assumptions
on every summand used to distribute the integral. The compiled theorem
`sqRisk_weight_difference` gives the general orthogonality reduction:

```lean
theorem risk_diff_of_orthogonal
    (hcrossNew : ∫ ω, (T ω - μ) * D ω * (w ω - θ) ∂P = 0)
    (hcrossGD  : ∫ ω, (T ω - μ) * D ω * (r ω - θ) ∂P = 0)
    -- integrability hypotheses
    :
    sqRisk μ (fun ω => T ω + D ω * (w ω - θ)) P
      - sqRisk μ (fun ω => T ω + D ω * (r ω - θ)) P
    =
    ∫ ω, D ω ^ 2 *
      ((w ω - θ) ^ 2 - (r ω - θ) ^ 2) ∂P
```

Then prove the pointwise perturbation identity

$$
(r+\varepsilon h-\theta)^2-(r-\theta)^2
=2\varepsilon(r-\theta)h+\varepsilon^2h^2.
$$

### 3. `Coordinates.lean`

Status: implemented and compiled.

Use

$$
\theta(s)=\frac{1+s}{2},\qquad
d(s,x)=\frac{1+sx}{2},\qquad
r(s,x)=\frac{(1+s)(1+x)}{2(1+sx)}.
$$

For $|s|<1$ and $|x|\le1$, prove $1+sx>0$ and then certify by
`field_simp` and `ring`:

$$
r(s,x)-\theta(s)
=\frac{(1-s^2)x}{2(1+sx)},
$$

$$
p(r(s,x))
=-\frac{(1-s^2)(1-x^2)(s+x)}{4(1+sx)^3},
$$

where $p(r)=r(1-r)(1-2r)$.

### 4. `Moments.lean` and `MomentRecurrence.lean`

Status: implemented and compiled. This includes $M_1,M_2,M_3$, the needed
exact ratios, strict positivity of every $M_j$, and

$$
(2j+1)M_j=(2j+15)M_{j+1}.
$$

For

$$
M_j=\int_0^1x^{2j}(1-x^2)^6\,dx,
$$

prove positivity and the recurrence

$$
(2j+1)M_j=(2j+15)M_{j+1}.
$$

For fixed exponent 6, expanding the polynomial and integrating monomials is
likely simpler than developing a general beta-integral API. The needed exact
values include

$$
M_1=\frac{1024}{45045},\qquad
M_2=\frac3{17}M_1,\qquad
M_3=\frac{15}{323}M_1.
$$

### 5. `Series.lean`

Status: split into several compiled modules:

- `AnalyticKernel.lean` proves the exact paired rational identity;
- `IntegralPairing.lean` proves the symmetric interval-integral identity;
- `GeometricSeries.lean` supplies the convergent denominator expansion;
- `PointwiseSeries.lean` and `SeriesIntegration.lean` prove the pointwise
  series identity and its termwise integration under an explicit summable
  majorant;
- `ShiftedBinomialSeries.lean` and `CollectedPointwise.lean` collect equal
  powers of $s^2$ using the leading-zero shifts $0,1,2,3$;
- `Coefficients.lean` and `SeriesCoefficients.lean` derive and certify every
  coefficient.
- `SeriesCertificate.lean` proves, conditional only on summability, that the
  series is bounded below by $M_1(1489/5610)>0$.
- `IntegratedCoefficients.lean` identifies every integrated collected term
  with $M_{m+1}Q_m(s^2)^m$.
- `CollectedIntegration.lean` completes the dominated-convergence assembly
  and proves `I13_eq_seriesSum13_sq`, `certificate_le_I13`, and `I13_pos`.

This part of the proof is complete.

Define

$$
I(s)=\int_{-1}^1
\frac{(1-x^2)^6x(s+x)(2/11+sx)}{(1+sx)^5}\,dx.
$$

Prove an absolutely convergent expansion

$$
I(s)=\sum_{m=0}^{\infty}M_{m+1}Q_m(s^2)^m
\qquad (|s|<1).
$$

The formal proof supplies the explicit uniform bound

$$
\left|f_m(s,x)\right|
\le 60\binom{m+4}{4}(s^2)^m,
$$

whose series is summable for $|s|<1$. Dominated convergence justifies the
exchange of summation and integration. The first three terms and the
nonnegative tail, together with the completed-square theorem in
`Algebra.lean`, then yield

$$
I(s)\ge M_1\frac{1489}{5610}>0.
$$

### 6. `QuadraticBound.lean`

Status: implemented as `QuadraticBounds.lean` and compiled.

The file formalizes the paired-integral estimates

$$
J_4(s)\le\frac{256}{165},\qquad
J_6(s)\le\frac{64}{9}.
$$

Pair the integrands at $x$ and $-x$ and reduce the comparison to monotonicity
in $s^2x^2$. This avoids differentiating under the integral sign. Use

$$
(s+x)^2\le(1+sx)^2,
$$

whose difference is $(1-s^2)(1-x^2)$.

The public endpoint results are `integral_quadraticKernel4_le` and
`integral_quadraticKernel6_le`. The theorem
`n13_quadratic_integrals_le` also packages the exact constant
$1696/165$ needed by the reduced-risk arithmetic.

### 7. `Reduced.lean`

Status: implemented and compiled.

The module defines the exact centered-coordinate quantities and proves

$$
C_\theta(s)\le K_a(1-s^2)^2\frac{1696}{165}.
$$

It then avoids dividing by the quadratic coefficient. The generic theorem is

```lean
theorem reducedRiskDifference13_neg_of_epsilon
    (Ka : ℝ) {s ε : ℝ}
    (hKa : 0 < Ka) (hs : |s| < 1) (hε : 0 < ε)
    (hεH :
      ε * (1696 / 165) < M 1 * (1489 / 5610)) :
    2 * ε * Btheta13 Ka s + ε ^ 2 * Ctheta13 Ka s < 0
```

`reducedRiskDifference13_neg` discharges the rational threshold at
$\varepsilon=1/2000$. This ratio-free form avoids a separate proof that
$C_\theta>0$. Combine it with the clipping contraction and the probability
law bridge to obtain the estimator-level dominance theorem.

### 8. Gamma and beta bridge modules

Status: implemented and compiled.

`GammaMoments.lean`, `BetaBridge.lean`, `CanonicalProduct.lean`, and
`CanonicalLaws.lean` now provide:

- gamma moments and inverse moments, including integrability;
- the centered `Beta(6,6)` integration formula;
- the mixed-moment factorizations from the component laws and independence;
- the complete canonical moment bridge from
  $P\sim\operatorname{Beta}(6,6)$,
  $L\sim\operatorname{Gamma}(12,1/2)$, and
  $V\sim\operatorname{Gamma}(1/2,1/2)$.

`NormalSquare.lean` adds the exact squared-standard-normal law and
common-rate gamma convolution/additivity. `BetaGamma.lean` proves the
beta–gamma ratio/sum theorem by the change of variables

$$
(p,\ell)\longmapsto(p\ell,(1-p)\ell),
$$

whose Jacobian determinant has absolute value $\ell$.  In particular, it
constructs both transformed laws and their independence.

### 9. `Canonical.lean`

This milestone is now implemented.  The central theorem is:

```lean
theorem canonicalNormalizedRiskDifference13_neg_of_component_laws
    ...
    (hP : HasLaw P (betaMeasure 6 6) Pmeasure)
    (hL : HasLaw L (gammaMeasure 12 (1 / 2)) Pmeasure)
    (hV : HasLaw V (gammaMeasure (1 / 2) (1 / 2)) Pmeasure)
    (hP_LV : IndepFun P (fun ω => (L ω, V ω)) Pmeasure)
    (hVL : IndepFun V L Pmeasure) :
    canonicalNormalizedRiskDifference13
      epsilon13 s P L V Pmeasure < 0
```

Internally, this derives exactly the required moments:

$$
E[V]=1,\quad E[V^2]=3,\quad E[V^3]=15,
$$

$$
E[L^{-1}]=\frac1{22},\qquad
E[L^{-2}]=\frac1{440}.
$$

`canonicalClippedEstimatorRiskDifference13_neg_of_summary_laws` then
transfers the strict inequality to the clipped estimator and derives all
finite-risk and centered-cross-term hypotheses from measurability,
square-integrability, mean zero, and independence of the centered error from
$(D,P,L)$.  `SummaryIndependence.lean` and `SummaryTransform.lean` now
provide the exact four-way mutual-independence adapter used by the raw
normal-sample layer.

### 10. `NormalSample.lean`

Status: implemented and compiled, together with `Cochran13.lean`,
`GaussianMeanBridge.lean`, and `RawNormalSummary.lean`.

The formalization represents each sample in `EuclideanSpace ℝ (Fin 13)`,
splits the residual vector into the twelve-dimensional hyperplane
orthogonal to the constant direction, and proves:

- normality of the sample means;
- independence of means and residual vectors;
- the squared residual norm has the required gamma/chi-square law;
- the two samples' summary variables have the canonical joint law.

The endpoint theorem is
`rawNormalSummaryLaws13_of_normal_samples`.  It includes
$P\sim\operatorname{Beta}(6,6)$,
$L\sim\operatorname{Gamma}(12,1/2)$,
$V\sim\operatorname{Gamma}(1/2,1/2)$, the centered-error moment
conditions, and mutual independence of $(C,D,P,L)$.

### 11. Raw estimator bridge

Status: implemented and compiled.

`canonicalClippedEstimatorRiskDifference13_neg_of_raw_normal` combines the
raw-sample summary-law theorem, canonical strict risk dominance, clipping,
and finite-risk facts.  `RawPositivity.lean` proves almost-everywhere
nonvanishing of the residual and sample-variance denominators.
`RawEstimatorCoordinates.lean` then applies the identities in
`RawCoordinates.lean` pointwise, and `RawEstimatorRisk.lean` transports the
risk inequality across the resulting almost-everywhere equalities.

The final theorem `rawGraybillDealEstimator13_strictly_dominated` states the
result exactly for

$$
\bar X_1+rD
$$

and

$$
\bar X_1+\operatorname{clip}_{[0,1]}
  \left(r+\frac1{2000}r(1-r)(1-2r)(4-q)\right)D.
$$

## Obligations that the paper proof can suppress but Lean cannot

- Every risk identity needs integrability hypotheses.
- Ratios involving sample variances need almost-everywhere positivity of the
  denominator.
- Endpoint expressions at $s=\pm1$ can contain $0/0$ and should be handled
  almost everywhere or avoided by proving the theorem first for $|s|<1$.
- The series/integral exchange requires an explicit summable dominating
  function.
- Independence of sample mean and sample variance must be derived, not
  asserted.
- The unclipped perturbation must be shown square-integrable before applying
  the real-valued risk identity.

## Extension to all equal sample sizes $n\geq10$

Status: implemented and compiled through the literal raw-estimator theorem.
The central analytic theorem, both quadratic endpoint formulas, the
reduced-risk comparison, canonical and raw probability-law bridges, and
almost-everywhere estimator transport are complete.

Parameterize by residual degrees of freedom $\nu=n-1\geq9$ and sample each
population over `Fin (ν + 1)`.  The new modules establish:

1. `GeneralAnalytic.lean`: $L_\nu(z)>0$ on $[0,1]$, an explicit
   sample-size statement, and existence of a positive $\varepsilon_\nu$
   once the two integral bounds are available.
2. `GeneralMoments.lean`, `GeneralCoefficients.lean`, and
   `GeneralSeriesCoefficients.lean`: the general moment recurrence, initial
   coefficients, positive tail, and exact derivation of every coefficient
   from the paired numerator.
3. `GeneralKernel.lean`, `GeneralIntegralPairing.lean`, and
   `GeneralSeriesCertificate.lean`: the exact real-power paired kernel,
   its symmetric integral, and the strictly positive formal-series
   certificate conditional on summability.
4. `GeneralMomentIntegral.lean`: the beta-integral identity
   $$
   M_{\nu,j}=\int_0^1x^{2j}(1-x^2)^{\nu/2}\,dx
   $$
   with its continuity, integrability, and endpoint obligations.
5. `GeneralSeriesIntegration.lean`, `GeneralCollectedPointwise.lean`, and
   `GeneralCollectedBounds.lean`: the pointwise series, exact shifted
   collection, and a summable uniform majorant.
6. `GeneralIntegratedCoefficients.lean`,
   `GeneralCollectedIntegration.lean`, and
   `GeneralCentralAnalytic.lean`: the exact identity
   $$
   I_\nu(s)=\sum_{m=0}^{\infty}
     M_{\nu,m+1}Q_{\nu,m}(s^2)^m
   $$
   and the central theorem
   $$
   M_{\nu,1}L_\nu(s^2)\leq I_\nu(s),\qquad I_\nu(s)>0
   $$
   for every natural $\nu\geq9$ and $|s|<1$, including direct
   sample-size statements for every $n\geq10$.
7. `GeneralQuadratic.lean`,
   `GeneralQuadraticEndpoint4.lean`, and
   `GeneralQuadraticEndpoint6.lean`: the pointwise reduction to the two
   endpoint kernels, their uniform bounds for $|s|<1$, and the exact
   evaluations
   $$
   J_4=2^{\nu-1}B(\nu/2+2,\nu/2-2),\qquad
   J_6=2^{\nu-3}B(\nu/2+2,\nu/2-4).
   $$
   The sixth-order proof treats the integrable singular endpoint at
   $\nu=9$.
8. `GeneralReduced.lean` and `GeneralQuadraticBounds.lean`: the combined
   allowance
   $$
   H_\nu=J_4+
     \frac{15\nu^2}{16(\nu-1)(\nu-2)}J_6
   $$
   and existence, for each natural $\nu\geq9$, of one
   $\varepsilon_\nu>0$ satisfying the ratio-free strict reduced-risk
   inequality for every $|s|<1$.
9. `GeneralBetaBridge.lean`, `GeneralCanonicalAlgebra.lean`, and
   `GeneralCanonicalProduct.lean`: the arbitrary symmetric-beta
   change of variables, generic gamma product moments, and the exact
   linear and quadratic moment reductions.
10. `GeneralCanonical.lean`, `GeneralCanonicalClipping.lean`, and
    `GeneralCanonicalLaws.lean`: the canonical normalized-risk identity,
    clipping contraction, and the component-law theorem
    `exists_generalCanonicalRisk_epsilon_of_component_laws`.  This theorem
    assumes
    $$
    P\sim\operatorname{Beta}(\nu/2,\nu/2),\quad
    L\sim\operatorname{Gamma}(\nu,1/2),\quad
    V\sim\operatorname{Gamma}(1/2,1/2),
    $$
    with $P\perp(L,V)$ and $V\perp L$, and produces one positive
    $\varepsilon_\nu$ that works for every interior variance ratio.
11. `GeneralGammaMoments.lean`, `GeneralBetaGamma.lean`,
    `GeneralNormalSample.lean`, and `GeneralGaussianMeanBridge.lean`: the
    parameter-generic inverse moments, beta--gamma transformation, Gaussian
    mean/residual decomposition, Cochran theorem, standardized
    mean-difference law, and its independence from the residual summaries.
12. `GeneralGraybillDealEpsilon.lean`: a noncomputable but fixed choice
    $$
    \varepsilon_\nu
      =\texttt{generalGraybillDealEpsilon }\nu>0
    $$
    for each $\nu\geq9$.  The choice depends only on $\nu$ and satisfies the
    strict reduced-risk inequality simultaneously for every $|s|<1$; in
    particular, it does not depend on the unknown population variances.
13. `GeneralCanonicalSummary.lean`, `GeneralSummaryTransform.lean`, and
    `GeneralSummaryIndependence.lean`: the estimator-level clipped-risk
    theorem, all finite-risk and centered-cross-term obligations, and the
    mutual-independence adapters for $(C,D,P,L)$.
14. `GeneralRawNormalSummary.lean`: direct assembly from the raw samples of
    $$
    P\sim\operatorname{Beta}(\nu/2,\nu/2),\quad
    L\sim\operatorname{Gamma}(\nu,1/2),\quad
    V\sim\operatorname{Gamma}(1/2,1/2),
    $$
    together with the required independence and centered-error moment
    statements.
15. `GeneralRawCoordinates.lean` and `GeneralRawPositivity.lean`: exact
    arbitrary-$\nu$ coordinate formulas and almost-everywhere positivity of
    the individual sample variances, $S_1^2+S_2^2$, and the residual
    coordinate $L$.
16. `GeneralRawEstimatorCoordinates.lean` and
    `GeneralRawEstimatorAE.lean`: pointwise-on-the-positive-denominator-set
    and almost-everywhere identification of the canonical expressions with
    the literal ordinary and clipped Graybill–Deal estimators.
17. `GeneralRawRiskBridge.lean` and `GeneralRawEstimatorRisk.lean`: assembly
    of all preceding layers and the final theorem
    `rawGraybillDealEstimatorN_strictly_dominated`.

For $\nu=n-1\geq9$, define

$$
D=\bar X_2-\bar X_1,\qquad
r=\frac{S_1^2}{S_1^2+S_2^2},\qquad
q=\frac{(\nu+1)D^2}{S_1^2+S_2^2},
$$

and

$$
w_\nu=\operatorname{clip}_{[0,1]}
  \left(r+\varepsilon_\nu r(1-r)(1-2r)(4-q)\right).
$$

For two independent measurable samples of common size $\nu+1$ from
$N(\mu,\sigma_i^2)$ with both population variances positive,
`rawGraybillDealEstimatorN_strictly_dominated` proves

$$
R(\mu,\bar X_1+w_\nu D)
<
R(\mu,\bar X_1+rD).
$$

Thus the ordinary Graybill–Deal estimator is inadmissible, under the
formalized squared-error model, for every fixed equal sample size
$n\geq10$.  The coefficient may vary with $n$; the formalization does not
claim one common numerical coefficient for all sample sizes, nor does it
cover unequal sample sizes or $n<10$.
