# Extending the unequal Graybill--Deal result to every pair $(n,n+4)$

## Target

The completed Lean theorem covers

$$
(n_1,n_2)=(2m-1,2m+3),\qquad m\in\mathbb N,\quad m\geq 7.
$$

Thus it gives the odd--odd pairs

$$
(13,17),(15,19),(17,21),\ldots.
$$

The next target is

$$
(n_1,n_2)=(n,n+4),\qquad n\geq 13,
$$

including the missing even--even pairs $(14,18),(16,20),\ldots$.

## Real parameterization

For arbitrary integer $n\geq 13$, put

$$
m=\frac{n+1}{2}.
$$

The residual degrees of freedom and their Gamma shapes are

$$
\nu_1=n-1=2(m-1),\qquad
\nu_2=n+3=2(m+1),
$$

so

$$
U_1\sim\Gamma\left(m-1,\frac12\right),\qquad
U_2\sim\Gamma\left(m+1,\frac12\right).
$$

Consequently,

$$
P=\frac{U_1}{U_1+U_2}
  \sim\operatorname{Beta}(m-1,m+1),
$$

and

$$
L=U_1+U_2\sim\Gamma\left(2m,\frac12\right).
$$

When $n$ is odd, $m$ is an integer and this is exactly the completed
formalization. When $n$ is even, $m$ is a half-integer. The probability
laws themselves make no distinction between these cases.

## The coefficient certificate already works for real $m$

The exceptional head coefficients and both generic tail numerators in the
completed proof were reduced to polynomial sign certificates after the
shifts

$$
u=m-7,\qquad v=j-3.
$$

Every coefficient of each shifted polynomial is strictly positive. These
polynomials and their positivity theorems are already stated over the real
numbers in `UnequalFixedDifferenceFourCoefficients.lean`. Therefore their
proof requires only

$$
m\geq 7,\qquad j\geq 3,
$$

and does not require $m$ to be an integer.

The remaining coefficient denominators factor into terms such as

$$
m,\quad 2m-1,\quad
2m+j,\ldots,2m+j+4,\quad
m^3+2m^2-m+10,
$$

all of which are positive for real $m\geq7$ and $j\geq3$.
The finite-product Beta moments

$$
\prod_{i=0}^{j-1}
\frac{m\pm1+i}{2m+i}
$$

are also positive for real $m\geq7$.

It follows that the same one-sided coefficient sequences are strictly
negative for every real $m\geq7$.

## Real-power Beta-density bridge

The only genuinely parity-sensitive part of the Lean implementation was
the use of natural powers in the chart densities. For real $m$, define

$$
\rho_+(y)
=
\frac{y^m(1-y)^{m-2}}
     {B(m+1,m-1)}
$$

and

$$
\rho_-(y)
=
\frac{y^{m-2}(1-y)^m}
     {B(m-1,m+1)}.
$$

Here the powers are real powers. Since $m\geq7$, both exponents $m$ and
$m-2$ are nonnegative, so these functions have continuous real-power
extensions. On $(0,1)$ they are exactly the
$\operatorname{Beta}(m+1,m-1)$ and
$\operatorname{Beta}(m-1,m+1)$ densities.

The new Lean module
`UnequalFixedDifferenceFourRealMoments.lean` already machine-checks:

1. continuity of both real-power densities;
2. the exact Beta moment products for arbitrary real $m\geq7$;
3. the interval-integral identities needed by the termwise series
   argument.

Thus the real-power density and monomial-moment obstruction has been
removed.  The separate module
`UnequalFixedDifferenceFourRealSeriesSign.lean` also machine-checks strict
negativity of every resulting formal coefficient for every real
$m\geq7$.

The subsequent modules now machine-check the rest of the reduced analytic
chain:

1. `UnequalFixedDifferenceFourRealSeriesBridge.lean` reduces the integrated
   coefficients to polynomial moments;
2. `UnequalFixedDifferenceFourRealCollectedAlgebra.lean` proves that each
   polynomial coefficient is exactly the certified negative coefficient;
3. `UnequalFixedDifferenceFourRealEnvelopeIntegrals.lean` evaluates the two
   inverse-Beta quadratic envelopes;
4. `UnequalFixedDifferenceFourRealReduced.lean` combines the linear and
   quadratic bounds with the fixed real-$m$ perturbation;
5. `UnequalFixedDifferenceFourRealCanonical.lean` defines the direct
   canonical denominator, Graybill--Deal weight, quadratic statistic, and
   clipped perturbation for real $m$;
6. `UnequalFixedDifferenceFourRealCanonicalReduced.lean` proves the two
   chart identities and transports their strict reduced-risk inequalities
   to the direct canonical beta coordinate;
7. `UnequalFixedDifferenceFourRealCanonicalProduct.lean` integrates out
   the two Gamma coordinates and packages the resulting moments as the
   required product-moment bridge;
8. `UnequalFixedDifferenceFourRealCanonicalLaws.lean` proves integrability
   of the canonical Beta factors and assembles the Beta/Gamma component
   laws with that product bridge;
9. `UnequalFixedDifferenceFourRealCanonicalSummary.lean` packages these
   results into a strict estimator-level squared-risk comparison under
   explicit canonical summary laws and independence hypotheses.

## Exact check at the first missing pair $(14,18)$

For $(n_1,n_2)=(14,18)$,

$$
m=\frac{15}{2},\qquad
t=\frac{13}{30},\qquad q=\frac{17}{30}.
$$

The exact direction constants are

$$
\kappa=\frac{3616}{21475},
\qquad
c=\frac{689}{210}.
$$

The pivot margin and quadratic envelopes are

$$
b_0=\frac{20059}{98956800},
$$

$$
M_+
=
\frac{1632146251187}{3929310000},
\qquad
M_-
=
\frac{20626488059}{436590000},
$$

with $0<M_-<M_+$. The safe perturbation coefficient is

$$
\varepsilon_{14,18}
=
\frac{b_0}{M_+}
=
\frac{21893897025}{44864436152628256}
\approx 4.88001163115\times10^{-7}.
$$

The first three coefficients on the plus chart are

$$
-\frac{20059}{98956800},\qquad
-\frac{18201391}{44530560000},\qquad
-\frac{43673981}{39899381760},
$$

and those on the minus chart are

$$
-\frac{20059}{98956800},\qquad
-\frac{8878259}{44530560000},\qquad
-\frac{124846891}{184719360000}.
$$

All are strictly negative, and the real polynomial tail certificate proves
the same for every later coefficient.

## Raw normalization for arbitrary $n$

Let

$$
\lambda=\frac{\sigma_1^2}{n}
       +\frac{\sigma_2^2}{n+4},
\qquad
\theta=
\frac{\sigma_1^2/n}{\lambda}.
$$

The beta pivots become

$$
t=\frac{n-1}{2(n+1)},\qquad
q=\frac{n+3}{2(n+1)}.
$$

Writing

$$
\mathcal D(\theta,p)
=
\frac{\theta}{t}p
+\frac{1-\theta}{q}(1-p),
$$

the sum of the two estimated sample-mean variances is

$$
A_1+A_2
=
\frac{\lambda L}{2(n+1)}
\mathcal D(\theta,P).
$$

Hence the canonical quadratic statistic is

$$
Q_{\mathrm{can}}
=
\frac{2(n+1)V}{L\mathcal D(\theta,P)}
=
\frac{4mV}{L\mathcal D(\theta,P)},
$$

which is exactly the expression used in the completed odd-family proof.

## Current status

Lean now proves the stronger reduced analytic statement

$$
\text{for every real }m\geq7\text{ and }0\leq s<1,
\quad
2\varepsilon_m B_\pm(m,s)
+\varepsilon_m^2 C_\pm(m,s)<0
\quad\text{on both one-sided charts}.
$$

It now also proves the direct canonical statement

$$
\text{for every real }m\geq7\text{ and }0<\theta<1,
\quad
2\varepsilon_m B_{\mathrm{can}}(m,\theta)
+\varepsilon_m^2 C_{\mathrm{can}}(m,\theta)<0.
$$

This is the theorem
`unequalFixedDifferenceFourRealCanonicalReducedRisk_neg`.  Taking
$m=(n+1)/2$ therefore supplies the complete direct canonical reduced-risk
certificate for every $(n,n+4)$ with $n\geq13$, including the half-integral
parameters arising from even $n$.

The canonical probability/product/estimator-summary layer is now complete
too.  Under its stated Beta/Gamma component laws, independence and
measurability hypotheses, and square-integrable mean-zero centered error,
the theorem
`unequalFixedDifferenceFourRealCanonicalClippedEstimatorRiskDifference_neg_of_summary_laws`
proves

$$
R_\mu(\widehat\mu_{\mathrm{clip},m})
<
R_\mu(\widehat\mu_{\mathrm{can},m})
$$

for every real $m\geq7$.  Here both estimators are still expressed in the
canonical summary coordinates; the theorem does not assert that an
arbitrary real $m$ is a raw sample dimension.

## Final raw theorem

For a natural number $n\geq13$, the raw layer sets

$$
m_n=\frac{n+1}{2},\qquad
\nu_1=n-1,\qquad
\nu_2=n+3.
$$

The exact Lean size lemmas
`unequalFixedDifferenceFourAllNResidualDF1_add_one` and
`unequalFixedDifferenceFourAllNResidualDF2_add_one` record

$$
\nu_1+1=n,\qquad
\nu_2+1=n+4.
$$

Thus the two index types represent samples of exactly the advertised sizes
$n$ and $n+4$.  The all-$n$ summary construction derives

$$
P\sim\operatorname{Beta}(m_n-1,m_n+1),
\qquad
L\sim\Gamma\left(2m_n,\frac12\right),
$$

together with the needed $V$ law, independence statements, centered-error
integrability, and mean-zero identity.  There is no parity obstruction:
these laws allow both integral $m_n$ for odd $n$ and half-integral $m_n$
for even $n$.

The final declaration is
`unequalFixedDifferenceFourAllNRawClippedPerturbedEstimator_sqRisk_lt_rawGraybillDealEstimator`.
Its conclusion is

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

for every $n\geq13$, assuming the stated two independent raw normal samples,
measurability of their coordinates, and strictly positive population
variances.  The perturbation coefficient is

$$
\varepsilon_n
=
\operatorname{unequalFixedDifferenceFourRealEpsilon}(m_n)
=
\operatorname{unequalFixedDifferenceFourRealEpsilon}
  \left(\frac{n+1}{2}\right).
$$

It is fixed by the sample size alone: it does not depend on the common
mean, the population variances, the variance ratio, or the realized data.

The proof interface transports the canonical clipped estimator and
canonical Graybill--Deal estimator to the literal estimators almost
everywhere, with the canonical functions on the left of each almost-
everywhere equality.  This direction lets the two canonical squared risks
rewrite directly to the two literal squared risks without reversing the
strict inequality.

The final all-$n$ raw declaration is machine-checked.  Both new production
modules compile, the aggregate build passes all 3337 jobs, and the axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound` for the
summary-law constructor, almost-everywhere transports, canonical raw risk
theorem, and final literal dominance theorem.  The theorem is confined to
the positive-variance raw normal model stated above.  It makes no claim
for zero population variances or for other sampling models.
