# The limiting-Bayes bridge for arbitrary sample sizes

This note expands the decision-theoretic part of the universal proof for
arbitrary \(n_1,n_2\ge2\). Its
purpose is to explain carefully why admissibility would imply the existence
of a probability measure $\nu$ satisfying

$$
A_\nu(r,q)
=
\frac{\displaystyle\int_0^1
  \theta B_\theta(r,q)^{-p}\,\nu(d\theta)}
{\displaystyle\int_0^1
  B_\theta(r,q)^{-p}\,\nu(d\theta)}
=r,
\tag{1}
$$

first for $0<r<1$, $q>0$, and then also at the boundary $q=0$.

Here

$$
a=\frac{n_1-1}{2},\qquad b=\frac{n_2-1}{2},\qquad
p=a+b+\frac32,
$$

and

$$
B_\theta(r,q)
=2ar(1-\theta)+2b(1-r)\theta+q\theta(1-\theta).
$$

The later moment calculations and the unequal/equal derivative
contradictions are developed separately.

## 1. What is the reduced decision problem?

Put

$$
v_1=\frac{\sigma_1^2}{n_1},\qquad
v_2=\frac{\sigma_2^2}{n_2},\qquad
\tau=v_1+v_2,\qquad
\theta=\frac{v_1}{\tau}.
$$

Because both variances are positive,

$$
0<\theta<1.
$$

Thus the reduced parameter space is

$$
\Theta=(0,1).
$$

Let

$$
D=\bar X_2-\bar X_1,\qquad
Y_1=\frac{S_1^2}{n_1},\qquad
Y_2=\frac{S_2^2}{n_2},
$$

and define the scale-free observations

$$
r=\frac{Y_1}{Y_1+Y_2},\qquad
q=\frac{D^2}{Y_1+Y_2}.
$$

Except on null events, $0<r<1$ and $q>0$.  The reduced sample space is
therefore

$$
\mathcal X=(0,1)\times(0,\infty).
$$

The action is a real number $d\in\mathbb R$, interpreted as an estimate of
$\theta$, and the loss is

$$
L(\theta,d)=(d-\theta)^2.
$$

The Graybill--Deal weight is the reduced rule

$$
d(r,q)=r.
$$

### Why inadmissibility here is enough

Gaussian regression gives

$$
\bar X_1-\mu=-\theta D+E,
$$

where $E$ is independent of $(D,S_1^2,S_2^2)$ and

$$
\operatorname{Var}(E)=\tau\theta(1-\theta).
$$

Consequently, if $\phi(r,q)$ is any reduced rule, the corresponding
estimator of the common mean,

$$
\delta_\phi=\bar X_1+D\phi(r,q),
$$

has risk

$$
R_{\mu,\tau,\theta}(\delta_\phi)
=
\tau\theta(1-\theta)
+
\tau E_\theta\!\left[
  \frac{D^2}{\tau}\{\phi(r,q)-\theta\}^2
\right].
\tag{2}
$$

Define the risk-weighted probability law

$$
Q_\theta(A)
=
E_\theta\!\left[
  \frac{D^2}{\tau}\,
  1_{\{(r,q)\in A\}}
\right].
\tag{3}
$$

It is a probability law because $D/\sqrt\tau\sim N(0,1)$ and hence
$E_\theta(D^2/\tau)=1$.  Equation (2) becomes

$$
R_{\mu,\tau,\theta}(\delta_\phi)
=
\tau\theta(1-\theta)
+
\tau\int_{\mathcal X}
  \{\phi(r,q)-\theta\}^2\,Q_\theta(d r\,d q).
\tag{4}
$$

Therefore, if some $\phi$ dominates $r$ in the reduced problem, then
$\delta_\phi$ dominates Graybill--Deal in the original problem.  A strict
improvement at one $\theta$ remains strict after multiplication by every
$\tau>0$, and neither side depends on $\mu$.

The contrapositive is what we use:

> If Graybill--Deal were admissible in the original problem, then $r$ would
> have to be admissible in the reduced problem.

This implication does **not** claim that every estimator of the common mean
has the form $\delta_\phi$.  It only observes that a dominator found in this
subclass would already disprove admissibility in the full class.

## 2. The reduced density and the part that matters for Bayes' formula

Relative to two-dimensional Lebesgue measure $d r\,d q$ on $\mathcal X$,
the risk-weighted law $Q_\theta$ has density

$$
f_\theta^Q(r,q)
=
C_{a,b}r^{a-1}(1-r)^{b-1}q^{1/2}
\frac{\theta^{b+3/2}(1-\theta)^{a+3/2}}
{\{2ar(1-\theta)+2b(1-r)\theta
   +q\theta(1-\theta)\}^{p}},
\tag{5}
$$

where

$$
C_{a,b}
=\frac{2^p a^a b^b\Gamma(p)}
{\sqrt{2\pi}\Gamma(a)\Gamma(b)}>0.
$$

For later convenience define

$$
c(r,q)=C_{a,b}r^{a-1}(1-r)^{b-1}q^{1/2},
\qquad
w(\theta)=\theta^{b+3/2}(1-\theta)^{a+3/2},
\tag{6}
$$

and

$$
B_\theta(r,q)
=
2ar(1-\theta)+2b(1-r)\theta+q\theta(1-\theta).
\tag{7}
$$

Then simply

$$
f_\theta^Q(r,q)=c(r,q)w(\theta)B_\theta(r,q)^{-p}.
\tag{8}
$$

For every $(r,q)\in\mathcal X$ and $\theta\in(0,1)$, all factors in
(5) are strictly positive.  Thus

$$
f_\theta^Q(r,q)>0.
\tag{9}
$$

This positivity is an important hypothesis of the complete-class theorem.

## 3. The exact theorem used from Lehmann--Casella

The relevant result is
[Theorem 7.15 in Chapter 5, Section 7 of Lehmann and Casella, *Theory of
Point Estimation*, second edition](https://www.dcpehvpm.org/E-Content/Stat/E%20L%20Lehaman.pdf)
(often referenced as Theorem 5.7.15; printed page 382, equation (5.7.12)).
In the notation used here, it says:

> Suppose that the experiment has a density $f_\theta(x)$ relative to a
> sigma-finite measure $m$, with $f_\theta(x)>0$ for every sample point $x$
> and every parameter value $\theta$.  Suppose also that
> $L(\theta,d)$ is continuous, strictly convex in $d$, and tends to
> infinity as $|d|\to\infty$.  Then every admissible rule $\delta$ is the
> $m$-almost-everywhere limit of Bayes rules for a sequence of priors having
> finite support.

Here the dominating measure $m$ is two-dimensional Lebesgue measure on
$\mathcal X$.  It is sigma-finite; for example,

$$
\mathcal X
=
\bigcup_{k=2}^\infty
\left[\frac1k,1-\frac1k\right]\times
\left[\frac1k,k\right],
$$

and each rectangle has finite Lebesgue measure.

The remaining hypotheses are checked directly:

1. Equation (9) gives strict positivity of the density.
2. $(d-\theta)^2$ is continuous in $(\theta,d)$.
3. Its second derivative with respect to $d$ is $2>0$, so it is strictly
   convex in $d$.
4. For every fixed $\theta$,

   $$
   (d-\theta)^2\longrightarrow\infty
   \quad\text{as }|d|\longrightarrow\infty.
   $$

The candidate rule also has finite risk: since \(0<r,\theta<1\),
\((r-\theta)^2\le1\), and \(Q_\theta\) is a probability law.

We deliberately take the action space to be $\mathbb R$, exactly as in the
theorem's coercivity condition.  Although projection onto $[0,1]$ can only
reduce squared error when $\theta\in(0,1)$, no compact-action modification
of the theorem is needed.

Assume now, for contradiction, that $r$ is admissible in the reduced
problem.  The theorem supplies priors

$$
\pi_j=\sum_{k=1}^{N_j}\alpha_{jk}\delta_{\theta_{jk}},
\qquad
\alpha_{jk}>0,\quad
\sum_k\alpha_{jk}=1,\quad
0<\theta_{jk}<1,
\tag{10}
$$

whose Bayes rules, denoted $A_j(r,q)$, satisfy

$$
A_j(r,q)\longrightarrow r
\quad\text{for Lebesgue-almost every }(r,q)\in\mathcal X.
\tag{11}
$$

The phrase "almost every" in (11) refers to the **sample-space**
Lebesgue measure $d r\,d q$, not to a measure on the parameter space.

## 4. Computing each finite-prior Bayes rule

Under squared loss, the Bayes action is the posterior mean of $\theta$.
This follows by completing the square.  If the posterior has mean $m$, then

$$
E[(d-\theta)^2\mid r,q]
=
(d-m)^2+\operatorname{Var}(\theta\mid r,q),
\tag{12}
$$

which is uniquely minimized at $d=m$.

For the finite prior (10), Bayes' formula gives

$$
A_j(r,q)
=
\frac{\displaystyle
  \sum_k\theta_{jk}f_{\theta_{jk}}^Q(r,q)\alpha_{jk}}
{\displaystyle
  \sum_k f_{\theta_{jk}}^Q(r,q)\alpha_{jk}}.
\tag{13}
$$

Substitute (8).  The data-only factor $c(r,q)$ cancels from numerator and
denominator:

$$
A_j(r,q)
=
\frac{\displaystyle\int_0^1
  \theta\,w(\theta)B_\theta(r,q)^{-p}\,\pi_j(d\theta)}
{\displaystyle\int_0^1
  w(\theta)B_\theta(r,q)^{-p}\,\pi_j(d\theta)}.
\tag{14}
$$

This is the origin of the reweighting in the short proof.

## 5. Reweighting the priors

Let

$$
Z_j=\int_0^1 w(\theta)\,\pi_j(d\theta).
\tag{15}
$$

Every support point of $\pi_j$ lies in $(0,1)$, and $w(\theta)>0$ there.
Therefore

$$
0<Z_j<\infty.
\tag{16}
$$

Define a new probability measure

$$
\nu_j(d\theta)
=
\frac{w(\theta)}{Z_j}\,\pi_j(d\theta).
\tag{17}
$$

Indeed,

$$
\int_0^1\nu_j(d\theta)
=
\frac1{Z_j}\int_0^1w(\theta)\,\pi_j(d\theta)=1.
$$

Multiplying both numerator and denominator of (14) by $1/Z_j$ gives

$$
A_j(r,q)
=
\frac{\displaystyle\int_0^1
  \theta B_\theta(r,q)^{-p}\,\nu_j(d\theta)}
{\displaystyle\int_0^1
  B_\theta(r,q)^{-p}\,\nu_j(d\theta)}.
\tag{18}
$$

The numbers $Z_j$ are allowed to approach zero.  That causes no problem:
each $\nu_j$ is still an ordinary probability measure, and all later
arguments concern $\nu_j$, not the magnitude of $Z_j$.

## 6. Taking a weakly convergent subsequence

We regard every $\nu_j$ as a probability measure on the closed interval
$[0,1]$.  The space $[0,1]$ is compact.  The standard sequential
compactness theorem for probability measures on a compact metric space
(equivalently, the compact case of Prokhorov's theorem) gives a subsequence,
which we continue to denote by $\nu_j$, and a probability measure $\nu$ on
$[0,1]$ such that

$$
\nu_j\Rightarrow\nu.
\tag{19}
$$

By definition of weak convergence, (19) means that

$$
\int_0^1 g(\theta)\,\nu_j(d\theta)
\longrightarrow
\int_0^1 g(\theta)\,\nu(d\theta)
\tag{20}
$$

for every bounded continuous function $g:[0,1]\to\mathbb R$.

Although each $\nu_j$ is supported inside $(0,1)$, the limit $\nu$ may put
mass at $0$ or $1$.  For example, $\delta_{1/j}\Rightarrow\delta_0$.
This is why the closed interval is used.

## 7. Why the posterior ratios converge pointwise

Fix any $0<r<1$ and $q\geq0$.  As a function of $\theta\in[0,1]$,
$B_\theta(r,q)$ is continuous.  Moreover,

$$
B_\theta(r,q)
\geq 2ar(1-\theta)+2b(1-r)\theta
\geq \min\{2ar,\,2b(1-r)\}>0.
\tag{21}
$$

The first inequality uses $q\theta(1-\theta)\geq0$.  The second holds
because the middle expression is the linear interpolation between $2ar$
and $2b(1-r)$.

It follows from (21) that both functions

$$
\theta\longmapsto B_\theta(r,q)^{-p},
\qquad
\theta\longmapsto\theta B_\theta(r,q)^{-p}
\tag{22}
$$

are bounded and continuous on $[0,1]$.  Apply (20) to each one:

$$
\int B_\theta(r,q)^{-p}\,\nu_j(d\theta)
\longrightarrow
\int B_\theta(r,q)^{-p}\,\nu(d\theta),
\tag{23}
$$

and

$$
\int\theta B_\theta(r,q)^{-p}\,\nu_j(d\theta)
\longrightarrow
\int\theta B_\theta(r,q)^{-p}\,\nu(d\theta).
\tag{24}
$$

The limiting denominator in (23) is strictly positive.  The integrand is
strictly positive for every $\theta$, and $\nu$ has total mass one.
Therefore elementary convergence of quotients gives, at every fixed
$0<r<1$, $q\geq0$,

$$
A_j(r,q)\longrightarrow A_\nu(r,q),
\tag{25}
$$

where $A_\nu$ is the ratio in (1).

Notice that (25) is pointwise convergence produced by weak convergence,
whereas (11) is almost-everywhere convergence produced by the
Lehmann--Casella theorem.

## 8. Why the two limits must agree

Let $E\subset\mathcal X$ be the full-Lebesgue-measure set on which (11)
holds.  Passing to a subsequence does not destroy convergence on $E$.
Thus, for every $(r,q)\in E$, the same sequence $A_j(r,q)$ has the two
limits

$$
A_j(r,q)\longrightarrow r
$$

by (11), and

$$
A_j(r,q)\longrightarrow A_\nu(r,q)
$$

by (25).  A real sequence has at most one limit, so

$$
A_\nu(r,q)=r
\quad\text{for Lebesgue-almost every }(r,q)\in\mathcal X.
\tag{26}
$$

We next upgrade (26) to equality everywhere in $\mathcal X$.

The numerator and denominator in (1) are continuous functions of $(r,q)$
on $\mathcal X$.  One way to verify this carefully is to fix
$(r_0,q_0)\in\mathcal X$ and choose a small neighborhood in which

$$
\varepsilon\leq r\leq1-\varepsilon,
\qquad 0\leq q\leq M
$$

for some $\varepsilon>0$ and finite $M$.  Inequality (21) then gives the
uniform lower bound
$B_\theta(r,q)\geq2\min(a,b)\varepsilon>0$ for every
$\theta\in[0,1]$.  The two integrands are jointly continuous and uniformly
bounded there, so dominated convergence proves continuity of their
integrals.  The denominator stays positive, hence $A_\nu$ is continuous.
The function $(r,q)\mapsto r$ is also continuous.

If two continuous functions differ at one point of the open set
$\mathcal X$, then, by continuity, they differ throughout some open ball
around that point.  Every nonempty open ball has positive Lebesgue measure,
contradicting (26).  Therefore

$$
A_\nu(r,q)=r
\quad\text{for every }0<r<1,\ q>0.
\tag{27}
$$

No analytic-continuation theorem and no diagonal-subsequence argument is
being used here.

## 9. Extending the identity to $q=0$

The statistical sample space has $q>0$.  At $q=0$, the density (5) contains
the factor $q^{1/2}$ and vanishes.  Thus $A_\nu(r,0)$ should **not** be
described as an ordinary posterior mean conditional on observing $q=0$.
It is instead the continuous boundary value of the ratio in (1).

Fix $0<r<1$.  Inequality (21) remains true for every $q\geq0$.  Therefore,
as $q\downarrow0$, dominated convergence gives

$$
\int B_\theta(r,q)^{-p}\,\nu(d\theta)
\longrightarrow
\int B_\theta(r,0)^{-p}\,\nu(d\theta)
$$

and the analogous convergence for the numerator.  The limiting denominator
is positive, so

$$
A_\nu(r,q)\longrightarrow A_\nu(r,0).
\tag{28}
$$

Taking $q\downarrow0$ in (27) now gives

$$
A_\nu(r,0)=r
\quad\text{for every }0<r<1.
\tag{29}
$$

This boundary identity is what permits the later $q=0$ moment calculation
and the right derivative in $q$.

## 10. Why endpoint atoms of $\nu$ are harmless

The limit measure $\nu$ may have atoms at $\theta=0$ or $\theta=1$, even
though these points are not members of the original parameter space.
Direct substitution into (7) gives

$$
B_0(r,q)=2ar,
\qquad
B_1(r,q)=2b(1-r).
\tag{30}
$$

For $0<r<1$, both numbers are strictly positive and do not depend on $q$.
Hence an atom at $0$ contributes the finite quantities

$$
(2ar)^{-p}\nu(\{0\})
\quad\text{to the denominator},\qquad
0
\quad\text{to the numerator},
$$

and an atom at $1$ contributes

$$
\{2b(1-r)\}^{-p}\nu(\{1\})
$$

to both numerator and denominator.  There is no division by zero or
divergent integral.

The same observation justifies taking the **right** derivative in \(q\) at
\(q=0\): the \(q\)-dependent factor is \(\theta(1-\theta)\), which equals
zero at both endpoints.

## 11. What has, and has not, been proved at this stage

Assuming reduced admissibility, the Lehmann--Casella theorem and the
elementary limiting arguments above produce a probability measure $\nu$ on
$[0,1]$ satisfying

$$
\boxed{
\frac{\displaystyle\int_0^1
  \theta
  \{2ar(1-\theta)+2b(1-r)\theta+q\theta(1-\theta)\}^{-p}
  \,\nu(d\theta)}
{\displaystyle\int_0^1
  \{2ar(1-\theta)+2b(1-r)\theta+q\theta(1-\theta)\}^{-p}
  \,\nu(d\theta)}
=r
}
\tag{31}
$$

for every $0<r<1$ and every $q\geq0$.

The remaining proof shows that no probability measure $\nu$ can satisfy
(31).  When \(a\ne b\), its restriction to \(q=0\) forces moments making
the right \(q\)-derivative nonzero at \(r=b/(a+b)\).  When \(a=b\), that
first derivative vanishes by symmetry, but a mixed \(r,q\)-derivative is
strictly positive.  Both conclusions contradict (31).

## 12. Subtle points worth checking independently

1. **The complete-class theorem is the deep input.**  
   Everything after its application is elementary weak convergence,
   continuity, and Bayes' formula.  The theorem proves existence of
   finite-prior approximants; it does not construct a dominating estimator.

2. **Use the action space $\mathbb R$.**  
   This matches the theorem as printed.  The finite-prior Bayes actions
   automatically lie in $(0,1)$ because they are posterior means of
   parameters in $(0,1)$.

3. **The dominating measure in the theorem and the limiting prior are
   different objects.**  
   The theorem's measure is Lebesgue measure on the sample space.  The
   symbol $\nu$ in (31) denotes a probability measure on the compactified
   parameter space.

4. **The reweighting constants may tend to zero.**  
   Only their strict positivity for each finite $j$ is needed.

5. **The limiting measure may live partly or entirely at the endpoints.**  
   Formula (30) shows that this causes no singularity.

6. **$q=0$ is a boundary, not a positive-probability observation.**  
   The identity there follows from continuity of the ratio after equality
   has first been established for every $q>0$.

7. **The density calculation and the Gaussian risk reduction are separate
   load-bearing inputs.**  
   The decision-theoretic bridge is correct provided equations (4) and (5)
   have been independently verified.
