# Graybill--Deal inadmissibility for every pair of sample sizes

## A detailed reader's edition of the limiting-Bayes proof

### Theorem

Consider two independent normal samples

$$
X_{ij}\sim N(\mu,\sigma_i^2),
\qquad i=1,2,\quad j=1,\ldots,n_i,
$$

with a common unknown mean $\mu$, arbitrary unknown positive variances, and
$n_1,n_2\ge2$. Let $S_i^2$ be the usual unbiased sample variances. Under
squared-error loss, the Graybill--Deal estimator

$$
\delta_{\mathrm{GD}}
=
\frac{(n_1/S_1^2)\bar X_1+(n_2/S_2^2)\bar X_2}
     {n_1/S_1^2+n_2/S_2^2}
$$

is inadmissible for every fixed pair $(n_1,n_2)$.

Here â€œdominatesâ€ means that another estimator has no greater risk for every
$(\mu,\sigma_1^2,\sigma_2^2)$ and strictly smaller risk for at least one
such parameter point. An estimator is inadmissible precisely when a
dominator exists.

The proof is nonconstructive: it proves that a dominating estimator exists
for each fixed pair of sample sizes, but it does not give a formula for that
estimator.

The one genuinely deep input is
[Lehmann--Casella, *Theory of Point Estimation*, Chapter 5, Section 7,
Theorem 7.15](https://www.dcpehvpm.org/E-Content/Stat/E%20L%20Lehaman.pdf)
(often referenced as Theorem 5.7.15; printed page 382). Everything else is
derived in the three companion modules listed below.

The logical implication chain is

$$
\begin{aligned}
\delta_{\mathrm{GD}}\text{ admissible}
&\Longrightarrow r\text{ admissible in the reduced experiment}\\
&\Longrightarrow
\text{finite-prior Bayes approximants exist}\\
&\Longrightarrow
\text{a probability }\nu\text{ satisfies }(\star)\\
&\Longrightarrow\text{a derivative contradiction}.
\end{aligned}
$$

We prove the last implication for both unequal and equal sample sizes, so
the first assertion must be false.

## How to read and verify the proof

The proof has three modules.

| Module | What it establishes | Main tools |
|---|---|---|
| [Raw-sample and density bridge](reader_density_bridge.md) | Reduction from the raw normal samples to a one-parameter experiment and derivation of its exact density | Normal sample theory, Gamma densities, a Jacobian, the Gamma integral |
| [Limiting-Bayes bridge](reader_limiting_bayes_bridge.md) | Admissibility would force a probability $\nu$ satisfying the posterior-mean identity $(\star)$ below | Lehmann--Casella 5.7.15, Bayes' formula, weak convergence, continuity |
| [ODE, moments, and contradictions](reader_ode_moments.md) | No probability $\nu$ can satisfy $(\star)$, for unequal or equal sample sizes | An elementary ODE, differentiation of a transform, quotient rules |

Every custom algebraic identity is expanded in those modules. Each also
contains copy-pastable WolframAlpha queries. The present file gives the
continuous logical spine, so that it is clear exactly how the modules fit
together.

---

## 1. Reduction to estimating a variance ratio

Put

$$
v_i=\frac{\sigma_i^2}{n_i},\qquad
\tau=v_1+v_2,\qquad
\theta=\frac{v_1}{\tau}.
$$

Then $\tau>0$, $0<\theta<1$, and conversely

$$
\sigma_1^2=n_1\tau\theta,\qquad
\sigma_2^2=n_2\tau(1-\theta).
$$

To check one-to-one explicitly, consider the map

$$
T:(0,\infty)^2\longrightarrow(0,\infty)\times(0,1),\qquad
T(\sigma_1^2,\sigma_2^2)=(\tau,\theta).
$$

By definition, \(T\) is one-to-one if

$$
T(\sigma_1^2,\sigma_2^2)
=T(\widetilde\sigma_1^2,\widetilde\sigma_2^2)
$$

implies

$$
(\sigma_1^2,\sigma_2^2)
=(\widetilde\sigma_1^2,\widetilde\sigma_2^2).
$$

Suppose the two variance pairs have the same image
\((\tau,\theta)\).  Applying the inverse formulas above to each pair gives

$$
\sigma_1^2=n_1\tau\theta=\widetilde\sigma_1^2,
\qquad
\sigma_2^2=n_2\tau(1-\theta)=\widetilde\sigma_2^2.
$$

Thus the two variance pairs are equal, which proves directly from the
definition that \(T\) is one-to-one.  Moreover, every
\((\tau,\theta)\in(0,\infty)\times(0,1)\) produces a positive variance pair
through the inverse formulas, so \(T\) is in fact a bijective
reparametrization.

Define

$$
D=\bar X_2-\bar X_1,\qquad
Y_i=\frac{S_i^2}{n_i},\qquad
r=\frac{Y_1}{Y_1+Y_2},\qquad
q=\frac{D^2}{Y_1+Y_2}.
$$

The commonly used definition of the two-sample Graybill--Deal estimator is
the inverse-estimated-variance weighted average

$$
\delta_{\mathrm{GD}}
=
\frac{(n_1/S_1^2)\bar X_1+(n_2/S_2^2)\bar X_2}
     {n_1/S_1^2+n_2/S_2^2}.
$$

Indeed, the variance of \(\bar X_i\) is
\(\operatorname{Var}(\bar X_i)=\sigma_i^2/n_i\), which is estimated by
\(S_i^2/n_i=Y_i\).  Thus \(n_i/S_i^2=Y_i^{-1}\) is the corresponding
estimated precision, and the definition can be written

$$
\delta_{\mathrm{GD}}
=
\frac{Y_1^{-1}\bar X_1+Y_2^{-1}\bar X_2}
     {Y_1^{-1}+Y_2^{-1}}.
$$

The coefficient of \(\bar X_2\) in this weighted average is

$$
\frac{Y_2^{-1}}{Y_1^{-1}+Y_2^{-1}}
=\frac{Y_1}{Y_1+Y_2}=r,
$$

while the coefficient of \(\bar X_1\) is

$$
\frac{Y_1^{-1}}{Y_1^{-1}+Y_2^{-1}}
=\frac{Y_2}{Y_1+Y_2}=1-r.
$$

Consequently,

$$
\begin{aligned}
\delta_{\mathrm{GD}}
&=(1-r)\bar X_1+r\bar X_2\\
&=\bar X_1+r(\bar X_2-\bar X_1)\\
&=\bar X_1+rD.
\end{aligned}
$$

The known-variance oracle is

$$
M=\bar X_1+\theta D.
$$

If $E=M-\mu$, elementary bivariate-normal calculations give

$$
E\perp(D,S_1^2,S_2^2),\qquad
E[E]=0,\qquad
\operatorname{Var}(E)=\tau\theta(1-\theta).
$$

For the variance calculation, first use

$$
E=M-\mu
=(1-\theta)(\bar X_1-\mu)+\theta(\bar X_2-\mu).
$$

The two sample means are independent, with variances \(v_1\) and \(v_2\).
Therefore

$$
\begin{aligned}
\operatorname{Var}(E)
&=(1-\theta)^2v_1+\theta^2v_2\\
&=(1-\theta)^2\tau\theta
  +\theta^2\tau(1-\theta)\\
&=\tau\theta(1-\theta)\{(1-\theta)+\theta\}\\
&=\tau\theta(1-\theta).
\end{aligned}
$$

For any measurable weight $\phi(r,q)$ of finite risk,

$$
\bar X_1+D\phi-\mu
=E+D(\phi-\theta).
$$

The cross term vanishes after squaring and taking expectations, so

$$
R_{\mu,\tau,\theta}(\bar X_1+D\phi)
=
\tau\theta(1-\theta)
+
\tau E_\theta\!\left[
\frac{D^2}{\tau}\{\phi(r,q)-\theta\}^2
\right].
\tag{1}
$$

Since $D/\sqrt\tau\sim N(0,1)$, the rule

$$
Q_\theta(C)
=
E_\theta\!\left[
\frac{D^2}{\tau}\mathbf 1_{\{(r,q)\in C\}}
\right]
\tag{2}
$$

defines a probability measure. Equation (1) becomes

$$
R_{\mu,\tau,\theta}(\bar X_1+D\phi)
=
\tau\theta(1-\theta)
+
\tau\int(\phi-\theta)^2\,dQ_\theta.
\tag{3}
$$

Therefore it is sufficient to show that the reduced rule

$$
\phi_0(r,q)=r
$$

is inadmissible for estimating $\theta$ under squared loss when
$(r,q)\sim Q_\theta$. Any reduced dominator $\phi$ lifts to the full-model
dominator $\bar X_1+D\phi$ through (3).

All independence and risk calculations in this section are expanded in
Sections 1--7 of `reader_density_bridge.md`.

---

## 2. Exact density of the reduced experiment

Set

$$
a=\frac{n_1-1}{2},\qquad
b=\frac{n_2-1}{2},\qquad
h=a+b,\qquad
p=h+\frac32.
$$

After dividing the scale variables by $\tau$,

$$
G_1=\frac{Y_1}{\tau}
\sim\operatorname{Gamma}\left(a,\text{ scale }\frac{\theta}{a}\right),
$$

$$
G_2=\frac{Y_2}{\tau}
\sim\operatorname{Gamma}\left(b,\text{ scale }\frac{1-\theta}{b}\right),
$$

and

$$
W=\frac{D^2}{\tau}\sim\chi_1^2.
$$

These three variables are independent. Weighting their joint law by $W$,
as in the definition of $Q_\theta$, changes the $\chi_1^2$ density into
the $\chi_3^2$ density.

Use

$$
G_1=rt,\qquad
G_2=(1-r)t,\qquad
W=qt.
$$

The absolute Jacobian is $t^2$. Integrating out $t$ with

$$
\int_0^\infty t^{p-1}e^{-At}\,dt=\frac{\Gamma(p)}{A^p}
$$

gives the exact density

$$
\boxed{
f_\theta^Q(r,q)
=
C_{a,b}r^{a-1}(1-r)^{b-1}q^{1/2}
\frac{\theta^{b+3/2}(1-\theta)^{a+3/2}}
     {B_\theta(r,q)^p}
}
\tag{4}
$$

on $0<r<1$, $q>0$, where

$$
C_{a,b}
=
\frac{2^p a^a b^b\Gamma(p)}
{\sqrt{2\pi}\Gamma(a)\Gamma(b)}
$$

and

$$
B_\theta(r,q)
=
2ar(1-\theta)+2b(1-r)\theta+q\theta(1-\theta).
\tag{5}
$$

The density is strictly positive for every observation and every
$0<\theta<1$. Its full derivation, including the crossed powers of
$\theta$, is in Sections 8--13 of `reader_density_bridge.md`.

---

## 3. What admissibility would imply

Suppose, for contradiction, that the reduced rule $r$ were admissible.
Apply Lehmann--Casella Theorem 5.7.15 with

$$
\mathcal X=(0,1)\times(0,\infty),\qquad
\Theta=(0,1),\qquad
L(\theta,d)=(d-\theta)^2.
$$

The theorem's assumptions hold:

1. Lebesgue measure on $\mathcal X$ is sigma-finite.
2. Equation (4) is a density relative to that measure and is everywhere
   positive.
3. Squared loss is continuous and strictly convex in $d$.
4. $(d-\theta)^2\to\infty$ as $|d|\to\infty$.

Moreover, \(r\) has finite reduced risk because \(0<r,\theta<1\) implies
\((r-\theta)^2\le1\).

Consequently, there are finite-support priors $\pi_j$ whose Bayes rules
$A_j(r,q)$ converge to $r$ for Lebesgue-almost every $(r,q)$.

Under squared loss, a Bayes action is the posterior mean. Factoring (4)
inside Bayes' formula gives

$$
A_j(r,q)
=
\frac{\int\theta w(\theta)B_\theta(r,q)^{-p}\,\pi_j(d\theta)}
     {\int w(\theta)B_\theta(r,q)^{-p}\,\pi_j(d\theta)},
\tag{6}
$$

where

$$
w(\theta)=\theta^{b+3/2}(1-\theta)^{a+3/2}.
$$

Define the reweighted probability

$$
\nu_j(d\theta)
=
\frac{w(\theta)\pi_j(d\theta)}
     {\int w\,d\pi_j}.
\tag{7}
$$

Regarding $\nu_j$ as probabilities on the compact interval $[0,1]$, pass
to a weakly convergent subsequence

$$
\nu_j\Rightarrow\nu.
$$

For fixed $0<r<1$ and $q\ge0$,

$$
B_\theta(r,q)
\ge
\min\{2ar,2b(1-r)\}>0.
$$

Thus $B_\theta^{-p}$ and $\theta B_\theta^{-p}$ are bounded continuous
functions of $\theta\in[0,1]$. Weak convergence passes both integrals in
(6) to the limit, and the limiting denominator is positive. Hence

$$
A_j(r,q)\longrightarrow
A_\nu(r,q)
:=
\frac{\int\theta B_\theta(r,q)^{-p}\,\nu(d\theta)}
     {\int B_\theta(r,q)^{-p}\,\nu(d\theta)}.
\tag{8}
$$

On the full-measure set supplied by Lehmann--Casella, the same sequence
converges to $r$. Therefore $A_\nu(r,q)=r$ almost everywhere. Both sides
are continuous in $(r,q)$, so equality holds everywhere for $q>0$.
Continuity as $q\downarrow0$ then gives

$$
\boxed{
A_\nu(r,q)=r
\quad\text{for every }0<r<1,\ q\ge0.
}
\tag{$\star$}
$$

Possible endpoint atoms of $\nu$ cause no problem because

$$
B_0(r,q)=2ar>0,\qquad
B_1(r,q)=2b(1-r)>0.
$$

Every step in this compactness argument, including the distinction between
sample-space almost-everywhere convergence and parameter-space weak
convergence, is expanded in `reader_limiting_bayes_bridge.md`.

---

## 4. Consequences of $(\star)$ on the boundary $q=0$

Put

$$
\lambda=p-1=h+\frac12
$$

and

$$
u_\theta(r)
=ar(1-\theta)+b(1-r)\theta,
$$

so that $B_\theta(r,0)=2u_\theta(r)$. Define

$$
I(r)=E_\nu[u_\theta(r)^{-p}],
\qquad
F(r)=E_\nu[u_\theta(r)^{-\lambda}].
$$

The identity $A_\nu(r,0)=r$ gives

$$
E_\nu[\theta u_\theta(r)^{-p}]=rI(r).
$$

Since

$$
u_\theta(r)=ar(1-\theta)+b(1-r)\theta,
$$

we obtain

$$
F(r)=hr(1-r)I(r).
\tag{9}
$$

Also

$$
\frac{\partial u_\theta(r)}{\partial r}=a-h\theta,
$$

and therefore

$$
F'(r)=-\lambda(a-hr)I(r).
\tag{10}
$$

Dividing (10) by (9),

$$
\frac{F'(r)}{F(r)}
=-\lambda
\left\{\frac{a}{hr}-\frac{b}{h(1-r)}\right\}.
$$

Solving this elementary ODE gives

$$
F(r)
=C r^{-\lambda a/h}(1-r)^{-\lambda b/h}.
\tag{11}
$$

Now define

$$
r_0=\frac{b}{h},\qquad
c=\frac{ab}{h},\qquad
Z=a-h\theta.
$$

At $r=r_0$, $u_\theta(r_0)=c$ independently of $\theta$. Put
$r=r_0+ct$ and divide (11) by its value at $r_0$. This yields

$$
\boxed{
E_\nu[(1+tZ)^{-\lambda}]
=(1+at)^{-\lambda a/h}(1-bt)^{-\lambda b/h}.
}
\tag{12}
$$

The identity holds for

$$
-\frac1a<t<\frac1b,
$$

which is exactly the condition \(0<r_0+ct<1\). This interval also keeps
\(1+tZ>0\) for every \(Z\in[-b,a]\).

The derivation of (9)--(12), including differentiation under the integral
sign, is in Parts I--II of `reader_ode_moments.md`.

---

## 5. Unequal sample sizes

Assume $a\ne b$, equivalently $n_1\ne n_2$. Differentiating (12) three
times at zero gives

$$
E[Z]=a-b,
\tag{13}
$$

$$
E[Z^2]
=
\frac{a^2-ab+b^2+\lambda(a-b)^2}{\lambda+1},
\tag{14}
$$

and

$$
E[Z^3]
=
\frac{(a-b)
\{2(a^2+b^2)+3\lambda(a^2-ab+b^2)
                  +\lambda^2(a-b)^2\}}
     {(\lambda+1)(\lambda+2)}.
\tag{15}
$$

Because

$$
\theta=\frac{a-Z}{h},\qquad
\theta-r_0=\frac{a-b-Z}{h},\qquad
1-\theta=\frac{b+Z}{h},
$$

substitution of (13)--(15) gives

$$
\boxed{
E_\nu[(\theta-r_0)\theta(1-\theta)]
=
\frac{2ab(a-b)(2h+1)}
{h^3(2h+3)(2h+5)}.
}
\tag{16}
$$

At $(r,q)=(r_0,0)$, equation (5) has the constant value

$$
B_\theta(r_0,0)=\frac{2ab}{h}=2c.
$$

Differentiating the quotient (8) from the right in $q$ gives

$$
\partial_{q+}A_\nu(r_0,0)
=
-\frac{p}{2c}
E_\nu[(\theta-r_0)\theta(1-\theta)].
$$

Using (16),

$$
\boxed{
\partial_{q+}A_\nu(r_0,0)
=
-\frac{(a-b)(2h+1)}
       {2h^2(2h+5)}
\ne0.
}
\tag{17}
$$

But $(\star)$ says $A_\nu(r_0,q)=r_0$, a constant function of $q$, whose
right derivative must be zero. This is a contradiction.

Parts III--V of `reader_ode_moments.md` derive every line of
(13)--(17), including the polynomial expansion behind (16).

---

## 6. Equal sample sizes

It remains to consider $a=b$, equivalently $n_1=n_2$. The derivative in
(17) then vanishes by symmetry.

Put

$$
Y=1-2\theta.
$$

The transform (12) becomes

$$
E_\nu[(1+sY)^{-\lambda}]
=(1-s^2)^{-\lambda/2}.
\tag{18}
$$

Comparing the coefficients of $s^2$ and $s^4$, with $p=\lambda+1$, gives

$$
E[Y^2]=\frac1p,\qquad
E[Y^4]=\frac3{p(p+2)}.
\tag{19}
$$

In these centered coordinates,

$$
B_\theta(r,q)
=
a+2a\left(r-\frac12\right)Y
+\frac q4(1-Y^2).
\tag{20}
$$

Differentiate the numerator and denominator in (8), first in $r$ and
then from the right in $q$, at $(r,q)=(1/2,0)$. Substitution of (19)
gives

$$
\boxed{
\partial_{q+}\partial_r A_\nu(1/2,0)
=
\frac{p-1}{4a(p+2)}>0.
}
\tag{21}
$$

But $(\star)$ says $A_\nu(r,q)=r$. Its derivative in $r$ is identically
$1$, whose derivative in $q$ is zero. Equation (21) is the required
contradiction.

Part VI of `reader_ode_moments.md` derives (18)--(21), including every
quotient-rule term and the two moment substitutions.

---

## 7. Conclusion

For every $n_1,n_2\ge2$, exactly one of the following holds:

1. $n_1\ne n_2$, in which case (17) contradicts $(\star)$;
2. $n_1=n_2$, in which case (21) contradicts $(\star)$.

Therefore the reduced rule $r$ cannot be admissible. By the definition of
inadmissibility, there exists a reduced rule $\phi$ whose squared risk is
no larger for every $\theta\in(0,1)$ and strictly smaller for at least one
$\theta$. Equation (3) lifts it to the estimator

$$
\delta_\phi=\bar X_1+D\phi(r,q),
$$

which dominates Graybill--Deal for all $\mu\in\mathbb R$ and all positive
variance pairs, with strict improvement somewhere. Hence Graybill--Deal is
inadmissible.

The estimator $\phi$ may depend on the fixed pair $(n_1,n_2)$; the theorem
does not assert that the same rule works simultaneously for every choice
of sample sizes.

---

## 8. Suggested verification order

1. Verify the ordinary Graybill--Deal algebra and the oracle decomposition.
2. Verify the Gamma laws, the $t^2$ Jacobian, and density (4).
3. Read Lehmann--Casella Theorem 5.7.15 and compare its hypotheses with
   Section 3.
4. Verify the reweighting (7) and the two weak limits in (8).
5. Verify the ODE (9)--(11).
6. Use WolframAlpha to differentiate transform (12) three times and check
   (13)--(16).
7. Verify the one quotient derivative leading to (17).
8. On the diagonal, compare the $s^2,s^4$ coefficients in (18) and check
   the quotient-rule calculation yielding (21).

The consolidated symbolic checker
`verify_graybill_deal_universal_reader.py` verifies the density Jacobian
and exponents, the unequal obstruction (16)--(17), the equal obstruction
(19)--(21), and the special constants. It deliberately does not attempt to
verify the Lehmann--Casella theorem.

## 9. Status and scope

The proof has been reconstructed independently in its probability,
decision-theory, and analytic parts and checked symbolically. Because the
conclusion is unusually strong and potentially resolves a longstanding
question, independent review by a specialist in statistical decision
theory remains prudent.

The theorem concerns:

- exactly two independent normal populations;
- a common unknown mean;
- arbitrary positive population variances;
- ordinary squared-error loss;
- fixed sample sizes $n_1,n_2\ge2$.

It does not cover sample size $1$, where the usual unbiased sample variance
is unavailable.
