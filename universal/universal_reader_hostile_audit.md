# Hostile audit of the expanded universal Graybill--Deal proof

## Verdict

I checked the following three modules as one continuous argument:

1. `reader_density_bridge.md`;
2. `reader_limiting_bayes_bridge.md`;
3. `reader_ode_moments.md`.

**I found no mathematical error.** Subject to the quoted
Lehmann--Casella limiting-Bayes theorem, the three modules form a valid
nonconstructive proof that the Graybill--Deal estimator is inadmissible for
every pair of sample sizes

$$
n_1,n_2\geq2.
$$

In particular, I independently checked:

- the exact risk reduction from the raw samples;
- the full normalized density of the risk-weighted experiment, including
  its constant and its crossed powers of \(\theta\);
- every hypothesis used from Lehmann--Casella;
- the reweighting and weak compactness argument, including possible endpoint
  mass;
- the passage from almost-everywhere equality to pointwise equality and then
  to the boundary \(q=0\);
- the \(q=0\) ODE and moment transform;
- the unequal-size \(q\)-derivative;
- the equal-size mixed derivative;
- the final lifting of reduced inadmissibility back to the original normal
  problem.

The repairs suggested at the end of this audit are expository rather than
logical. None changes a formula or an inference.

---

## 1. Audit of the raw-sample and risk bridge

Write

$$
v_i=\frac{\sigma_i^2}{n_i},\qquad
\tau=v_1+v_2,\qquad
\theta=\frac{v_1}{\tau}.
$$

Then \(v_1=\theta\tau\), \(v_2=(1-\theta)\tau\), and

$$
D=\bar X_2-\bar X_1\sim N(0,\tau).
$$

The proposed oracle error is

$$
E=(1-\theta)(\bar X_1-\mu)+\theta(\bar X_2-\mu).
$$

Direct calculation gives

$$
\operatorname{Cov}(E,D)
=-(1-\theta)v_1+\theta v_2=0
$$

and

$$
\operatorname{Var}(E)
=(1-\theta)^2v_1+\theta^2v_2
=\tau\theta(1-\theta).
$$

Because \((E,D)\) is jointly normal, zero covariance gives \(E\perp D\).
Normal-sample mean/variance independence, followed by independence of the
two samples, gives

$$
E\perp(D,S_1^2,S_2^2).
$$

Thus, for every measurable \(\phi(r,q)\) having finite risk,

$$
\bar X_1+D\phi-\mu=E+D(\phi-\theta)
$$

and the cross term has expectation zero. Therefore

$$
R_{\mu,\tau,\theta}(\bar X_1+D\phi)
=\tau\theta(1-\theta)
 +\tau E_\theta[D_0^2(\phi-\theta)^2],
\qquad D_0=\frac D{\sqrt\tau}.
$$

The plus sign between the two terms is important and is present in both
reader modules.

The Graybill--Deal coefficient of \(\bar X_2\) is indeed

$$
\frac{n_2/S_2^2}{n_1/S_1^2+n_2/S_2^2}
=\frac{S_1^2/n_1}{S_1^2/n_1+S_2^2/n_2}=r.
$$

Consequently, \(\delta_{\rm GD}=\bar X_1+rD\).

Since \(E D_0^2=1\),

$$
Q_\theta(C)=E_\theta[D_0^2\,1_{\{(r,q)\in C\}}]
$$

is a probability measure. If \(\psi\) dominates \(r\) under squared loss in
this experiment, then

$$
\delta_\psi=\bar X_1+D\psi(r,q)
$$

dominates Graybill--Deal in the original experiment after multiplying the
reduced risk inequality by \(\tau>0\) and adding the common oracle risk.
Strictness at one \(\theta\) gives strictness for that \(\theta\), every
\(\mu\), and every \(\tau>0\). This is enough for ordinary inadmissibility.

This verifies the direction actually used:

$$
\text{original admissibility}
\ \Longrightarrow\
\text{admissibility of }r\text{ in the reduced experiment}.
$$

It is not necessary to show that every estimator in the original experiment
has the displayed form.

---

## 2. Independent audit of the full \(Q_\theta\)-density

Put

$$
a=\frac{n_1-1}{2},\qquad b=\frac{n_2-1}{2},\qquad
p=a+b+\frac32.
$$

After normalization by \(\tau\),

$$
G_1=\frac{S_1^2/n_1}{\tau}
=\frac{\theta U_1}{2a},\qquad
G_2=\frac{S_2^2/n_2}{\tau}
=\frac{(1-\theta)U_2}{2b},
$$

where \(U_1\sim\chi^2_{2a}\), \(U_2\sim\chi^2_{2b}\). Hence

$$
G_1\sim\operatorname{Gamma}\left(a,\frac{\theta}{a}\right),
\qquad
G_2\sim\operatorname{Gamma}\left(b,\frac{1-\theta}{b}\right),
$$

with the second argument denoting scale. Also

$$
W=D_0^2\sim\chi^2_1.
$$

The \(Q_\theta\)-weight is \(W\). It changes

$$
\frac{1}{\sqrt{2\pi}}w^{-1/2}e^{-w/2}
$$

into

$$
\frac{1}{\sqrt{2\pi}}w^{1/2}e^{-w/2},
$$

which is exactly the \(\chi^2_3\) density.

Under

$$
G_1=rt,\qquad G_2=(1-r)t,\qquad W=qt,
$$

the Jacobian matrix has determinant \(-t^2\), so the absolute Jacobian is
\(t^2\). The power of \(t\) is

$$
(a-1)+(b-1)+\frac12+2
=a+b+\frac12=p-1.
$$

The exponential rate is

$$
A_\theta(r,q)
=\frac{ar}{\theta}
 +\frac{b(1-r)}{1-\theta}
 +\frac q2.
$$

Integrating \(t^{p-1}e^{-A_\theta t}\) over \(t>0\) gives
\(\Gamma(p)A_\theta^{-p}\). Since

$$
A_\theta(r,q)
=\frac{B_\theta(r,q)}{2\theta(1-\theta)},
$$

where

$$
B_\theta(r,q)
=2ar(1-\theta)+2b(1-r)\theta+q\theta(1-\theta),
$$

the powers left after multiplication by the original Gamma normalizers are

$$
\theta^{p-a}=\theta^{b+3/2},\qquad
(1-\theta)^{p-b}=(1-\theta)^{a+3/2}.
$$

Thus the density and its constant are exactly

$$
f_\theta^Q(r,q)
=
\frac{2^p a^a b^b\Gamma(p)}
{\sqrt{2\pi}\Gamma(a)\Gamma(b)}
r^{a-1}(1-r)^{b-1}q^{1/2}
\frac{\theta^{b+3/2}(1-\theta)^{a+3/2}}
{B_\theta(r,q)^p}.
$$

I also numerically integrated this density for

$$
(a,b,\theta)=\left(\frac12,1,0.37\right)
$$

and obtained \(0.999999999922604\). This is only a numerical cross-check;
normalization already follows rigorously from the normalized product density
and the bijective change of variables.

At \(a=1/2,b=1,p=3\), the constant simplifies to

$$
\frac{2^3(1/2)^{1/2}\Gamma(3)}
{\sqrt{2\pi}\Gamma(1/2)\Gamma(1)}
=\frac8\pi.
$$

Every density factor is finite and strictly positive at every
\(0<r<1,q>0,0<\theta<1\), even when \(a<1\). The density may be unbounded
as \(r\) approaches the boundary, but the boundary is not part of the open
sample space and boundedness is not a hypothesis of the theorem.

---

## 3. Audit of the Lehmann--Casella application

The quoted result appears in Chapter 5, Section 7 as printed Theorem 7.15
(often referenced in full as Theorem 5.7.15). It requires:

1. a density relative to a sigma-finite measure;
2. strict positivity \(f_\theta(x)>0\) for every sample point and parameter;
3. loss continuous in its arguments;
4. loss strictly convex in the action;
5. loss tending to infinity as the magnitude of the action tends to
   infinity.

All five hypotheses hold:

- two-dimensional Lebesgue measure on
  \((0,1)\times(0,\infty)\) is sigma-finite;
- the density above is everywhere positive on that open sample space;
- \(L(\theta,d)=(d-\theta)^2\) is continuous;
- \(L_{dd}=2>0\);
- \(L(\theta,d)\to\infty\) as \(|d|\to\infty\).

The action space is correctly taken to be \(\mathbb R\). This avoids the
mistake of applying the printed coercivity condition after restricting the
action space to \([0,1]\).

Also, the candidate rule \(r\) has finite risk:

$$
0<r,\theta<1
\quad\Longrightarrow\quad
(r-\theta)^2\leq1.
$$

Under assumed admissibility, the theorem therefore supplies finite-support
priors \(\pi_j\) whose Bayes actions converge to \(r\) Lebesgue-almost
everywhere in the **sample space**. Each finite-prior marginal density is
positive everywhere, so its unique posterior-mean Bayes action has the
canonical ratio version used in the module at every sample point.

No invariant-prior theorem, exponential-family theorem, or compact-action
complete-class theorem is being smuggled into this step.

---

## 4. Audit of reweighting, compactness, and endpoint escape

Bayes' formula contains the factor

$$
w(\theta)=\theta^{b+3/2}(1-\theta)^{a+3/2}.
$$

All support points of each \(\pi_j\) are in \((0,1)\), so

$$
Z_j=\int w\,d\pi_j>0.
$$

The measures

$$
\nu_j=\frac{w\,\pi_j}{Z_j}
$$

are probabilities. It is immaterial if \(Z_j\to0\), because it cancels
inside the posterior ratio.

After extending each \(\nu_j\) by zero mass at the endpoints,
sequential compactness of the probability measures on compact \([0,1]\)
gives a weakly convergent subsequence \(\nu_j\Rightarrow\nu\).
Endpoint escape is allowed: \(\nu\) may charge \(0\) or \(1\).

For fixed \(0<r<1,q\geq0\),

$$
B_\theta(r,q)
\geq \min\{2ar,2b(1-r)\}>0.
$$

Therefore \(B_\theta^{-p}\) and
\(\theta B_\theta^{-p}\) are bounded continuous functions on the entire
compactified parameter interval. Weak convergence applies to numerator and
denominator separately, and the limiting denominator is positive.
Consequently the posterior ratios converge pointwise to \(A_\nu(r,q)\).

The same subsequence still converges to \(r\) on the full-measure set supplied
by Lehmann--Casella. Uniqueness of limits gives \(A_\nu=r\) almost
everywhere. Both sides are continuous on the open sample space, so equality
holds everywhere there: a nonzero value of their continuous difference
would persist on an open set of positive Lebesgue measure.

Finally, dominated convergence as \(q\downarrow0\) extends the identity to

$$
A_\nu(r,0)=r,\qquad 0<r<1.
$$

At the endpoints of the compactified parameter space,

$$
B_0(r,q)=2ar,\qquad
B_1(r,q)=2b(1-r),
$$

so endpoint atoms produce finite contributions. They create neither a
zero denominator nor a differentiation problem. This closes the most
plausible compactification gap.

---

## 5. Audit of the \(q=0\) ODE and moment transform

Set

$$
h=a+b,\qquad \lambda=p-1=h+\frac12,
$$

and

$$
u_\theta(r)=ar(1-\theta)+b(1-r)\theta.
$$

At \(q=0\), the factor \(2^{-p}\) cancels. If

$$
I(r)=E[u^{-p}],\qquad F(r)=E[u^{-\lambda}],
$$

then \(A_\nu(r,0)=r\) gives

$$
E[\theta u^{-p}]=rI,\qquad
E[(1-\theta)u^{-p}]=(1-r)I.
$$

Since \(u^{-\lambda}=u\,u^{-p}\),

$$
F=hr(1-r)I.
$$

Also \(u_r=a-h\theta\), so

$$
F'=-\lambda(a-hr)I.
$$

Division yields

$$
\frac{F'}F
=-\lambda\left\{\frac{a}{hr}
                 -\frac{b}{h(1-r)}\right\},
$$

and hence

$$
F(r)=C_0r^{-\lambda a/h}(1-r)^{-\lambda b/h}.
$$

Now put

$$
r_0=\frac bh,\qquad c=\frac{ab}{h},\qquad Z=a-h\theta.
$$

Then

$$
u_\theta(r_0)=c,\qquad
u_\theta(r_0+ct)=c(1+tZ),
$$

while

$$
\frac{r_0+ct}{r_0}=1+at,\qquad
\frac{1-r_0-ct}{1-r_0}=1-bt.
$$

Dividing the ODE solution at \(r_0+ct\) by its value at \(r_0\) cancels
\(C_0\) and gives

$$
E(1+tZ)^{-\lambda}
=(1+at)^{-\lambda a/h}(1-bt)^{-\lambda b/h}.
$$

The natural full interval here is

$$
-\frac1a<t<\frac1b.
$$

On this interval \(r_0+ct\in(0,1)\), and since
\(-b\leq Z\leq a\), one also has \(1+tZ>0\). Only a neighborhood of zero is
needed for the moment calculations.

Logarithmic differentiation of the right side gives

$$
\ell'(0)=-\lambda(a-b),
$$

$$
\ell''(0)=\lambda(a^2-ab+b^2),
$$

and

$$
\ell'''(0)=-2\lambda(a-b)(a^2+b^2).
$$

Using

$$
G'''=G\{\ell'''+3\ell'\ell''+(\ell')^3\}
$$

and equating derivatives with those of
\(E(1+tZ)^{-\lambda}\) reproduces exactly the three moments stated in the
reader module. I also reran the supplied symbolic checker with

```text
PYTHONPATH=.python_deps python verify_limiting_bayes_universal.py
```

and obtained the advertised general obstruction and both specializations.

---

## 6. Audit of the unequal-size derivative

The algebraic expansion

$$
(\theta-r_0)\theta(1-\theta)
=\frac{(a-b-Z)(a-Z)(b+Z)}{h^3}
$$

combined with the first three moments gives

$$
E[(\theta-r_0)\theta(1-\theta)]
=
\frac{2ab(a-b)(2h+1)}
{h^3(2h+3)(2h+5)}.
$$

At \(r=r_0,q=0\), \(B_\theta=2ab/h\), independently of \(\theta\).
Applying the quotient rule gives

$$
\partial_{q+}A_\nu(r_0,0)
=-\frac{p}{2ab/h}
E[(\theta-r_0)\theta(1-\theta)],
$$

and therefore

$$
\boxed{
\partial_{q+}A_\nu(r_0,0)
=-\frac{(a-b)(2h+1)}
{2h^2(2h+5)}.
}
$$

This is nonzero if and only if \(a\ne b\). Since
\(A_\nu(r_0,q)=r_0\) for every \(q\geq0\), its right derivative must be
zero. The unequal-size contradiction is valid.

For the concrete check \(a=1/2,b=1\), the two sides are

$$
E[(\theta-\tfrac23)\theta(1-\theta)]=-\frac1{81},
\qquad
\partial_{q+}A_\nu(2/3,0)=\frac1{18},
$$

in agreement with the symbolic checker.

---

## 7. Audit of the equal-size mixed derivative

Set \(a=b\),

$$
p=2a+\frac32,\qquad \lambda=p-1,
\qquad Y=1-2\theta.
$$

The transform becomes

$$
E(1+sY)^{-\lambda}=(1-s^2)^{-\lambda/2}.
$$

Comparing the second and fourth derivatives at zero gives

$$
E[Y^2]=\frac1p,\qquad
E[Y^4]=\frac3{p(p+2)},
$$

while the first and third moments vanish.

With \(x=r-1/2\) and \(C=(1-Y^2)/4\),

$$
B_\theta(r,q)=a+2axY+qC.
$$

At \(x=q=0\),

$$
\mathcal D=a^{-p},\qquad
\mathcal D_r=0,\qquad
\mathcal D_{rq}=0,
$$

$$
\mathcal N_r=p\,a^{-p}E[Y^2],
$$

$$
\mathcal D_q=-p\,a^{-p-1}E[C],
$$

and

$$
\mathcal N_{rq}
=-p(p+1)a^{-p-1}E[Y^2C].
$$

The quotient rule consequently gives

$$
A_{rq}
=\frac pa\{- (p+1)E[Y^2C]
             +pE[Y^2]E[C]\}.
$$

Substitution of

$$
E[C]=\frac{1-E[Y^2]}4,\qquad
E[Y^2C]=\frac{E[Y^2]-E[Y^4]}4
$$

yields

$$
\boxed{
\partial_{q+}\partial_rA_\nu(1/2,0)
=\frac{p-1}{4a(p+2)}>0.
}
$$

But \(A_\nu(r,q)=r\) makes \(A_r=1\) for all \(q\geq0\), so the same mixed
right derivative must be zero. The equal-size contradiction is valid.

Although \(q=0\) is a boundary of the statistical sample space, the ratio of
integrals extends differentiably to a neighborhood of \(q=0\): at the
unequal central point \(B=2ab/h\), and at the equal central point \(B=a\).
Thus one may either interpret the displayed derivatives as right derivatives
or as ordinary derivatives of that local analytic extension.

---

## 8. Final logic

The complete implication chain is

$$
\begin{aligned}
\delta_{\rm GD}\text{ admissible in the original experiment}
&\Longrightarrow
r\text{ admissible in the reduced }Q_\theta\text{-experiment}\\
&\Longrightarrow
\text{finite-prior Bayes rules }A_j\to r\text{ a.e.}\\
&\Longrightarrow
\text{a probability }\nu\text{ satisfying }A_\nu(r,q)=r\\
&\Longrightarrow
\begin{cases}
\partial_{q+}A_\nu(r_0,0)\ne0,&a\ne b,\\
\partial_{q+}\partial_rA_\nu(1/2,0)>0,&a=b,
\end{cases}
\end{aligned}
$$

where the last line contradicts \(A_\nu(r,q)=r\).

Since \(a,b>0\) is equivalent to \(n_1,n_2\geq2\), the contradiction covers
every permitted pair of sample sizes.

This is a nonconstructive argument. It establishes that a reduced dominator,
and therefore an original-sample dominator, exists; it does not provide a
closed formula for that dominator.

---

## 9. Minimal suggested reader-clarity repairs

I would make the following small additions before presenting the modules as
one reader edition:

1. **Give the complete implication chain near the beginning.**  
   The chain in Section 8 above helps prevent the reader from confusing
   admissibility in the original three-parameter experiment with
   admissibility in the reduced one-parameter experiment.

2. **Clarify the theorem number.**  
   Write “Chapter 5, Section 7, printed Theorem 7.15 (full reference
   5.7.15).” This avoids confusion when the PDF itself displays
   “Theorem 7.15.”

3. **State finite risk of the candidate reduced rule.**  
   Add the one-line bound \((r-\theta)^2\leq1\). It is not a missing
   hypothesis in the current reasoning, but it reassures the reader that
   no extended-risk pathology is present.

4. **Give the exact \(t\)-interval in the moment transform.**  
   Replace “for sufficiently small \(t\)” by the stronger explicit statement
   \(-1/a<t<1/b\), followed by the observation
   \(Z\in[-b,a]\). This makes all differentiations visibly safe.

5. **Use “right derivative” consistently at \(q=0\).**  
   Alternatively, add one sentence that the integral ratio has a
   differentiable extension to small negative \(q\) near each central point.

6. **Define domination once.**  
   A reader-facing preface could say that “dominates” means no larger risk at
   every \((\mu,\sigma_1^2,\sigma_2^2)\), with strict inequality at at least
   one parameter point.

These are readability improvements only. I found no step requiring a new
lemma, a changed constant, or an altered conclusion.

