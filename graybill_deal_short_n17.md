# A short proof that the Graybill–Deal estimator is inadmissible ($n_1=n_2=17$)

### *Annotated working copy*

This is a copy of `graybill_deal_n17/graybill_deal_short_proof_n17.md` with
supporting detail added. **The originals in that directory are untouched.**

Added material is marked

> **[Annotation]**

so that the original argument can be read on its own by skipping those blocks.
The only substantive insertion so far expands the one-paragraph justification of
the oracle decomposition — the step where `Cov(T,D) = 0` and the independence of
`T` from `(D,S_1^2,S_2^2)` are asserted — into a full proof, together with an
appendix proving the Gaussian facts it uses. A verification log is at the end.

---

Consider two independent samples of size $17$,

$$
X_{ij}\sim N(\mu,\sigma_i^2),
\qquad i=1,2,\quad j=1,\ldots,17,
$$

where $\mu\in\mathbb R$ and $\sigma_1^2,\sigma_2^2>0$ are unknown. Let
$S_i^2$ denote the usual unbiased sample variance, and put

$$
D=\overline X_2-\overline X_1,\qquad
r=\frac{S_1^2}{S_1^2+S_2^2},\qquad
q=\frac{17D^2}{S_1^2+S_2^2}.
$$

The Graybill–Deal estimator is

$$
\widehat\mu_{\mathrm{GD}}=\overline X_1+Dr.
$$

Define $p(r)=r(1-r)(1-2r)$ and

$$
\widehat\mu_*
=
\overline X_1+
D\left\{
r+\frac1{2000}p(r)(4-q)
\right\}.
$$

Set $r=q=0$ on $\{S_1^2+S_2^2=0\}$, which is a null event.

> **[Annotation]** $S_1^2+S_2^2=0$ occurs only when every sample observation is
> equal exactly to the sample mean. This means within each sample, all sample
> observations are exactly equal, which happens with probability zero.

## Theorem

For every $\mu\in\mathbb R$ and every $\sigma_1^2,\sigma_2^2>0$,

$$
R(\mu,\sigma_1^2,\sigma_2^2;\widehat\mu_*)
<
R(\mu,\sigma_1^2,\sigma_2^2;\widehat\mu_{\mathrm{GD}})
$$

under squared-error loss. Hence the Graybill–Deal estimator is inadmissible
when the two sample sizes are both $17$.

## Proof

Set

$$
\theta=\frac{\sigma_1^2}{\sigma_1^2+\sigma_2^2},
\qquad
\lambda=\frac{\sigma_1^2+\sigma_2^2}{17}
=\operatorname{Var}(D).
$$

If $X$ and $Y$ are independent:

$\operatorname{Var}(X-Y)=\operatorname{Var}(X)+\operatorname{Var}(Y)$

$\operatorname{Var}(\bar{X}_i)=\frac{\sigma_i^2}{17}$

The known-variance estimator

$$
T=\overline X_1+\theta D
$$

is independent of $(D,S_1^2,S_2^2)$ and satisfies
$\mathbb E(T-\mu)=0$. Indeed, the sample means are jointly normal,
$\operatorname{Cov}(T,D)=0$, and the sample means are independent of the
sample variances. Therefore, for every weight
$w=w(D,S_1^2,S_2^2)$ of finite risk,

$$
R(\overline X_1+Dw)
=
\mathbb E\!\left[(T-\mu)^2\right]
+\mathbb E\!\left[D^2(w-\theta)^2\right].
\tag{$*$}
$$

> **[Annotation] Proof of $(*)$ in detail.**
>
> Since $D=\overline X_2-\overline X_1$, both $T-\mu$ and $D$ are affine
> functions of the pair of sample means:
>
> $$T-\mu = \overline X_1+\theta D-\mu=(1-\theta)\overline X_1+\theta\overline X_2-\mu. \tag{A.1}$$
>
> Recall $\overline X_i\sim N(\mu,\sigma_i^2/17)$, and that $\overline X_1$ and
> $\overline X_2$ are independent because the two samples are.
>
> **(i) $\mathbb E(T-\mu)=0$.** By (A.1),
> $\mathbb E(T-\mu)=(1-\theta)\mu+\theta\mu-\mu=0$, since the weights sum to 1.
>
> **(ii) $\operatorname{Cov}(T,D)=0$.** Covariance is unaffected by the additive
> constant $-\mu$ and is bilinear, so
>
> $$\operatorname{Cov}(T,D)=\operatorname{Cov}\big((1-\theta)\overline X_1+\theta\overline X_2,\ \overline X_2-\overline X_1\big)$$
> $$=(1-\theta)\operatorname{Cov}(\overline X_1,\overline X_2)-(1-\theta)\operatorname{Var}(\overline X_1)+\theta\operatorname{Var}(\overline X_2)-\theta\operatorname{Cov}(\overline X_2,\overline X_1).$$
>
> The two covariance terms vanish by independence of the samples, leaving
>
> $$\operatorname{Cov}(T,D)=\theta\frac{\sigma_2^2}{17}-(1-\theta)\frac{\sigma_1^2}{17}
> =\frac1{17}\cdot\frac{\sigma_1^2\sigma_2^2-\sigma_2^2\sigma_1^2}{\sigma_1^2+\sigma_2^2}=0,$$
>
> on substituting $\theta=\sigma_1^2/(\sigma_1^2+\sigma_2^2)$ and
> $1-\theta=\sigma_2^2/(\sigma_1^2+\sigma_2^2)$.
>
> *This is the only place the choice of $\theta$ is used, and it is no accident.*
> The condition $\theta\sigma_2^2=(1-\theta)\sigma_1^2$ just derived is the
> stationarity condition of
>
> $$\operatorname{Var}\big((1-\theta)\overline X_1+\theta\overline X_2\big)
> =(1-\theta)^2\frac{\sigma_1^2}{17}+\theta^2\frac{\sigma_2^2}{17},$$
>
> whose derivative in $\theta$ is
> $\tfrac2{17}\big(\theta\sigma_2^2-(1-\theta)\sigma_1^2\big)$. So $\theta$ is
> the variance-minimising — that is, inverse-variance, or "oracle" — weight, and
> $\operatorname{Cov}(T,D)=0$ is precisely its first-order condition. It is the
> population version of the quantity Graybill–Deal estimates by $r$.
>
> **(iii) $T$ and $D$ are independent.** This needs care, since joint normality
> does *not* follow from normality of the marginals, and both $T$ and $D$ are
> built from both samples.
>
> *(iii-a) $(\overline X_1,\overline X_2)$ is jointly normal.* By Lemma B.1
> below, a random vector $W$ is multivariate normal precisely when
> $\alpha^{\mathsf T}W$ is univariate normal for every fixed $\alpha$. For any
> $\alpha_1,\alpha_2$ the variable
> $\alpha_1\overline X_1+\alpha_2\overline X_2$ is a sum of two **independent**
> normal variables, hence normal by Lemma B.3. So
> $(\overline X_1,\overline X_2)$ is bivariate normal, with
>
> $$(\overline X_1,\overline X_2)\sim N_2\!\left(\begin{pmatrix}\mu\\\mu\end{pmatrix},\ \Sigma\right),
> \qquad \Sigma=\operatorname{diag}\!\left(\frac{\sigma_1^2}{17},\ \frac{\sigma_2^2}{17}\right).$$
>
> This is the step that uses independence of the two samples, and it is exactly
> what marginal normality alone would fail to give.
>
> *(iii-b) $(T-\mu,D)$ is jointly normal.* By (A.1) both coordinates are affine
> functions of $(\overline X_1,\overline X_2)$, so any linear combination of them
> is an affine function of $(\overline X_1,\overline X_2)$, hence normal by
> (iii-a); apply Lemma B.1 again. Explicitly,
>
> $$\begin{pmatrix}T-\mu\\ D\end{pmatrix}
> =M\begin{pmatrix}\overline X_1\\ \overline X_2\end{pmatrix}+\begin{pmatrix}-\mu\\ 0\end{pmatrix},
> \qquad M=\begin{pmatrix}1-\theta & \theta\\ -1 & 1\end{pmatrix},$$
>
> so by Lemma B.2 the covariance matrix of $(T-\mu,D)$ is $M\Sigma M^{\mathsf T}$.
> (Equivalently, use the transformation rule
> $\operatorname{Cov}(AZ+b)=A\operatorname{Cov}(Z)A^{\mathsf T}$: the shift $b$
> cancels in the centring, so with $Y=Z-\mathbb E Z$,
> $\operatorname{Cov}(AZ+b)=\mathbb E[(AY)(AY)^{\mathsf T}]=A\,\mathbb E[YY^{\mathsf T}]\,A^{\mathsf T}$,
> using $(AY)^{\mathsf T}=Y^{\mathsf T}A^{\mathsf T}$ and the fact that constant
> matrices pass through the expectation.) Carrying out the multiplication,
>
> $$M\Sigma M^{\mathsf T}=
> \begin{pmatrix}
> \dfrac{\sigma_1^2\sigma_2^2}{17(\sigma_1^2+\sigma_2^2)} & 0\\[2mm]
> 0 & \dfrac{\sigma_1^2+\sigma_2^2}{17}
> \end{pmatrix}. \tag{A.2}$$
>
> The vanishing off-diagonal entry is the computation of (ii) again. Note the
> lower-right entry **proves the assertion $\lambda=\operatorname{Var}(D)$** made
> at the start of the proof; since $D$ is normal with mean $0$, it follows that
> $D/\sqrt\lambda$ is standard normal and hence $V=D^2/\lambda\sim\chi^2_1$, as
> used later. The upper-left entry gives
> $\mathbb E[(T-\mu)^2]=\sigma_1^2\sigma_2^2/(17(\sigma_1^2+\sigma_2^2))$, the
> oracle risk; it does not involve $w$, which is why comparing two estimators of
> the form $\overline X_1+Dw$ reduces to comparing
> $\mathbb E[D^2(w-\theta)^2]$.
>
> *(iii-c) Zero covariance now gives independence.* Both diagonal entries of
> (A.2) are strictly positive because $\sigma_1^2,\sigma_2^2>0$, so the
> covariance matrix $\Lambda$ of $(T-\mu,D)$ is nonsingular and the pair has the
> density $(2\pi)^{-1}(\det\Lambda)^{-1/2}\exp\big(-\tfrac12(w-m)^{\mathsf T}\Lambda^{-1}(w-m)\big)$,
> where $w\in\mathbb R^2$ is the argument and $m$ is the mean vector. Here
> $m=(0,0)^{\mathsf T}$: the first coordinate is $\mathbb E(T-\mu)=0$ by (i), and
> the second is $\mathbb E D=\mathbb E\overline X_2-\mathbb E\overline X_1=\mu-\mu=0$,
> both samples having the same mean. (Note $m$ is unrelated to the matrix $M$
> above, despite the letters.)
> Since $\Lambda$ is diagonal, so is $\Lambda^{-1}$, and the quadratic form splits
> as a sum of a term in the first coordinate and a term in the second (and since
> $m=0$ we may write $w$ in place of $w-m$):
>
> $w^{\mathsf T}\Lambda^{-1} w=\sum_i \sum_j w_i \Lambda^{-1}_{i,j} w_j$
>
> $\Lambda^{-1}_{i,j} = 0$ if $i\neq j$
>
> $w^{\mathsf T} \Lambda^{-1} w = \sum_i w_i \Lambda^{-1}_{i,i} w_i = w_1 \Lambda^{-1}_{1,1} w_1 + w_2 \Lambda^{-1}_{2,2} w_2$
>
> The exponential of a sum is a product, so the joint density factorises. In fact
> no appeal to a factorisation theorem is needed here: because $\Lambda$ is
> diagonal, $\det\Lambda=\Lambda_{1,1}\Lambda_{2,2}$ and
> $\Lambda^{-1}_{i,i}=1/\Lambda_{i,i}$, so the constant splits along with the
> exponent and the two factors are *visibly* the $N(0,\Lambda_{1,1})$ and
> $N(0,\Lambda_{2,2})$ densities:
>
> $$f(w)=\frac{1}{2\pi\sqrt{\Lambda_{1,1}\Lambda_{2,2}}}
> \exp\!\left(-\tfrac12\Big(\tfrac{w_1^2}{\Lambda_{1,1}}+\tfrac{w_2^2}{\Lambda_{2,2}}\Big)\right)
> =\left[\tfrac{1}{\sqrt{2\pi\Lambda_{1,1}}}e^{-w_1^2/(2\Lambda_{1,1})}\right]
> \left[\tfrac{1}{\sqrt{2\pi\Lambda_{2,2}}}e^{-w_2^2/(2\Lambda_{2,2})}\right].$$
>
> Since the joint density is the product of the two marginal densities, $T-\mu$
> and $D$ are independent, hence $T\perp D$.
>
> (For the record, the general statement also holds without identifying the
> factors: if $f(y_1,y_2)=g(y_1)h(y_2)$ a.e. on $\mathbb R^2$ with $g,h\ge0$, put
> $c_g=\int g$, $c_h=\int h$; then $1=\int\!\!\int f=c_gc_h$ by Tonelli, the
> marginals are $f_1=c_h g$ and $f_2=c_g h$, and so
> $f_1f_2=c_gc_h\,gh=gh=f$. No condition on the support is required — but the
> factorisation must hold on all of $\mathbb R^2$, including where $f=0$, since
> otherwise the shape of the support can itself encode dependence.)
>
> **(iv) $(T,D)$ is independent of $(S_1^2,S_2^2)$.** Within a normal sample the
> sample mean is independent of the vector of residuals, hence of $S_i^2$; and the
> two samples are independent of each other. So
> $(\overline X_1,\overline X_2)\perp(S_1^2,S_2^2)$, and $(T,D)$ is a function of
> $(\overline X_1,\overline X_2)$.
>
> This last deduction needs care. It is **not** enough that
> $\overline X_1\perp S_1^2$ and $\overline X_2\perp S_2^2$: in general $A\perp B$
> and $C\perp D$ do not give $(A,C)\perp(B,D)$. (Take $A\perp B$ and set $C=B$,
> $D=A$; then $C\perp D$, yet $(A,C)=(A,B)$ and $(B,D)=(B,A)$ determine each
> other.) Here is the argument in full. Pick any sets and consider the four events
>
> $$E_1=\{\overline X_1\in A_1\},\quad F_1=\{S_1^2\in B_1\},\quad
> E_2=\{\overline X_2\in A_2\},\quad F_2=\{S_2^2\in B_2\}.$$
>
> *Step 1 (the two samples are independent).* $E_1\cap F_1$ is determined by the
> observations of sample 1 alone, and $E_2\cap F_2$ by those of sample 2 alone.
> The samples are independent, so
>
> $$\mathbb P(E_1\cap F_1\cap E_2\cap F_2)=\mathbb P(E_1\cap F_1)\,\mathbb P(E_2\cap F_2).$$
>
> *Step 2 (within each sample).* Since $\overline X_i\perp S_i^2$,
> $\mathbb P(E_i\cap F_i)=\mathbb P(E_i)\mathbb P(F_i)$ for $i=1,2$. Substituting,
>
> $$\mathbb P(E_1\cap F_1\cap E_2\cap F_2)
> =\mathbb P(E_1)\,\mathbb P(F_1)\,\mathbb P(E_2)\,\mathbb P(F_2).$$
>
> *Step 3 (regroup).* Note that $\overline X_1\perp\overline X_2$ and
> $S_1^2\perp S_2^2$, since the samples are independent. Grouping the two means
> together and the two variances together,
>
> $$=\big[\mathbb P(E_1)\mathbb P(E_2)\big]\big[\mathbb P(F_1)\mathbb P(F_2)\big]
> =\mathbb P(E_1\cap E_2)\,\mathbb P(F_1\cap F_2).$$
>
> (Rebracketing four numbers is of course free; it is those two independences that
> turn the regrouped brackets back into joint probabilities.) This says exactly
> that $(\overline X_1,\overline X_2)\perp(S_1^2,S_2^2)$.
>
> The point is Step 3: the within-sample independences alone give only the two
> brackets $\mathbb P(E_i\cap F_i)=\mathbb P(E_i)\mathbb P(F_i)$, which pair each
> mean with *its own* variance. It is the cross-sample independence that breaks
> the product all the way down into four separate factors, after which regrouping
> means-with-means is legitimate.
>
> **(v) $T$ is independent of the triple $(D,S_1^2,S_2^2)$.** This is the same
> factor-then-regroup argument as in (iv). Write $S=(S_1^2,S_2^2)$ and take any
> sets $A$, $B$, $C$ for $T$, $D$, $S$ respectively. Then
>
> $$\mathbb P(T\in A,\ D\in B,\ S\in C)
> =\mathbb P\big((T,D)\in A\times B\big)\ \mathbb P(S\in C)$$
>
> by (iv), and applying $T\perp D$ from (iii) to the first factor,
>
> $$=\mathbb P(T\in A)\ \mathbb P(D\in B)\ \mathbb P(S\in C).$$
>
> The probability is now a product of three separate factors, so regroup the last
> two:
>
> $$=\mathbb P(T\in A)\ \mathbb P(D\in B,\ S\in C),$$
>
> using $D\perp S$ — which is free, being (iv) restricted to the first
> coordinate. The result is exactly $T\perp(D,S_1^2,S_2^2)$ on product sets, and
> hence in general.
>
> **Conclusion.** Writing $\overline X_1+Dw-\mu=(T-\mu)+(w-\theta)D$ and expanding,
>
> $$\mathbb E\big[(\overline X_1+Dw-\mu)^2\big]
> =\mathbb E\big[(T-\mu)^2\big]+2\,\mathbb E\big[(T-\mu)(w-\theta)D\big]+\mathbb E\big[D^2(w-\theta)^2\big].$$
>
> Since $w$ is a function of $(D,S_1^2,S_2^2)$, so is $(w-\theta)D$; by (v) and
> (i) the cross term factorises as
> $\mathbb E(T-\mu)\cdot\mathbb E[(w-\theta)D]=0$. This is $(*)$. $\square$
>
> Only $\mathbb E(T-\mu)=0$ and independence were used, so no assumption on $w$
> beyond integrability of the displayed terms is needed — which is what the
> phrase "of finite risk" in $(*)$ requires, and what (4) and (16) below verify
> for the $w$ at hand.

Let

$$
h=p(r)\left(1-\frac q4\right),
\qquad
\varepsilon=\frac1{500}.
$$

Then the weight of $\widehat\mu_*$ is $r+\varepsilon h$, because

$$
\varepsilon h=\frac1{2000}p(r)(4-q).
$$

Consequently,

$$
R(\widehat\mu_*)-R(\widehat\mu_{\mathrm{GD}})
=2\varepsilon B+\varepsilon^2C,
$$

where

$$
B=\mathbb E\!\left[D^2(r-\theta)h\right],
\qquad
C=\mathbb E\!\left[D^2h^2\right].
\tag{1}
$$

> **[Annotation] Derivation of $(1)$.** Apply $(*)$ to each of the two
> estimators. The Graybill–Deal estimator has weight $w=r$ and $\widehat\mu_*$
> has weight $w=r+\varepsilon h$, so
>
> $$R(\widehat\mu_{\mathrm{GD}})=\mathbb E\big[(T-\mu)^2\big]+\mathbb E\big[D^2(r-\theta)^2\big],$$
> $$R(\widehat\mu_*)=\mathbb E\big[(T-\mu)^2\big]+\mathbb E\big[D^2(r+\varepsilon h-\theta)^2\big].$$
>
> The term $\mathbb E[(T-\mu)^2]$ is the same in both — it does not involve the
> weight — so it cancels in the difference:
>
> $$R(\widehat\mu_*)-R(\widehat\mu_{\mathrm{GD}})
> =\mathbb E\Big[D^2\big\{(r-\theta+\varepsilon h)^2-(r-\theta)^2\big\}\Big].$$
>
> Expanding the square with $a=r-\theta$ and $b=\varepsilon h$, so that
> $(a+b)^2-a^2=2ab+b^2$,
>
> $$(r-\theta+\varepsilon h)^2-(r-\theta)^2
> =2\varepsilon(r-\theta)h+\varepsilon^2h^2 .$$
>
> Multiplying by $D^2$, taking expectations, and pulling the constants
> $\varepsilon$ and $\varepsilon^2$ outside gives
>
> $$R(\widehat\mu_*)-R(\widehat\mu_{\mathrm{GD}})
> =2\varepsilon\,\mathbb E\big[D^2(r-\theta)h\big]+\varepsilon^2\,\mathbb E\big[D^2h^2\big]
> =2\varepsilon B+\varepsilon^2 C .$$
>
> Note this is an exact identity, not an approximation: no expansion in small
> $\varepsilon$ has been made, and the only property of $h$ used is that
> $r+\varepsilon h$ is again a function of $(D,S_1^2,S_2^2)$, so that $(*)$
> applies to it.

We will prove the uniform bounds

$$
B<-\frac6{8075}\lambda(1-s^2)^2,
\qquad
C<\frac12\lambda(1-s^2)^2,
\tag{2}
$$

where $s=2\theta-1\in(-1,1)$.

### Canonical variables

Put $\nu=16$ and $U_i=\nu S_i^2/\sigma_i^2$. By the usual normal-sample theory,
$U_1,U_2$ are independent $\chi^2_{16}$ variables and are independent of $D$.

> **[Annotation]** The sample size is $n=17$, so $\nu=n-1=16$ is already the
> degrees of freedom — it is not the sample size, and nothing is subtracted from
> it again. Thus
> $U_i=(n-1)S_i^2/\sigma_i^2=\sum_{j}(X_{ij}-\overline X_i)^2/\sigma_i^2$
> has the $\chi^2_{n-1}=\chi^2_{16}$ distribution. (Some references state this as
> $nS_i^2/\sigma_i^2\sim\chi^2_{n-1}$, which uses the *biased* sample variance
> with divisor $n$; either way the quantity is
> $\sum_j(X_{ij}-\overline X_i)^2/\sigma_i^2$ and the degrees of freedom are
> $n-1=16$. As a check, $\mathbb E U_i=16$, matching the mean of $\chi^2_{16}$,
> since $\mathbb E S_i^2=\sigma_i^2$ by unbiasedness.)

The beta–gamma factorisation gives

$$
P=\frac{U_1}{U_1+U_2}\sim\operatorname{Beta}(8,8),
\qquad
L=U_1+U_2\sim\chi^2_{32},
$$

with $P$ and $L$ independent. Moreover $V=D^2/\lambda\sim\chi^2_1$ is
independent of $(P,L)$.

> **[Annotation] The beta–gamma factorisation.** All three conclusions — the law
> of $P$, the law of $L$, and their independence — drop out of a single change of
> variables.
>
> *A chi-square is a gamma.* In the shape–rate parametrisation the gamma density
> with shape $\alpha>0$ and rate $\beta>0$ is
>
> $$f_{\operatorname{Gamma}}(x;\alpha,\beta)=\frac{\beta^{\alpha}}{\Gamma(\alpha)}\,x^{\alpha-1}e^{-\beta x},
> \qquad x>0,$$
>
> while the $\chi^2_k$ density is
>
> $$f_{\chi^2}(x;k)=\frac{1}{2^{k/2}\Gamma(k/2)}\,x^{k/2-1}e^{-x/2},
> \qquad x>0.$$
>
> Putting $\alpha=k/2$ and $\beta=1/2$ in the first gives
>
> $$f_{\operatorname{Gamma}}\!\left(x;\tfrac k2,\tfrac12\right)
> =\frac{(1/2)^{k/2}}{\Gamma(k/2)}x^{k/2-1}e^{-x/2}
> =\frac{1}{2^{k/2}\Gamma(k/2)}x^{k/2-1}e^{-x/2}
> =f_{\chi^2}(x;k),$$
>
> so $\chi^2_k=\operatorname{Gamma}(k/2,\ \text{rate }1/2)$ — the two are the same
> family, and the rate is $1/2$ for *every* $k$. That last point is what makes the
> factorisation below work.
>
> Hence $U_1,U_2$ are independent $\operatorname{Gamma}(8,1/2)$ variables, so by
> independence their joint density on $(0,\infty)^2$ is the product of the
> marginals,
>
> $$f_{U_1,U_2}(u_1,u_2)=\frac{(1/2)^{8}}{\Gamma(8)}u_1^{7}e^{-u_1/2}\cdot
> \frac{(1/2)^{8}}{\Gamma(8)}u_2^{7}e^{-u_2/2}.$$
>
> *Change of variables.* Put $p=u_1/(u_1+u_2)$ and $\ell=u_1+u_2$, a bijection
> from $(0,\infty)^2$ onto $(0,1)\times(0,\infty)$ with inverse
> $u_1=p\ell$, $u_2=(1-p)\ell$. The density of $(P,L)$ is then
>
> $$g_{P,L}(p,\ell)=f_{U_1,U_2}\big(p\ell,\ (1-p)\ell\big)\,|J|,$$
>
> where $|J|$ is the absolute Jacobian determinant of the inverse map
> $(p,\ell)\mapsto(u_1,u_2)$:
>
> $$J=\det\begin{pmatrix}
> \partial u_1/\partial p & \partial u_1/\partial \ell\\
> \partial u_2/\partial p & \partial u_2/\partial \ell
> \end{pmatrix}
> =\det\begin{pmatrix}\ell & p\\ -\ell & 1-p\end{pmatrix}
> =\ell(1-p)+p\ell=\ell,
> \qquad |J|=\ell$$
>
> since $\ell>0$. Substituting, the exponentials combine as
> $e^{-p\ell/2}e^{-(1-p)\ell/2}=e^{-\ell/2}$ — the $p$-dependence cancels — and
> $(p\ell)^{7}\big((1-p)\ell\big)^{7}=p^{7}(1-p)^{7}\ell^{14}$, so
>
> $$g_{P,L}(p,\ell)
> =\frac{(1/2)^{16}}{\Gamma(8)^2}\,p^{7}(1-p)^{7}\,\ell^{14}e^{-\ell/2}\cdot\ell
> =\underbrace{\frac{p^{7}(1-p)^{7}}{B(8,8)}}_{g_P(p),\ \operatorname{Beta}(8,8)}
> \cdot\underbrace{\frac{(1/2)^{16}}{\Gamma(16)}\ell^{15}e^{-\ell/2}}_{g_L(\ell),\ \operatorname{Gamma}(16,1/2)},$$
>
> having multiplied and divided by $\Gamma(16)$ and used
> $1/B(8,8)=\Gamma(16)/\Gamma(8)^2$. Since
> $g_{P,L}(p,\ell)=g_P(p)\,g_L(\ell)$ with each factor a probability density in
> its own variable, the same reasoning as in (iii-c) gives
> $P\sim\operatorname{Beta}(8,8)$,
> $L\sim\operatorname{Gamma}(16,1/2)=\chi^2_{32}$, and $P\perp L$.
>
> Two things worth noting. First, the cancellation
> $e^{-p\ell/2}e^{-(1-p)\ell/2}=e^{-\ell/2}$ is the whole mechanism, and it
> requires the two gamma variables to share the **same rate**. This is precisely
> why $U_i$ is defined as $\nu S_i^2/\sigma_i^2$ rather than $\nu S_i^2$: dividing
> by $\sigma_i^2$ puts both on rate $1/2$. With unequal rates the exponent would
> retain a $p\ell$ term and $P$ and $L$ would not be independent.
> Second, $L\sim\chi^2_{32}$ is the expected total: $32=16+16$ degrees of
> freedom.

Write

$$
x=2P-1,\qquad
\Delta=\theta P+(1-\theta)(1-P)=\frac{1+sx}{2}.
$$

> **[Annotation]** Both $x=2P-1$ and $s=2\theta-1$ invert to
>
> $$P=\frac{1+x}{2},\quad 1-P=\frac{1-x}{2},\qquad
> \theta=\frac{1+s}{2},\quad 1-\theta=\frac{1-s}{2},$$
>
> so substituting into $\Delta$ and expanding,
>
> $$\Delta=\frac{1+s}{2}\cdot\frac{1+x}{2}+\frac{1-s}{2}\cdot\frac{1-x}{2}
> =\frac{(1+s)(1+x)+(1-s)(1-x)}{4}
> =\frac{(1+s+x+sx)+(1-s-x+sx)}{4}
> =\frac{2+2sx}{4}
> =\frac{1+sx}{2},$$
>
> the terms $\pm s$ and $\pm x$ cancelling in pairs and the two $sx$ terms adding.
>
> Note for later that $1+sx$ never vanishes. Since $\sigma_1^2,\sigma_2^2>0$ by
> hypothesis, $\theta=\sigma_1^2/(\sigma_1^2+\sigma_2^2)$ lies **strictly**
> between $0$ and $1$, so $s=2\theta-1$ satisfies $|s|<1$. Hence for every
> $x\in[-1,1]$,
>
> $$|sx|=|s|\,|x|\le|s|<1,
> \qquad\text{so}\qquad
> 1+sx\ \ge\ 1-|s|\ >\ 0 ,$$
>
> and therefore $\Delta=(1+sx)/2>0$ as well. Only the strictness of $|s|<1$ is
> used: $x$ may range over the closed interval $[-1,1]$, so nothing needs to be
> said about whether $P$ can equal $0$ or $1$. (For $1+sx=0$ one would need
> $sx=-1$, i.e. $|s|=|x|=1$ with opposite signs, and $|s|=1$ is already excluded.)
>
> This matters because $(1+sx)$ appears in denominators throughout the rest of the
> proof — up to the fifth and eighth powers — and $\Delta^{-1},\Delta^{-2}$ appear
> in the brackets for $B$ and $C$; the bound above keeps all of them finite on the
> range of integration. Note also that the bound $1-|s|$ degenerates as
> $|s|\to1$, i.e. as $\theta\to0$ or $1$. That is exactly why the factors
> $(1-s^2)^2$ appear in (2), and why the $C$-side must later be controlled at
> $s=1$ through $I_4(1)$ and $I_6(1)$ rather than merely for each $s<1$.

Direct substitution gives

$$
r=\frac{\theta P}{\Delta},
\qquad
q=\frac{16V}{L\Delta}.
\tag{3}
$$

> **[Annotation] Derivation of (3).** Three substitutions are used throughout:
> $S_i^2=\sigma_i^2U_i/\nu=\sigma_i^2U_i/16$ (from $U_i=\nu S_i^2/\sigma_i^2$);
> $U_1=PL$ and $U_2=(1-P)L$ (from $P=U_1/L$, $L=U_1+U_2$); and
> $\sigma_1^2=\theta(\sigma_1^2+\sigma_2^2)$,
> $\sigma_2^2=(1-\theta)(\sigma_1^2+\sigma_2^2)$ (from the definition of $\theta$).
>
> *For $r$.* Substituting the first,
>
> $$r=\frac{S_1^2}{S_1^2+S_2^2}
> =\frac{\sigma_1^2U_1/16}{(\sigma_1^2U_1+\sigma_2^2U_2)/16}
> =\frac{\sigma_1^2U_1}{\sigma_1^2U_1+\sigma_2^2U_2},$$
>
> so the divisor $16$ cancels. Substituting the third, the common factor
> $\sigma_1^2+\sigma_2^2$ cancels as well:
>
> $$r=\frac{\theta U_1}{\theta U_1+(1-\theta)U_2}.$$
>
> Finally $U_1=PL$, $U_2=(1-P)L$, and the common factor $L$ cancels:
>
> $$r=\frac{\theta PL}{\theta PL+(1-\theta)(1-P)L}
> =\frac{\theta P}{\theta P+(1-\theta)(1-P)}=\frac{\theta P}{\Delta}.$$
>
> So $r$ depends on $P$ alone — not on $L$, and not on the overall variance
> scale. This is what makes $r$ a function of $P$ only, used repeatedly later.
>
> *For $q$.* The denominator, by the same two substitutions, is
>
> $$S_1^2+S_2^2=\frac{\sigma_1^2U_1+\sigma_2^2U_2}{16}
> =\frac{(\sigma_1^2+\sigma_2^2)\big[\theta P+(1-\theta)(1-P)\big]L}{16}
> =\frac{(\sigma_1^2+\sigma_2^2)L\Delta}{16}.$$
>
> The numerator is $17D^2=17\lambda V=(\sigma_1^2+\sigma_2^2)V$, since
> $\lambda=(\sigma_1^2+\sigma_2^2)/17$. Dividing,
>
> $$q=\frac{17D^2}{S_1^2+S_2^2}
> =\frac{(\sigma_1^2+\sigma_2^2)V}{(\sigma_1^2+\sigma_2^2)L\Delta/16}
> =\frac{16V}{L\Delta}.$$
>
> Note the constant in the answer is $16=\nu$, not $17=n$: the $17$ from the
> definition of $q$ cancels against the $17$ in $\lambda$, while the $16$ is the
> divisor in $S_i^2=\sigma_i^2U_i/16$. Note too that both $r$ and $q$ are free of
> $\sigma_1^2,\sigma_2^2$ except through $\theta$ — the scale
> $\sigma_1^2+\sigma_2^2$ cancels in each, as it must, since $r$ and $q$ are
> statistics.

The density of $x$ is $(1-x^2)^7/Z$ on $(-1,1)$, where
$Z=\int_{-1}^1(1-x^2)^7dx$.

> **[Annotation] Derivation of the density of $x$.** From
> $P\sim\operatorname{Beta}(8,8)$,
>
> $$g_P(p)=\frac{p^{7}(1-p)^{7}}{B(8,8)},\qquad 0<p<1 .$$
>
> The map $x=2p-1$ is a bijection from $(0,1)$ onto $(-1,1)$ with inverse
> $p=(1+x)/2$ and $\left|\dfrac{dp}{dx}\right|=\dfrac12$, so the
> one-dimensional change of variables gives
>
> $$g_X(x)=g_P\!\left(\frac{1+x}{2}\right)\left|\frac{dp}{dx}\right|
> =\frac{1}{B(8,8)}\left(\frac{1+x}{2}\right)^{7}\left(\frac{1-x}{2}\right)^{7}\cdot\frac12 ,$$
>
> using $1-p=1-\frac{1+x}{2}=\frac{1-x}{2}$. Collecting the powers of two and
> using $(1+x)(1-x)=1-x^2$,
>
> $$g_X(x)=\frac{(1-x^2)^{7}}{2^{15}\,B(8,8)},\qquad -1<x<1 .$$
>
> So the density is a constant multiple of $(1-x^2)^{7}$, and since a density
> integrates to $1$ that constant must be $1/Z$ with
> $Z=\int_{-1}^{1}(1-x^2)^{7}dx$ — which is how the document writes it. One never
> needs the value of $Z$ itself: it always cancels, because every expectation
> below is of the form $\frac1Z\int_{-1}^1(1-x^2)^7(\cdots)\,dx$ and the bounds
> compare such integrals with each other.
>
> Equivalently, $Z=2^{15}B(8,8)$, which can be seen directly by substituting
> $x=2p-1$ in $Z$: then $1-x^2=4p(1-p)$ and $dx=2\,dp$, so
> $Z=4^{7}\cdot2\int_0^1p^{7}(1-p)^{7}dp=2^{15}B(8,8)$. Numerically this is
> $4096/6435$, the value asserted in the original's verification script.

We shall use

$$
\mathbb EV=1,\quad
\mathbb EV^2=3,\quad
\mathbb EV^3=15,\quad
\mathbb EL^{-1}=\frac1{30},\quad
\mathbb EL^{-2}=\frac1{840}.
\tag{4}
$$

> **[Annotation] Derivation of the moments in (4).** These formulas can also be
> found by asking Wolfram|Alpha for
> [“moments of chi square distribution”](https://www.wolframalpha.com/input?i=moments+of+chi+square+distribution)
> and
> [“moments of inverse chi square distribution”](https://www.wolframalpha.com/input?i=moments+of+inverse+chi+square+distribution).
>
> For a chi-square variable $X\sim\chi^2_d$, Wolfram|Alpha lists the first three
> moments as
>
> $$\mathbb EX=d,\qquad
> \mathbb EX^2=d(d+2),\qquad
> \mathbb EX^3=d(d+2)(d+4).$$
>
> Since $V\sim\chi^2_1$, substituting $d=1$ gives
>
> $$\mathbb EV=1,\qquad
> \mathbb EV^2=1\cdot3=3,\qquad
> \mathbb EV^3=1\cdot3\cdot5=15.$$
>
> For $L\sim\chi^2_{32}$, its reciprocal $W=1/L$ has the
> [inverse-chi-squared distribution](https://en.wikipedia.org/wiki/Inverse-chi-squared_distribution)
> with $32$ degrees of freedom. For an inverse-chi-square variable with $d$
> degrees of freedom, Wolfram|Alpha lists the first two moments as
>
> $$\mathbb EW=\frac{1}{2(d/2-1)}
> \quad\text{for }1<\frac d2,\qquad
> \mathbb EW^2=\frac{1}{4(d/2-2)(d/2-1)}
> \quad\text{for }2<\frac d2.$$
>
> Here $d/2=16$, and $2<16$, so both listed formulas apply. Substitution gives
>
> $$\mathbb EL^{-1}=\mathbb EW=\frac{1}{2(16-1)}=\frac1{30},\qquad
> \mathbb EL^{-2}=\mathbb EW^2
> =\frac{1}{4(16-2)(16-1)}=\frac1{840}.$$

### The first-order term

Using (3)–(4) to integrate out $V$ and $L$ gives

$$
\frac B\lambda
=
\mathbb E_x\!\left[
(r-\theta)p(r)
\left(1-\frac{2}{5\Delta}\right)
\right].
$$

> **[Annotation] Derivation of the first expectation.** Recall the definitions
>
> $$B=\mathbb E\!\left[D^2(r-\theta)h\right],\qquad
> V=\frac{D^2}{\lambda},\qquad
> h=p(r)\left(1-\frac q4\right).$$
>
> Equation (3) supplies the remaining substitution:
>
> $$q=\frac{16V}{L\Delta}=\frac{\nu V}{L\Delta},$$
>
> since $\nu=16$. Therefore, dividing the definition of $B$ by $\lambda$ and
> substituting first $D^2/\lambda=V$ and $h=p(r)(1-q/4)$, then the expression
> for $q$, gives
>
> $$\begin{aligned}
> \frac B\lambda
> &=\frac1\lambda\,
>   \mathbb E\!\left[D^2(r-\theta)h\right]\\
> &=\mathbb E\!\left[
>   \frac{D^2}{\lambda}(r-\theta)
>   p(r)\left(1-\frac q4\right)\right]\\
> &=\mathbb E\!\left[
>   V(r-\theta)p(r)
>   \left(1-\frac14\frac{\nu V}{L\Delta}\right)\right]\\
> &=\mathbb E\!\left[
>   V(r-\theta)p(r)
>   \left(1-\frac{\nu V}{4L\Delta}\right)\right].
> \end{aligned}$$
>
> The two independence assertions used next were established earlier, for
> different reasons. Step (iv) in the derivation of $(*)$ proved
>
> $$(\overline X_1,\overline X_2)\perp(S_1^2,S_2^2).$$
>
> Now $D=\overline X_2-\overline X_1$, and hence $V=D^2/\lambda$, is a function
> of the sample means. On the other hand,
> $U_i=\nu S_i^2/\sigma_i^2$ is a function of the sample variances, and
>
> $$P=\frac{U_1}{U_1+U_2},\qquad L=U_1+U_2$$
>
> are functions of $(U_1,U_2)$. Applying functions to two independent random
> vectors preserves their independence, so $V\perp(P,L)$. Separately, the
> beta–gamma factorisation above proved $P\perp L$ by factoring their joint
> density as $g_{P,L}(p,\ell)=g_P(p)g_L(\ell)$. Together these facts make
> $V,P,L$ mutually independent.
>
> Finally, $\Delta=\theta P+(1-\theta)(1-P)$ and
> $r=\theta P/\Delta$ are functions of $P$ alone. Thus, conditional on $P$, the
> quantities $\Delta$, $r$, and $p(r)$ are fixed while $V$ and $L$ are integrated
> out. In particular,
>
> $$\mathbb E\!\left[\left.
> V-\frac{\nu V^2}{4L\Delta}\,\right|\,P\right]
> =\mathbb EV-\frac{\nu}{4}\,\mathbb EV^2\,\mathbb EL^{-1}\frac1\Delta
> =1-\frac{16\cdot3}{4\cdot30}\cdot\frac1\Delta
> =1-\frac{2}{5\Delta}.$$
>
> To connect this conditional expectation back to $B/\lambda$, set
> $G(P)=(r-\theta)p(r)$. The expression derived above for $B/\lambda$ can first
> be rewritten by multiplying the leading $V$ into the parentheses:
>
> $$\frac B\lambda
> =\mathbb E\!\left[
> G(P)\left(V-\frac{\nu V^2}{4L\Delta}\right)\right].$$
>
> The law of iterated expectation says to average this first conditional on $P$
> and then average the result over $P$:
>
> $$\begin{aligned}
> \frac B\lambda
> &=\mathbb E_P\!\left[
> \mathbb E\!\left[\left.
> G(P)\left(V-\frac{\nu V^2}{4L\Delta}\right)
> \,\right|\,P\right]\right]\\
> &=\mathbb E_P\!\left[
> G(P)\,
> \mathbb E\!\left[\left.
> V-\frac{\nu V^2}{4L\Delta}
> \,\right|\,P\right]\right].
> \end{aligned}$$
>
> The second line pulls $G(P)$ outside the inner expectation because, once $P$
> is fixed, $G(P)$ is just a constant. Substituting the conditional expectation
> just calculated therefore gives
>
> $$\frac B\lambda
> =\mathbb E_P\!\left[
> (r-\theta)p(r)\left(1-\frac{2}{5\Delta}\right)\right].$$
>
> Finally, $x=2P-1$ is a one-to-one reparametrisation of $P$. Thus averaging a
> function of $P$ with respect to $P$ is the same as averaging the corresponding
> function of $x$ with respect to the density of $x$ derived above. The proof
> denotes this latter expectation by $\mathbb E_x$, so the preceding display is
> exactly
>
> $$\frac B\lambda
> =\mathbb E_x\!\left[
> (r-\theta)p(r)\left(1-\frac{2}{5\Delta}\right)\right],$$
>
> as asserted.

The elementary identities

$$
r-\theta=\frac{(1-s^2)x}{2(1+sx)},
\qquad
p(r)
=-\frac{(1-s^2)(1-x^2)(x+s)}
        {4(1+sx)^3}
$$

> **[Annotation] Derivation of the two identities.** Using
> $P=(1+x)/2$, $\theta=(1+s)/2$, and $\Delta=(1+sx)/2$ in
> $r=\theta P/\Delta$ gives
>
> $$r=\frac{(1+s)(1+x)}{2(1+sx)}.$$
>
> Therefore
>
> $$\begin{aligned}
> r-\theta
> &=\frac{1+s}{2}
>   \left(\frac{1+x}{1+sx}-1\right)\\
> &=\frac{1+s}{2}\,
>   \frac{x-sx}{1+sx}
> =\frac{(1-s^2)x}{2(1+sx)}.
> \end{aligned}$$
>
> For $p(r)=r(1-r)(1-2r)$, the other two factors simplify to
>
> $$1-r=\frac{(1-s)(1-x)}{2(1+sx)},\qquad
> 1-2r=-\frac{x+s}{1+sx}.$$
>
> Multiplying these expressions by the formula for $r$,
>
> $$\begin{aligned}
> p(r)
> &=\frac{(1+s)(1+x)}{2(1+sx)}
>   \frac{(1-s)(1-x)}{2(1+sx)}
>   \left(-\frac{x+s}{1+sx}\right)\\
> &=-\frac{(1-s^2)(1-x^2)(x+s)}
>          {4(1+sx)^3},
> \end{aligned}$$
>
> using $(1+s)(1-s)=1-s^2$ and $(1+x)(1-x)=1-x^2$.

These identities therefore yield

$$
B=-\frac{\lambda(1-s^2)^2}{40Z}K(s),
\tag{5}
$$

where

$$
K(s)=
\int_{-1}^1
(1-x^2)^8
\frac{x(x+s)(1+5sx)}{(1+sx)^5}\,dx.
\tag{6}
$$

> **[Annotation] Derivation of (5)–(6).** The preceding result was
>
> $$\frac B\lambda
> =\mathbb E_x\!\left[
> (r-\theta)p(r)\left(1-\frac2{5\Delta}\right)\right].$$
>
> Since $x$ has density $(1-x^2)^7/Z$ on $(-1,1)$, writing out this expectation
> as an integral gives
>
> $$\frac B\lambda
> =\frac1Z\int_{-1}^1(1-x^2)^7
> (r-\theta)p(r)\left(1-\frac2{5\Delta}\right)\,dx.$$
>
> The two identities just derived supply the first two factors. For the third,
> use $\Delta=(1+sx)/2$:
>
> $$1-\frac2{5\Delta}
> =1-\frac4{5(1+sx)}
> =\frac{5(1+sx)-4}{5(1+sx)}
> =\frac{1+5sx}{5(1+sx)}.$$
>
> Thus the product inside the expectation is
>
> $$\begin{aligned}
> &(r-\theta)p(r)\left(1-\frac2{5\Delta}\right)\\
> &\quad=
> \frac{(1-s^2)x}{2(1+sx)}
> \left[-\frac{(1-s^2)(1-x^2)(x+s)}
> {4(1+sx)^3}\right]
> \frac{1+5sx}{5(1+sx)}\\
> &\quad=
> -\frac{(1-s^2)^2}{40}\,
> \frac{x(1-x^2)(x+s)(1+5sx)}{(1+sx)^5}.
> \end{aligned}$$
>
> Here the minus sign comes from $p(r)$, the constant is
> $2\cdot4\cdot5=40$, and the denominator has power
> $(1+sx)^{1+3+1}=(1+sx)^5$. Substituting this product into the integral and
> combining its factor $(1-x^2)$ with the density factor $(1-x^2)^7$ gives
>
> $$\begin{aligned}
> \frac B\lambda
> &=-\frac{(1-s^2)^2}{40Z}
> \int_{-1}^1(1-x^2)^8
> \frac{x(x+s)(1+5sx)}{(1+sx)^5}\,dx\\
> &=-\frac{(1-s^2)^2}{40Z}K(s),
> \end{aligned}$$
>
> where the last equality is exactly the definition (6) of $K(s)$. Multiplying
> both sides by $\lambda$ gives (5).
>
> The integer $5$ here is why $n=17$ is chosen. In general the bracket is
> $1-2\nu\,\mathbb EV^2\,\mathbb EL^{-1}/(4\Delta)$, and writing $m=2\nu$ the
> ratio of the two constants in the numerator is $4(m-2)/(m-8)$, which is the
> integer $5$ exactly when $m=32$, i.e. $n=17$. For $n=13$ it is $11/2$ and the
> kernel is correspondingly less pleasant.

It remains only to bound $K(s)$. Define

$$
f_s(x)=\frac{x(x+s)(1+5sx)}{(1+sx)^5},
\qquad
z=s^2x^2.
$$

The following identity is a direct differentiation:

$$
\begin{aligned}
&(1-x^2)^8
\left[
\frac{f_s(x)+f_s(-x)}2
-\frac{x^2(1-14z+125z^2)}{(1-z)^4}
\right] \\
&\qquad =
\frac{d}{dx}
\left[
\frac{8s^4x^5(1-x^2)^9}{(1-s^2x^2)^4}
\right].
\tag{7}
\end{aligned}
$$

> **[Annotation] Checking the differentiation identity with Wolfram|Alpha.**
> Ask Wolfram|Alpha to
> [“differentiate \(8s^4x^5(1-x^2)^9/(1-s^2x^2)^4\) with respect to \(x\)”](https://www.wolframalpha.com/input?i=differentiate%208%20s%5E4%20x%5E5%20%281-x%5E2%29%5E9%2F%281-s%5E2%20x%5E2%29%5E4%20with%20respect%20to%20x).
> Its result is
>
> $$\frac d{dx}\left[
> \frac{8s^4x^5(1-x^2)^9}{(1-s^2x^2)^4}\right]
> =
> -\frac{8s^4x^4(1-x^2)^8
> \big[15s^2x^4+(3s^2-23)x^2+5\big]}
> {(s^2x^2-1)^5}.$$
>
> Now use $z=s^2x^2$. Since
> $(s^2x^2-1)^5=-(1-z)^5$, the minus signs cancel; also
> $s^4x^4=z^2$ and
>
> $$15s^2x^4+(3s^2-23)x^2+5
> =5+3z-23x^2+15x^2z.$$
>
> Thus the Wolfram|Alpha result is
>
> $$(1-x^2)^8
> \frac{8z^2\big(5+3z-23x^2+15x^2z\big)}
> {(1-z)^5}.$$
>
> It remains to simplify the square brackets on the left of (7). Put $a=sx$, so
> $z=a^2$. The definition of $f_s$ gives
>
> $$f_s(x)=\frac{(x^2+a)(1+5a)}{(1+a)^5},\qquad
> f_s(-x)=\frac{(x^2-a)(1-5a)}{(1-a)^5}.$$
>
> Their common denominator is
> $(1-a^2)^5=(1-z)^5$. For the numerator, set
>
> $$A=(1+5a)(1-a)^5,\qquad B=(1-5a)(1+a)^5.$$
>
> Expanding these two polynomials gives
>
> $$\begin{aligned}
> A&=1-15a^2+40a^3-45a^4+24a^5-5a^6,\\
> B&=1-15a^2-40a^3-45a^4-24a^5-5a^6.
> \end{aligned}$$
>
> Hence, grouping their even and odd parts and using $z=a^2$,
>
> $$\frac{A+B}{2}=1-15z-45z^2-5z^3,\qquad
> \frac{A-B}{2}=40a^3+24a^5.$$
>
> Consequently,
>
> $$\begin{aligned}
> \frac{f_s(x)+f_s(-x)}2
> &=\frac{(x^2+a)A+(x^2-a)B}{2(1-z)^5}\\
> &=\frac{x^2(A+B)/2+a(A-B)/2}{(1-z)^5}\\
> &=\frac{x^2(1-15z-45z^2-5z^3)+40z^2+24z^3}
> {(1-z)^5},
> \end{aligned}$$
>
> where $a(40a^3+24a^5)=40a^4+24a^6=40z^2+24z^3$.
> Put the other fraction over the same denominator:
>
> $$\begin{aligned}
> \frac{x^2(1-14z+125z^2)}{(1-z)^4}
> &=\frac{x^2(1-14z+125z^2)(1-z)}{(1-z)^5}\\
> &=\frac{x^2(1-15z+139z^2-125z^3)}{(1-z)^5}.
> \end{aligned}$$
>
> Subtracting the numerators now gives
>
> $$\begin{aligned}
> &x^2(1-15z-45z^2-5z^3)+40z^2+24z^3\\
> &\quad-x^2(1-15z+139z^2-125z^3)\\
> &=40z^2+24z^3-184x^2z^2+120x^2z^3\\
> &=8z^2\big(5+3z-23x^2+15x^2z\big).
> \end{aligned}$$
>
> Therefore
>
> $$\frac{f_s(x)+f_s(-x)}2
> -\frac{x^2(1-14z+125z^2)}{(1-z)^4}
> =
> \frac{8z^2\big(5+3z-23x^2+15x^2z\big)}
> {(1-z)^5}.$$
>
> Multiplication by $(1-x^2)^8$ now gives exactly the Wolfram|Alpha derivative,
> proving (7).

The primitive on the right vanishes at $x=\pm1$. Since $(1-x^2)^8$ is even,
integrating (7) gives

$$
K(s)=
\int_{-1}^1
x^2(1-x^2)^8
\frac{1-14z+125z^2}{(1-z)^4}\,dx.
\tag{8}
$$

> **[Annotation] Derivation of (8) from (7).** Write
>
> $$w(x)=(1-x^2)^8,\qquad
> G(x)=\frac{8s^4x^5(1-x^2)^9}{(1-s^2x^2)^4}.$$
>
> Integrating both sides of (7) from $-1$ to $1$ and applying the fundamental
> theorem of calculus to its right-hand side gives
>
> $$\begin{aligned}
> &\int_{-1}^1 w(x)\frac{f_s(x)+f_s(-x)}2\,dx\\
> &\quad-\int_{-1}^1w(x)x^2
> \frac{1-14z+125z^2}{(1-z)^4}\,dx
> =G(1)-G(-1).
> \end{aligned}$$
>
> Since $|s|<1$, the denominator of $G$ does not vanish on $[-1,1]$; and at
> each endpoint the factor $(1-x^2)^9$ in its numerator is zero. Hence
> $G(1)=G(-1)=0$.
>
> It remains to identify the first integral. By (6),
>
> $$K(s)=\int_{-1}^1w(x)f_s(x)\,dx.$$
>
> Because $w$ is even, the substitution $u=-x$ also gives
>
> $$\int_{-1}^1w(x)f_s(-x)\,dx
> =\int_{-1}^1w(u)f_s(u)\,du
> =K(s).$$
>
> Therefore the average of these two integrals is again $K(s)$:
>
> $$\int_{-1}^1w(x)\frac{f_s(x)+f_s(-x)}2\,dx
> =\frac{K(s)+K(s)}2=K(s).$$
>
> Substituting this and $G(1)-G(-1)=0$ into the integrated form of (7), then
> moving the second integral to the right, yields exactly (8).

Here $0\le z<1$, and

$$
1-14z+125z^2
=
125\left(z-\frac7{125}\right)^2+\frac{76}{125}
>
\frac35.
$$

Also $(1-z)^4\le1$, so

$$
K(s)>
\frac35
\int_{-1}^1x^2(1-x^2)^8\,dx.
\tag{9}
$$

A beta-integral calculation gives

$$
\frac{\displaystyle\int_{-1}^1x^2(1-x^2)^8\,dx}
     {\displaystyle\int_{-1}^1(1-x^2)^7\,dx}
=\frac{16}{323}.
\tag{10}
$$

> **[Annotation] Checking the beta-integral ratio.** The quickest check is to ask
> Wolfram|Alpha to evaluate the
> [entire ratio of definite integrals](https://www.wolframalpha.com/input?i=%28integral%20from%20-1%20to%201%20of%20x%5E2%20%281-x%5E2%29%5E8%20dx%29%2F%28integral%20from%20-1%20to%201%20of%20%281-x%5E2%29%5E7%20dx%29);
> it returns $16/323$ directly.
>
> For a short hand derivation, both integrands are even. On $[0,1]$, substitute
> $t=x^2$, so $dx=dt/(2\sqrt t)$. Then
>
> $$\int_{-1}^1x^2(1-x^2)^8\,dx
> =B\!\left(\frac32,9\right),\qquad
> \int_{-1}^1(1-x^2)^7\,dx
> =B\!\left(\frac12,8\right).$$
>
> Using $B(a,b)=\Gamma(a)\Gamma(b)/\Gamma(a+b)$, their ratio is
>
> $$\begin{aligned}
> \frac{B(3/2,9)}{B(1/2,8)}
> &=
> \frac{\Gamma(3/2)}{\Gamma(1/2)}
> \frac{\Gamma(9)}{\Gamma(8)}
> \frac{\Gamma(17/2)}{\Gamma(21/2)}\\
> &=\frac12\cdot8\cdot
> \frac{1}{(17/2)(19/2)}
> =\frac12\cdot8\cdot\frac4{323}
> =\frac{16}{323}.
> \end{aligned}$$

Combining (5), (9), and (10),

$$
B<
-\frac{\lambda(1-s^2)^2}{40}
\cdot\frac35\cdot\frac{16}{323}
=-\frac6{8075}\lambda(1-s^2)^2.
\tag{11}
$$

> **[Annotation] Derivation of (11).** Let
>
> $$I=\int_{-1}^1x^2(1-x^2)^8\,dx.$$
>
> Equation (5) says
>
> $$B=-\frac{\lambda(1-s^2)^2}{40Z}K(s),$$
>
> while (9) says $K(s)>\frac35 I$. The coefficient
> $-\lambda(1-s^2)^2/(40Z)$ is strictly negative: $\lambda>0$, $Z>0$, and
> $|s|<1$. Multiplying the bound for $K(s)$ by this negative coefficient
> therefore reverses the inequality:
>
> $$B<
> -\frac{\lambda(1-s^2)^2}{40Z}\cdot\frac35 I
> =-\frac{\lambda(1-s^2)^2}{40}\cdot\frac35\cdot\frac IZ.$$
>
> By the definition of $Z$ and equation (10),
>
> $$Z=\int_{-1}^1(1-x^2)^7\,dx,\qquad
> \frac IZ=\frac{16}{323}.$$
>
> Substitution gives the first expression in (11). Finally,
>
> $$\frac1{40}\cdot\frac35\cdot\frac{16}{323}
> =\frac{3\cdot16}{40\cdot5\cdot323}
> =\frac6{25\cdot323}
> =\frac6{8075},$$
>
> which gives the last expression in (11).

> **[Annotation]** Identity (7) is the most algebraically tedious step — it is a
> rational-function identity of degree about $20$ in $x$ — and it is the
> load-bearing claim. The calculation above checks it against Wolfram|Alpha's
> exact derivative, and the original verification script checks it independently
> (see the log below), along with the vanishing of the primitive at $x=\pm1$ and
> the agreement of (6) with (8) at several values of $s$.
>
> Note that $K(s)$ is genuinely transcendental: at $s=1/2$ both (6) and (8)
> equal $1314599337728/715-1673566272\log 3$. The content of (7) is that this
> log-carrying quantity has a *manifestly positive* integral representation.
>
> Two consistency notes. First, at $s=0$ both (6) and (8) reduce to
> $\int x^2(1-x^2)^8dx$, so (8) is exact at the symmetric point. Second, (9)
> uses $(1-z)^4\le1$ in the direction that *decreases* the denominator's
> reciprocal, i.e. it discards a genuinely large factor when $z$ is near $1$;
> this is lossy but harmless, since the resulting margin still suffices.

### The quadratic term

Expanding the square in $C$ and again using (3)–(4) gives

$$
\frac C\lambda
=
\mathbb E_x\!\left[
p(r)^2
\left(
1-\frac4{5\Delta}+\frac2{7\Delta^2}
\right)
\right].
\tag{12}
$$

> **[Annotation] Derivation of (12).** Recall
>
> $$C=\mathbb E[D^2h^2],\qquad
> V=\frac{D^2}{\lambda},\qquad
> h=p(r)\left(1-\frac q4\right),\qquad
> q=\frac{\nu V}{L\Delta}.$$
>
> Dividing the definition of $C$ by $\lambda$ and making these substitutions
> gives
>
> $$\begin{aligned}
> \frac C\lambda
> &=\mathbb E\!\left[\frac{D^2}{\lambda}h^2\right]\\
> &=\mathbb E\!\left[
> Vp(r)^2\left(1-\frac q4\right)^2\right]\\
> &=\mathbb E\!\left[
> Vp(r)^2
> \left(1-\frac{\nu V}{4L\Delta}\right)^2\right].
> \end{aligned}$$
>
> Expanding $(1-a)^2=1-2a+a^2$ with
> $a=\nu V/(4L\Delta)$, and then multiplying by the leading $V$, yields
>
> $$\frac C\lambda
> =\mathbb E\!\left[
> p(r)^2\left(
> V-\frac{\nu V^2}{2L\Delta}
> +\frac{\nu^2V^3}{16L^2\Delta^2}
> \right)\right].$$
>
> As in the first-order calculation, $V,P,L$ are mutually independent, while
> $p(r)$ and $\Delta$ are functions of $P$ alone. Conditional on $P$, the inner
> expectation over $V$ and $L$ is therefore
>
> $$\begin{aligned}
> &\mathbb E\!\left[\left.
> V-\frac{\nu V^2}{2L\Delta}
> +\frac{\nu^2V^3}{16L^2\Delta^2}
> \,\right|\,P\right]\\
> &\quad=
> \mathbb EV
> -\frac{\nu}{2\Delta}\mathbb EV^2\,\mathbb EL^{-1}
> +\frac{\nu^2}{16\Delta^2}\mathbb EV^3\,\mathbb EL^{-2}\\
> &\quad=
> 1-\frac{16}{2\Delta}\cdot3\cdot\frac1{30}
> +\frac{16^2}{16\Delta^2}\cdot15\cdot\frac1{840}\\
> &\quad=
> 1-\frac4{5\Delta}+\frac2{7\Delta^2}.
> \end{aligned}$$
>
> The two nonconstant coefficients simplify because
>
> $$\frac{16}{2}\cdot3\cdot\frac1{30}=\frac45,\qquad
> \frac{16^2}{16}\cdot15\cdot\frac1{840}=\frac27.$$
>
> Applying the law of iterated expectation, pulling the $P$-measurable factor
> $p(r)^2$ outside the conditional expectation, gives
>
> $$\frac C\lambda
> =\mathbb E_P\!\left[
> p(r)^2\left(1-\frac4{5\Delta}+\frac2{7\Delta^2}\right)\right].$$
>
> Finally, $x=2P-1$ reparametrises the remaining expectation, so
> $\mathbb E_P$ may be written as $\mathbb E_x$. This is exactly (12).

The middle term in parentheses is negative and may be discarded. Furthermore,

$$
p(r)^2
=
\frac{(1-s^2)^2(1-x^2)^2(x+s)^2}
     {16(1+sx)^6}.
$$

> **[Annotation]** This follows by squaring the identity derived in the
> first-order section:
>
> $$p(r)=-\frac{(1-s^2)(1-x^2)(x+s)}
> {4(1+sx)^3}.$$
>
> Hence
>
> $$\begin{aligned}
> p(r)^2
> &=\left[-\frac{(1-s^2)(1-x^2)(x+s)}
> {4(1+sx)^3}\right]^2\\
> &=\frac{(1-s^2)^2(1-x^2)^2(x+s)^2}
> {4^2(1+sx)^{2\cdot3}}\\
> &=\frac{(1-s^2)^2(1-x^2)^2(x+s)^2}
> {16(1+sx)^6}.
> \end{aligned}$$
>
> The minus sign disappears on squaring, $4^2=16$, and
> $\big((1+sx)^3\big)^2=(1+sx)^6$.

The other identity used below is

$$
(1+sx)^2-(x+s)^2=(1-s^2)(1-x^2)\ge0.
\tag{13}
$$

> **[Annotation] Derivation of (13).** Expanding both squares, the two $2sx$
> terms cancel:
>
> $$\begin{aligned}
> (1+sx)^2-(x+s)^2
> &=(1+2sx+s^2x^2)-(x^2+2sx+s^2)\\
> &=1-s^2-x^2+s^2x^2\\
> &=(1-s^2)-x^2(1-s^2)\\
> &=(1-s^2)(1-x^2).
> \end{aligned}$$
>
> Since $|s|<1$ and $|x|\le1$, both factors are nonnegative (and
> $1-s^2$ is strictly positive), proving the final inequality in (13).

For $k=4,6$, set $I_k(s)=\int_{-1}^1(1-x^2)^9(1+sx)^{-k}dx$. Equations
(12)–(13) imply

$$
C\le
\frac{\lambda(1-s^2)^2}{Z}
\left(
\frac1{16}I_4(s)+\frac1{14}I_6(s)
\right).
\tag{14}
$$

> **[Annotation] Derivation of (14).** Recall that
>
> $$C=\mathbb E[D^2h^2],$$
>
> and equation (12) rewrites this quantity as
>
> $$\frac C\lambda
> =\mathbb E_x\!\left[
> p(r)^2\left(
> 1-\frac4{5\Delta}+\frac2{7\Delta^2}
> \right)\right].$$
>
> Since $p(r)^2\ge0$ and $\Delta>0$, the contribution involving
> $-4/(5\Delta)$ is nonpositive. Discarding it can only increase the right-hand
> side, so
>
> $$\frac C\lambda
> \le\mathbb E_x\!\left[
> p(r)^2\left(1+\frac2{7\Delta^2}\right)\right].$$
>
> Now $\Delta=(1+sx)/2$, and hence
>
> $$\frac2{7\Delta^2}=\frac{8}{7(1+sx)^2}.$$
>
> Substitute this, the formula
>
> $$p(r)^2=
> \frac{(1-s^2)^2(1-x^2)^2(x+s)^2}
> {16(1+sx)^6},$$
>
> and the density $(1-x^2)^7/Z$ of $x$. Combining
> $(1-x^2)^7(1-x^2)^2=(1-x^2)^9$ gives
>
> $$\begin{aligned}
> \frac C\lambda
> &\le\frac{(1-s^2)^2}{Z}
> \int_{-1}^1(1-x^2)^9
> \frac{(x+s)^2}{16(1+sx)^6}
> \left(1+\frac{8}{7(1+sx)^2}\right)\,dx\\
> &=\frac{(1-s^2)^2}{Z}\left[
> \frac1{16}\int_{-1}^1(1-x^2)^9
> \frac{(x+s)^2}{(1+sx)^6}\,dx
> +\frac1{14}\int_{-1}^1(1-x^2)^9
> \frac{(x+s)^2}{(1+sx)^8}\,dx
> \right],
> \end{aligned}$$
>
> where $(1/16)(8/7)=1/14$. Equation (13) says
>
> $$(x+s)^2\le(1+sx)^2.$$
>
> Because $1+sx>0$, this bounds the two rational factors by
>
> $$\frac{(x+s)^2}{(1+sx)^6}\le\frac1{(1+sx)^4},
> \qquad
> \frac{(x+s)^2}{(1+sx)^8}\le\frac1{(1+sx)^6}.$$
>
> Therefore, using the definitions of $I_4(s)$ and $I_6(s)$,
>
> $$\frac C\lambda
> \le\frac{(1-s^2)^2}{Z}
> \left(\frac1{16}I_4(s)+\frac1{14}I_6(s)\right).$$
>
> Multiplying both sides by $\lambda>0$ gives exactly (14).

The functions $I_k$ are even.

> **[Annotation] Why $I_k$ is even.** Here “even” refers to $I_k$ as a function
> of $s$. From its definition,
>
> $$I_k(-s)=\int_{-1}^1(1-x^2)^9(1-sx)^{-k}\,dx.$$
>
> Substitute $u=-x$, so $dx=-du$ and the endpoints exchange. Since
> $1-(-u)^2=1-u^2$,
>
> $$\begin{aligned}
> I_k(-s)
> &=\int_{1}^{-1}(1-u^2)^9(1+su)^{-k}(-du)\\
> &=\int_{-1}^{1}(1-u^2)^9(1+su)^{-k}\,du\\
> &=I_k(s).
> \end{aligned}$$
>
> Thus $I_k(-s)=I_k(s)$ for every $|s|<1$.

For $0\le s<1$, pairing $x$ with $-x$ shows that $I_k(s)$ is increasing in
$s$, because the derivative of the paired integrand is

$$
kx(1-x^2)^9
\left[
(1-sx)^{-k-1}-(1+sx)^{-k-1}
\right]\ge0
$$

for $0\le x\le1$. Hence $I_k(s)\le I_k(1)$.

> **[Annotation] What “pairing $x$ with $-x$” means.** Split the defining
> integral at zero:
>
> $$\begin{aligned}
> I_k(s)
> &=\int_{-1}^1(1-x^2)^9(1+sx)^{-k}\,dx\\
> &=\int_{-1}^0(1-x^2)^9(1+sx)^{-k}\,dx
> +\int_0^1(1-x^2)^9(1+sx)^{-k}\,dx.
> \end{aligned}$$
>
> In the first integral, put $u=-x$. Then $x=-u$, $dx=-du$, and the endpoints
> change as
>
> $$x=-1\longmapsto u=1,\qquad x=0\longmapsto u=0.$$
>
> Therefore
>
> $$\begin{aligned}
> \int_{-1}^0(1-x^2)^9(1+sx)^{-k}\,dx
> &=\int_1^0\big(1-(-u)^2\big)^9
>       \big(1+s(-u)\big)^{-k}(-du)\\
> &=\int_0^1(1-u^2)^9(1-su)^{-k}\,du.
> \end{aligned}$$
>
> Renaming the dummy variable $u$ back to $x$ and substituting this expression
> into the split integral gives
>
> $$\begin{aligned}
> I_k(s)
> &=\int_0^1(1-x^2)^9(1-sx)^{-k}\,dx
> +\int_0^1(1-x^2)^9(1+sx)^{-k}\,dx\\
> &=\int_0^1(1-x^2)^9
> \left[(1+sx)^{-k}+(1-sx)^{-k}\right]\,dx.
> \end{aligned}$$
>
> The two terms in square brackets are the contributions from the original
> points $x$ and $-x$; placing them together is the “pairing.” For fixed
> $x\in[0,1]$, differentiate this paired integrand with respect to $s$:
>
> $$\begin{aligned}
> &\frac{\partial}{\partial s}
> \left\{(1-x^2)^9
> \left[(1+sx)^{-k}+(1-sx)^{-k}\right]\right\}\\
> &\quad=kx(1-x^2)^9
> \left[(1-sx)^{-k-1}-(1+sx)^{-k-1}\right].
> \end{aligned}$$
>
> Here the chain rule gives a minus sign when differentiating $1-sx$, which
> cancels the minus sign from differentiating the negative power. When
> $0\le s<1$ and $0\le x\le1$,
>
> $$0<1-sx\le1+sx.$$
>
> Because $k+1>0$, taking the power $-(k+1)$ reverses this comparison:
>
> $$(1-sx)^{-k-1}\ge(1+sx)^{-k-1}.$$
>
> Every other factor in the derivative is nonnegative, so the paired integrand
> is nondecreasing in $s$ for every $x\in[0,1]$. To spell out the passage from
> the integrand to the integral, define
>
> $$H_s(x)=(1-x^2)^9
> \left[(1+sx)^{-k}+(1-sx)^{-k}\right].$$
>
> If $0\le s_1\le s_2<1$, the preceding derivative calculation says
>
> $$H_{s_1}(x)\le H_{s_2}(x)\qquad\text{for every }x\in[0,1].$$
>
> Integration preserves a pointwise inequality, so
>
> $$I_k(s_1)=\int_0^1H_{s_1}(x)\,dx
> \le\int_0^1H_{s_2}(x)\,dx=I_k(s_2).$$
>
> This is exactly the statement that $I_k$ is nondecreasing on $[0,1)$.
>
> **Endpoint comparison.** It remains to justify
> $I_k(s)\le I_k(1)$. The apparent singularity at $s=1$ is removable, and
> monotone convergence then closes the argument.
>
> First, $I_k(1)$ is finite. For $k=4,6$, and for $-1<x<1$,
>
> $$\frac{(1-x^2)^9}{(1+x)^k}
> =(1-x)^9(1+x)^{9-k}.$$
>
> Here $9-k$ is $5$ or $3$, so the expression on the right extends continuously
> to $x=-1$ with value $0$. Thus the singularity in the uncancelled expression
> for $I_k(1)$ is removable, and
>
> $$I_k(1)=\int_{-1}^1(1-x)^9(1+x)^{9-k}\,dx<\infty.$$
>
> Recall the paired integrand
>
> $$H_t(x)=(1-x^2)^9
> \left[(1+tx)^{-k}+(1-tx)^{-k}\right],
> \qquad 0\le x\le1.$$
>
> Fix $0\le s<1$ and, for $n=1,2,\ldots$, set
>
> $$t_n=1-\frac{1-s}{n}.$$
>
> Then $t_1=s$ and $t_n\uparrow1$. The monotonicity already proved shows that,
> for each fixed $0\le x<1$,
>
> $$H_{t_n}(x)\uparrow H_1(x),$$
>
> where cancellation of the removable endpoint factors gives
>
> $$H_1(x)
> =(1-x)^9(1+x)^{9-k}
> +(1+x)^9(1-x)^{9-k}.$$
>
> Because $9-k>0$, this expression extends continuously to $x=1$ with value
> $0$. Also $H_{t_n}(1)=0$ for every finite $n$, since $t_n<1$, so the
> convergence holds at $x=1$ as well.
>
> The functions $H_{t_n}$ are nonnegative. The monotone convergence theorem
> therefore permits the limit to pass through the integral:
>
> $$\begin{aligned}
> I_k(1)
> &=\int_0^1H_1(x)\,dx\\
> &=\lim_{n\to\infty}\int_0^1H_{t_n}(x)\,dx\\
> &=\lim_{n\to\infty}I_k(t_n).
> \end{aligned}$$
>
> Since $I_k(t_n)$ is nondecreasing and $t_1=s$,
>
> $$I_k(s)=I_k(t_1)
> \le\lim_{n\to\infty}I_k(t_n)
> =I_k(1).$$
>
> Finally, evenness gives
>
> $$I_k(s)=I_k(|s|)\le I_k(1)
> \qquad\text{for every }|s|<1.$$
>
> One subtlety is worth emphasizing: monotonicity on $[0,1)$ alone would not
> determine a separately assigned value at $s=1$. The cancellation and
> monotone-convergence argument prove that the displayed $I_k(1)$ is genuinely
> the limit from below.

Two elementary beta integrals give

$$
\frac{I_4(1)}Z=\frac{12}{7},
\qquad
\frac{I_6(1)}Z=\frac92.
\tag{15}
$$

> **[Annotation] Wolfram|Alpha checks for (15).** Substituting $s=1$ into the
> definition of $I_k$ gives
>
> $$I_k(1)=\int_{-1}^1\frac{(1-x^2)^9}{(1+x)^k}\,dx,\qquad
> Z=\int_{-1}^1(1-x^2)^7\,dx.$$
>
> Wolfram|Alpha can evaluate each complete ratio directly:
>
> - [calculate \(I_4(1)/Z\)](https://www.wolframalpha.com/input?i=%28integral%20from%20-1%20to%201%20of%20%281-x%5E2%29%5E9%2F%281%2Bx%29%5E4%20dx%29%2F%28integral%20from%20-1%20to%201%20of%20%281-x%5E2%29%5E7%20dx%29), which returns $12/7$;
> - [calculate \(I_6(1)/Z\)](https://www.wolframalpha.com/input?i=%28integral%20from%20-1%20to%201%20of%20%281-x%5E2%29%5E9%2F%281%2Bx%29%5E6%20dx%29%2F%28integral%20from%20-1%20to%201%20of%20%281-x%5E2%29%5E7%20dx%29), which returns $9/2$.

It follows from (14)–(15) that

$$
C\le
\lambda(1-s^2)^2
\left(
\frac1{16}\frac{12}{7}
+\frac1{14}\frac92
\right)
=\frac37\lambda(1-s^2)^2
<
\frac12\lambda(1-s^2)^2.
\tag{16}
$$

In particular, the inverse-$\chi^2$ moments in (4) and the bound (16) show that
the proposed estimator has finite risk.

### Risk comparison

Finally, substituting (11) and (16) into (1), with $\varepsilon=1/500$, gives

$$
\begin{aligned}
R(\widehat\mu_*)-R(\widehat\mu_{\mathrm{GD}})
&<
\varepsilon\lambda(1-s^2)^2
\left(
-\frac{12}{8075}+\frac{\varepsilon}{2}
\right) \\
&=
-\frac{157}{323000}\,
\varepsilon\lambda(1-s^2)^2
<0.
\end{aligned}
$$

This holds for every $\mu\in\mathbb R$ and every $\sigma_1^2,\sigma_2^2>0$,
completing the proof. $\square$

> **[Annotation] Slack.** The bounds (11) and (16) permit any
> $\varepsilon<2b/c$ with $b=6/8075$ and $c=3/7$, i.e.
> $\varepsilon<28/8075\approx1/288$; with the coarser $c=1/2$ the limit is
> $24/8075\approx1/337$. The chosen $\varepsilon=1/500$ therefore carries a
> factor of about $1.5$–$1.7$ in hand. Since
> $\varepsilon h=p(r)(4-q)/2000$, the perturbation actually applied is the same
> one as in the $n=13$ argument of `SHORT_PROOF_N13.md`, where the corresponding
> slack is only $1.13$.

## Optional clipping

If a weight constrained to $[0,1]$ is preferred, replace the weight of
$\widehat\mu_*$ by its projection onto $[0,1]$. Since $0<\theta<1$, projection
cannot increase $(w-\theta)^2$ pointwise. The clipped estimator therefore also
strictly dominates the Graybill–Deal estimator.

---

## Appendix B. The Gaussian facts used in $(*)$

> **[Annotation]** This appendix is not in the original; it supplies the three
> standard facts invoked in step (iii).

They are proved with **characteristic functions** rather than moment generating
functions. The reason is rigour: $\varphi_X(t)=\mathbb E[e^{itX}]$ exists for
*every* random variable, since $|e^{itX}|=1$, and the uniqueness theorem — two
probability measures on $\mathbb R^k$ with the same characteristic function
coincide — holds without side conditions. A moment generating function may be
infinite off the origin, and MGF-based uniqueness requires finiteness on a
neighbourhood of $0$. For the Gaussians here that does hold, so an MGF argument
is also valid; but it needs a hypothesis the CF argument does not.

**Conventions.** Call $X$ *univariate normal* $N(\mu,\sigma^2)$, allowing the
degenerate case $\sigma^2=0$ (a point mass at $\mu$), if
$\varphi_X(t)=\exp(it\mu-\tfrac12t^2\sigma^2)$ for all $t\in\mathbb R$. Call
$W\in\mathbb R^k$ *multivariate normal* $N_k(m,\Sigma)$, with $\Sigma$ symmetric
nonnegative-definite, if

$$
\varphi_W(t)=\mathbb E\big[e^{it^{\mathsf T}W}\big]
=\exp\big(it^{\mathsf T}m-\tfrac12t^{\mathsf T}\Sigma t\big),
\qquad t\in\mathbb R^k.
\tag{B.1}
$$

Admitting degenerate cases is not cosmetic: a linear combination
$\alpha^{\mathsf T}W$ can have zero variance, and Lemma B.1 would be false if
such combinations were not counted as normal.

### Lemma B.1 (Cramér–Wold characterisation)

*$W\in\mathbb R^k$ is multivariate normal if and only if $\alpha^{\mathsf T}W$
is univariate normal for every $\alpha\in\mathbb R^k$.*

*Proof.* ($\Rightarrow$) Assume (B.1) and fix $\alpha$. For $t\in\mathbb R$,

$$
\varphi_{\alpha^{\mathsf T}W}(t)
=\mathbb E\big[e^{i(t\alpha)^{\mathsf T}W}\big]
=\varphi_W(t\alpha)
=\exp\big(it\,\alpha^{\mathsf T}m-\tfrac12t^2\,\alpha^{\mathsf T}\Sigma\alpha\big),
$$

the characteristic function of
$N(\alpha^{\mathsf T}m,\alpha^{\mathsf T}\Sigma\alpha)$, the variance being
$\ge0$ since $\Sigma$ is nonnegative-definite.

($\Leftarrow$) Assume every $\alpha^{\mathsf T}W$ is univariate normal. Taking
$\alpha=e_j$ shows each $W_j$ is normal, hence has finite mean and variance; by
Cauchy–Schwarz all covariances are finite. So $m:=\mathbb E W$ and
$\Sigma:=\operatorname{Cov}(W)$ exist, $\Sigma$ is symmetric
nonnegative-definite, and by linearity of expectation and bilinearity of
covariance — neither of which needs normality —

$$
\mathbb E[\alpha^{\mathsf T}W]=\alpha^{\mathsf T}m,
\qquad
\operatorname{Var}(\alpha^{\mathsf T}W)=\alpha^{\mathsf T}\Sigma\alpha .
$$

By hypothesis $\alpha^{\mathsf T}W$ *is* normal, and a univariate normal law is
determined by its mean and variance, so
$\alpha^{\mathsf T}W\sim N(\alpha^{\mathsf T}m,\alpha^{\mathsf T}\Sigma\alpha)$
and

$$
\mathbb E\big[e^{it(\alpha^{\mathsf T}W)}\big]
=\exp\big(it\,\alpha^{\mathsf T}m-\tfrac12t^2\,\alpha^{\mathsf T}\Sigma\alpha\big).
$$

Evaluate at $t=1$: the left side is exactly $\varphi_W(\alpha)$, so

$$
\varphi_W(\alpha)=\exp\big(i\alpha^{\mathsf T}m-\tfrac12\alpha^{\mathsf T}\Sigma\alpha\big)
\qquad\text{for every }\alpha\in\mathbb R^k,
$$

which is (B.1). Uniqueness of characteristic functions finishes. $\square$

The step worth noting is the last one: a one-parameter family of univariate
characteristic functions, evaluated at the single point $t=1$ but allowed to
range over all directions $\alpha$, recovers the whole $k$-dimensional
characteristic function. This is the Cramér–Wold device.

### Lemma B.2 (affine images)

*If $W\sim N_k(m,\Sigma)$, $A$ is $\ell\times k$ and $b\in\mathbb R^\ell$, then
$AW+b\sim N_\ell(Am+b,\ A\Sigma A^{\mathsf T})$.*

*Proof.* For $t\in\mathbb R^\ell$,

$$
\varphi_{AW+b}(t)=e^{it^{\mathsf T}b}\varphi_W(A^{\mathsf T}t)
=\exp\big(it^{\mathsf T}(Am+b)-\tfrac12t^{\mathsf T}(A\Sigma A^{\mathsf T})t\big),
$$

using $(A^{\mathsf T}t)^{\mathsf T}m=t^{\mathsf T}Am$ and
$(A^{\mathsf T}t)^{\mathsf T}\Sigma(A^{\mathsf T}t)=t^{\mathsf T}A\Sigma A^{\mathsf T}t$.
Also $A\Sigma A^{\mathsf T}$ is nonnegative-definite, since
$t^{\mathsf T}A\Sigma A^{\mathsf T}t=(A^{\mathsf T}t)^{\mathsf T}\Sigma(A^{\mathsf T}t)\ge0$.
Uniqueness gives the claim. $\square$

This is what (iii-b) uses, with $A=M$ and $b=(-\mu,0)^{\mathsf T}$; it delivers
(A.2) directly as $M\Sigma M^{\mathsf T}$.

### Lemma B.3 (sums of independent normals)

*If $X\sim N(\mu_1,\sigma_1^2)$ and $Y\sim N(\mu_2,\sigma_2^2)$ are independent
and $a,b\in\mathbb R$, then
$aX+bY\sim N(a\mu_1+b\mu_2,\ a^2\sigma_1^2+b^2\sigma_2^2)$.*

*Proof.* Independence makes the characteristic function of a sum the product of
the characteristic functions, so

$$
\varphi_{aX+bY}(t)=\varphi_X(at)\varphi_Y(bt)
=\exp\Big(it(a\mu_1+b\mu_2)-\tfrac12t^2\big(a^2\sigma_1^2+b^2\sigma_2^2\big)\Big).
\ \square
$$

The proof shows exactly where independence enters: it is what turns the
characteristic function of the sum into a product, so that the two Gaussian
exponents add. Without it the product formula fails and the sum need not be
normal — which is why joint normality of $(\overline X_1,\overline X_2)$ is a
consequence of the samples being independent, not of the marginals being normal.

---

