# An elementary local proof of Graybill--Deal inadmissibility

## Theorem

Let two independent normal samples have a common unknown mean $\mu$,
positive unknown variances $\sigma_1^2,\sigma_2^2$, and sample sizes
$n_1,n_2\ge 2$.  Under ordinary squared-error loss, the Graybill--Deal
estimator is inadmissible.

The proof uses only normal regression, chi-square densities, elementary
differentiation, uniform continuity on a compact set, and integration by
parts.  In particular, it uses no complete-class or limiting-Bayes theorem.

Throughout,
$$
 S_i^2=\frac1{n_i-1}\sum_{j=1}^{n_i}(X_{ij}-\bar X_i)^2
$$
is the usual unbiased sample variance.

## 1. Exact reduction

Put
$$
 a=\frac{n_1-1}{2},\qquad b=\frac{n_2-1}{2},\qquad
 h=a+b,\qquad p=h+\frac32,
$$
and
$$
 v_i=\frac{\sigma_i^2}{n_i},\qquad
 \tau=v_1+v_2,\qquad
 \theta=\frac{v_1}{\tau}\in(0,1).
$$
Let
$$
 D=\bar X_2-\bar X_1,\qquad
 Y_i=\frac{S_i^2}{n_i},\qquad
 r=\frac{Y_1}{Y_1+Y_2},\qquad
 q=\frac{D^2}{Y_1+Y_2}.
$$
The usual inverse-estimated-variance estimator is
$$
 \frac{(n_1/S_1^2)\bar X_1+(n_2/S_2^2)\bar X_2}
      {n_1/S_1^2+n_2/S_2^2},
$$
so the Graybill--Deal estimator is
$$
 \delta_{\rm GD}=\bar X_1+rD.
$$

For any measurable real-valued $\phi(r,q)$, write
$$
 \delta_\phi=\bar X_1+D\phi(r,q).
$$
The normal variable
$$
 E=\bar X_1+\theta D-\mu
$$
is independent of $(D,Y_1,Y_2)$, has mean zero, and has variance
$\tau\theta(1-\theta)$.  Consequently,
$$
 R_{\mu,\tau,\theta}(\delta_\phi)
 =\tau\theta(1-\theta)
 +\tau E_\theta\!\left[
       D_0^2\{\phi(r,q)-\theta\}^2
    \right],
 \qquad D_0=\frac D{\sqrt\tau}.                                      \tag{1}
$$

Define the probability law
$$
 Q_\theta(A)=E_\theta\!\left[D_0^2
        1_{\{(r,q)\in A\}}\right].
$$
It has total mass one because $E_\theta[D_0^2]=1$.
A direct gamma change of variables gives
$$
 dQ_\theta(r,q)
 =C_{a,b}\,
   \theta^{\,b+3/2}(1-\theta)^{a+3/2}
   B_\theta(r,q)^{-p}w(r,q)\,dr\,dq,                                \tag{2}
$$
on $(0,1)\times(0,\infty)$, where $C_{a,b}>0$ is independent of
$\theta,r,q$, and
$$
 \begin{split}
 B_\theta(r,q)
   &=2ar(1-\theta)+2b(1-r)\theta+q\theta(1-\theta),\\
 w(r,q)&=r^{a-1}(1-r)^{b-1}q^{1/2}.                                 \tag{3}
 \end{split}
$$
The short verification of (2) is given in Section 5 below.

## 2. The two differential certificates

Define the first-variation kernel
$$
 K_\theta(r,q)=(r-\theta)B_\theta(r,q)^{-p}.                         \tag{4}
$$
At each pivot used below, $B_\theta$ is bounded away from zero uniformly
in $0\le\theta\le1$.  Thus $K_\theta$ extends smoothly to a two-sided
neighborhood of $q=0$, so the displayed boundary derivatives are
ordinary derivatives rather than a distributional convention.

### Unequal sample sizes

Suppose $a\ne b$, and put
$$
 r_0=\frac bh,\qquad c=\frac{2ab}{h},\qquad \Delta=a-b.
$$
The zero-order term in the following display means scalar multiplication.
Define
$$
 L_u=\operatorname{sgn}(\Delta)\left[
 -\frac{p(p-1)h^2}{ab}
 +\frac{(p+1)h\Delta}{ab}\,\partial_r
 +\partial_r^2
 -\frac{2(p+1)h^3}{ab}\,\partial_q
 \right].                                                          \tag{5}
$$
Then, for every $0\le\theta\le1$,
$$
 \boxed{\quad
 (L_uK_\theta)(r_0,0)
 =-c^{-p}\frac{(p-1)h|\Delta|}{ab}<0.
 \quad}                                                            \tag{6}
$$

### Equal sample sizes

Suppose $a=b$, and put
$$
 d=p^2+p+1.
$$
Define
$$
 L_e=\partial_r+
       \frac{4a(p+2)}d\,\partial_r\partial_q
       -\frac1{4d}\,\partial_r^3.                                  \tag{7}
$$
Then, for every $0\le\theta\le1$,
$$
 \boxed{\quad
 (L_eK_\theta)(1/2,0)
 =-a^{-p}\frac{p-1}{d}<0.
 \quad}                                                            \tag{8}
$$

Equations (6) and (8) are the whole algebraic core of the proof.
Their direct polynomial verification is in Section 4.

## 3. From the certificate to a dominating estimator

Use $L=L_u$ and $r_*=r_0$ in the unequal case, and use $L=L_e$ and
$r_*=1/2$ in the equal case.  Equations (6) and (8) say that, for some
$\kappa>0$,
$$
 (LK_\theta)(r_*,0)=-\kappa
 \qquad(0\le\theta\le1).                                           \tag{9}
$$

Choose
$$
 0<\delta_0<\frac12\min(r_*,1-r_*).
$$
If $|r-r_*|\le\delta_0$, $q\ge0$, and $0\le\theta\le1$, then
$$
 \begin{split}
 B_\theta(r,q)
 &\ge \min\{2ar,\,2b(1-r)\}\\
 &\ge
 \min\{2a(r_*-\delta_0),\,2b(1-r_*-\delta_0)\}>0.
 \end{split}
$$
Thus $LK_\theta(r,q)$ is jointly continuous on the compact one-sided
tube
$$
 [0,1]\times[r_*-\delta_0,r_*+\delta_0]\times[0,\delta_0].
$$
Since its value at $(r_*,0)$ is the same negative constant
$-\kappa$ for every $\theta$, uniform continuity gives a
$0<\delta\le\delta_0$ such that
$$
 LK_\theta(r,q)\le-\frac{\kappa}{2}
 \quad\text{whenever}\quad
 |r-r_*|<\delta,\qquad 0\le q<\delta,\qquad 0\le\theta\le1.          \tag{10}
$$
Now choose an open rectangle $U$ whose closure lies inside
$$
 (r_*-\delta,r_*+\delta)\times(0,\delta).
$$
Thus $U$ is close to the boundary point but is wholly inside $q>0$.
No quantitative lower bound on $\delta$ is needed: for each fixed pair
of known sample sizes, $\delta$ and $U$ are chosen once and do not
vary with $\theta$ or any other unknown parameter.

Choose $r_c,q_c,\alpha,\beta$ so that
$$
 \{(r,q):|r-r_c|\le\alpha,\ |q-q_c|\le\beta\}\subset U.
$$
With $x_+=\max(x,0)$, define the explicit nonnegative bump
$$
 \rho(r,q)=
 \left[1-\left(\frac{r-r_c}{\alpha}\right)^2\right]_+^4
 \left[1-\left(\frac{q-q_c}{\beta}\right)^2\right]_+^4.
$$
It is nonzero, compactly supported in $U$, and $C^3$, which is all
that is needed because $L$ has order at most three.  Each factor and
its first three derivatives match zero at the endpoints of its support.
Thus its zero extension is $C^3$,
$\operatorname{supp}(L^*\rho)\subseteq\operatorname{supp}\rho\Subset U$,
and the repeated integrations by parts below are classical.

Let $L^*$ denote the formal adjoint of $L$ with respect to Lebesgue
measure, and set
$$
 H(r,q)=\frac{L^*\rho(r,q)}{w(r,q)},                                \tag{11}
$$
with $H=0$ off $U$.  Since $w$ is smooth and strictly positive on
$\overline U$, the function $H$ is bounded and compactly supported.
The choices of $U,\rho$, and $H$ depend only on the known sample sizes
$(n_1,n_2)$, not on $\mu,\sigma_1^2,\sigma_2^2$.
Explicitly, a term $c_{ij}\partial_r^i\partial_q^j$ in $L$ becomes
$(-1)^{i+j}c_{ij}\partial_r^i\partial_q^j$ in $L^*$.
Integration by parts has no boundary terms and gives, uniformly in
$0\le\theta\le1$,
$$
 \begin{split}
 I_\theta
 &:=\int H(r,q)K_\theta(r,q)w(r,q)\,dr\,dq\\
 &=\int \rho(r,q)(LK_\theta)(r,q)\,dr\,dq\\
 &\le-\frac{\kappa}{2}\int\rho(r,q)\,dr\,dq
 =:-\gamma<0.                                                      \tag{12}
 \end{split}
$$

Also set
$$
 J_\theta=\int H(r,q)^2B_\theta(r,q)^{-p}
                 w(r,q)\,dr\,dq.                                  \tag{13}
$$
The set $\operatorname{supp}H\times[0,1]$ is compact and
$B_\theta>0$ there.  Moreover, (12) implies $H\not\equiv0$.  Hence
$$
 M:=\sup_{0\le\theta\le1}J_\theta
 \quad\text{satisfies}\quad 0<M<\infty.                             \tag{14}
$$

Now take
$$
 \phi_\varepsilon(r,q)=r+\varepsilon H(r,q),\qquad
 \delta_\varepsilon=\bar X_1+D\phi_\varepsilon(r,q).
$$
Using (1)--(4), for $0<\theta<1$,
$$
 \begin{split}
 &R_{\mu,\tau,\theta}(\delta_\varepsilon)
  -R_{\mu,\tau,\theta}(\delta_{\rm GD})\\
 &\quad=
 \tau C_{a,b}\theta^{b+3/2}(1-\theta)^{a+3/2}
 \{2\varepsilon I_\theta+\varepsilon^2J_\theta\}\\
 &\quad\le
 \tau C_{a,b}\theta^{b+3/2}(1-\theta)^{a+3/2}
 \{-2\varepsilon\gamma+\varepsilon^2M\}.                            \tag{15}
\end{split}
$$
Every factor outside the braces is positive.  Since the correction is
compactly supported away from $r=0,1$, put
$$
 d_0=\operatorname{dist}\!\left(
       \operatorname{proj}_r(\operatorname{supp}H),\{0,1\}\right)>0.
$$
Choose once and for all
$$
 0<\varepsilon<
 \min\!\left\{
   \frac{\gamma}{M},
   \frac{d_0}{2\lVert H\rVert_\infty}
 \right\}.                                                        \tag{16}
$$
Any such $\varepsilon$ depends only on the known sample sizes and the fixed bump,
not on $\mu,\tau,\theta$.  The first bound makes the braces in (15)
smaller than $-\varepsilon\gamma$, giving strict risk improvement
throughout the parameter space.  The second ensures
$$
 0\le r+\varepsilon H(r,q)\le1
$$
everywhere.  Hence $\delta_\varepsilon$ has finite risk and can even be
kept as a convex combination of the two sample means.  It is also
unbiased: conditional on $(Y_1,Y_2)$, the function
$\phi_\varepsilon(r,q)$ depends on $D$ only through $D^2$, so
$D\phi_\varepsilon(r,q)$ is odd in the centered normal variable $D$.
Thus $E[D\phi_\varepsilon(r,q)]=0$ and
$E[\delta_\varepsilon]=\mu$.  This proves the theorem. $\square$

## 4. Five-minute verification of the certificates

Because $B_\theta$ is affine in $r$ and $q$, if
$$
 x=r-\theta,\qquad A=\partial_rB_\theta,\qquad Q=\partial_qB_\theta
                  =\theta(1-\theta),
$$
then
$$
 \begin{split}
 K_r&=B^{-p}-pxAB^{-p-1},\\
 K_{rr}&=-2pAB^{-p-1}+p(p+1)xA^2B^{-p-2},\\
 K_q&=-pxQB^{-p-1},\\
 K_{rq}&=-pQB^{-p-1}+p(p+1)xAQB^{-p-2},\\
 K_{rrr}&=3p(p+1)A^2B^{-p-2}
          -p(p+1)(p+2)xA^3B^{-p-3}.                                \tag{17}
 \end{split}
$$

For the unequal case, evaluate at $(r_0,0)$ and retain
$x=r_0-\theta$.  Then
$$
 B=c,\qquad
 A=2(\Delta+hx),\qquad
 Q=\frac{ab}{h^2}-\frac{\Delta x}{h}-x^2.                           \tag{18}
$$
Substitution of (17)--(18) into the operator inside the square brackets
in (5) cancels the coefficients of $x,x^2,x^3$ and leaves
$$
 -c^{-p}\frac{(p-1)h\Delta}{ab}.
$$
Multiplication by $\operatorname{sgn}(\Delta)$ proves (6).

For the equal case, put $x=1/2-\theta$.  At $(1/2,0)$,
$$
 B=a,\qquad A=4ax,\qquad Q=\frac14-x^2.
$$
Equation (17) becomes
$$
 \begin{split}
 a^pK_r&=1-4px^2,\\
 a^pK_{rq}
 &=\frac{p}{4a}\{
       -1+4(p+2)x^2-16(p+1)x^4
     \},\\
 a^pK_{rrr}
 &=48p(p+1)x^2-64p(p+1)(p+2)x^4.                                  \tag{19}
 \end{split}
$$
Inserting (19) into (7) cancels the $x^2$ and $x^4$ terms.  The
constant is
$$
 1-\frac{p(p+2)}{p^2+p+1}
 =-\frac{p-1}{p^2+p+1},
$$
which proves (8).

The cancellations above do not use the statistical relation
$p=h+3/2$.  If the corresponding $p$-dependent operators are used,
both identities hold for arbitrary real $p$, with the displayed
negative signs whenever $p>1$.  The normal problem simply specializes
to $p=h+3/2\ge5/2$.

Two small-sample checks are especially transparent:
$$
 \begin{array}{ll}
 (n_1,n_2)=(2,3):&
 (27+6\partial_r-\partial_r^2+54\partial_q)
 K_\theta(2/3,0)=-81/8,\\[4pt]
 (n_1,n_2)=(2,2):&
 \left(\partial_r+\frac{12}{13}\partial_r\partial_q
 -\frac1{39}\partial_r^3\right)
 K_\theta(1/2,0)=-\dfrac{8\sqrt2}{13}.
 \end{array}                                                       \tag{20}
$$

## 5. Verification of the reduced density

Since $2a=n_1-1$ and $2b=n_2-1$,
$$
 \frac{Y_1}{v_1}\sim\frac{\chi^2_{2a}}{2a},\qquad
 \frac{Y_2}{v_2}\sim\frac{\chi^2_{2b}}{2b},\qquad
 D_0^2\sim\chi^2_1,
$$
independently.  Put
$$
 G_i=\frac{Y_i}{\tau},\qquad Z=D_0^2.
$$
Weighting by $D_0^2=Z$, as in the definition of $Q_\theta$, makes
the joint density of $(G_1,G_2,Z)$, apart from a constant independent
of $\theta$, equal to
$$
 \theta^{-a}(1-\theta)^{-b}
 G_1^{a-1}G_2^{b-1}Z^{1/2}
 \exp\!\left\{
 -\frac{aG_1}{\theta}
 -\frac{bG_2}{1-\theta}
 -\frac Z2
 \right\}.                                                        \tag{21}
$$
Use
$$
 G_1=sr,\qquad G_2=s(1-r),\qquad Z=sq.
$$
The Jacobian is $s^2$, and the power of $s$ in (21) is
$$
 s^{a-1+b-1+1/2+2}=s^{p-1}.
$$
The exponential rate is
$$
 \frac{ar}{\theta}+\frac{b(1-r)}{1-\theta}+\frac q2
 =\frac{B_\theta(r,q)}{2\theta(1-\theta)}.
$$
Integrating $s$ over $(0,\infty)$ gives
$$
 \Gamma(p)
 \left\{\frac{2\theta(1-\theta)}{B_\theta(r,q)}\right\}^{p}.
$$
Combining this with the factor
$\theta^{-a}(1-\theta)^{-b}$ yields
$$
 \theta^{p-a}(1-\theta)^{p-b}
 =\theta^{b+3/2}(1-\theta)^{a+3/2},
$$
which is exactly (2).  If desired, its normalizing constant is
$$
 C_{a,b}=
 \frac{2^p a^a b^b\Gamma(p)}
      {\sqrt{2\pi}\,\Gamma(a)\Gamma(b)}.
$$

## 6. Gap checklist

1. **All variance pairs are covered.**
   Positive $(v_1,v_2)$ are in one-to-one correspondence with
   $\tau>0$ and $0<\theta<1$; explicitly,
   $\sigma_1^2=n_1\tau\theta$ and
   $\sigma_2^2=n_2\tau(1-\theta)$.

2. **The apparent endpoint problem is harmless.**
   The endpoints $0,1$ are used only to obtain uniform bounds for the
   factored kernels $I_\theta,J_\theta$.  In the actual parameter space,
   $0<\theta<1$, and the common factor
   $\theta^{b+3/2}(1-\theta)^{a+3/2}$ in (15) is strictly positive.

3. **The boundary jet produces an interior correction.**
   Uniform continuity is first applied in a one-sided neighborhood
   $q\ge0$; the bump itself is then supported in a smaller rectangle
   whose closure lies in $q>0$.

4. **There are no integration-by-parts boundary terms.**
   The function $\rho$ has compact support strictly inside the
   observation space.

5. **Division by $w$ is safe.**
   On $\operatorname{supp}\rho$, the variables $r,1-r,q$ are bounded
   away from zero, so $w$ and $w^{-1}$ are smooth and bounded.

6. **One $\varepsilon$ works for all variance ratios.**
   The negative bound in (12) and the positive bound in (14) are uniform
   on the compact interval $0\le\theta\le1$.

7. **The estimator is legitimate.**
   The function $H$ is parameter-free, bounded, measurable, and
   compactly supported.  The resulting estimator has finite risk, and
   the second restriction in (16) keeps its random weight in $[0,1]$.
   The quantities $r,q$ may be defined arbitrarily on the null event
   $Y_1+Y_2=0$.

8. **Strict domination is obtained.**
   Equation (15) is strictly negative for every $\mu$, every
   $\tau>0$, and every $0<\theta<1$, which is stronger than the single
   strict inequality required for inadmissibility.

## 7. Relation to prior relative admissibility

For equal sample sizes, Duanmu, Roy, and Schrittesser proved that
Graybill--Deal is admissible within the restricted class
$$
 \mathcal C_1=
 \left\{
 \bar X_1+D\widehat\phi(S_1^2,S_2^2):
 \widehat\phi:(0,\infty)^2\longrightarrow[0,1]
 \right\}.
$$
See
[Duanmu--Roy--Schrittesser (2021 preprint), Corollary 5.3](https://arxiv.org/abs/2112.14257).
There is no contradiction.  The estimator constructed here is unbiased
and its weight can be kept in $[0,1]$, but its coefficient depends
genuinely on $D^2$ through
$$
 q=\frac{D^2}{Y_1+Y_2}.
$$
Indeed, $H\not\equiv0$ by (12), while $H$ has compact $q$-support,
so this dependence cannot reduce to a function of the sample variances
alone.  The rule therefore lies outside $\mathcal C_1$.  In the
equal-sample problem, this explains why incorporating the observed mean
contrast is essential for this domination mechanism.

The proof is qualitative and claims no useful numerical lower bound on
the improvement.  For this constructed rule, no positive raw-risk gap
is uniform over all variance ratios because the common factor in (15)
tends to zero as $\theta$ approaches either endpoint.  This does not
affect strict inadmissibility at every actual parameter point
$0<\theta<1$.
