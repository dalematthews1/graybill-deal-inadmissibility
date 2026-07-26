# A short proof that the Graybill–Deal estimator is inadmissible

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

Set $r=q=0$ on
$\{S_1^2+S_2^2=0\}$, which is a null event.

## Theorem

For every $\mu\in\mathbb R$ and every
$\sigma_1^2,\sigma_2^2>0$,

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
$$

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

We will prove the uniform bounds

$$
B<-\frac6{8075}\lambda(1-s^2)^2,
\qquad
C<\frac12\lambda(1-s^2)^2,
\tag{2}
$$

where $s=2\theta-1\in(-1,1)$.

### Canonical variables

Put $\nu=16$ and

$$
U_i=\frac{\nu S_i^2}{\sigma_i^2}.
$$

By the usual normal-sample theory,
$U_1,U_2$ are independent $\chi^2_{16}$ variables and are independent of
$D$. The beta–gamma factorisation gives

$$
P=\frac{U_1}{U_1+U_2}\sim\operatorname{Beta}(8,8),
\qquad
L=U_1+U_2\sim\chi^2_{32},
$$

with $P$ and $L$ independent. Moreover,

$$
V=\frac{D^2}{\lambda}\sim\chi^2_1
$$

is independent of $(P,L)$.

Write

$$
x=2P-1,\qquad
\Delta=\theta P+(1-\theta)(1-P)=\frac{1+sx}{2}.
$$

Direct substitution gives

$$
r=\frac{\theta P}{\Delta},
\qquad
q=\frac{16V}{L\Delta}.
\tag{3}
$$

The density of $x$ is $(1-x^2)^7/Z$ on $(-1,1)$, where

$$
Z=\int_{-1}^1(1-x^2)^7\,dx.
$$

We shall use

$$
\mathbb EV=1,\quad
\mathbb EV^2=3,\quad
\mathbb EV^3=15,\quad
\mathbb EL^{-1}=\frac1{30},\quad
\mathbb EL^{-2}=\frac1{840}.
\tag{4}
$$

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

The elementary identities

$$
r-\theta=\frac{(1-s^2)x}{2(1+sx)},
$$

$$
p(r)
=-\frac{(1-s^2)(1-x^2)(x+s)}
        {4(1+sx)^3}
$$

therefore yield

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

The primitive on the right vanishes at $x=\pm1$.
Since $(1-x^2)^8$ is even, integrating (7) gives

$$
K(s)=
\int_{-1}^1
x^2(1-x^2)^8
\frac{1-14z+125z^2}{(1-z)^4}\,dx.
\tag{8}
$$

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

Combining (5), (9), and (10),

$$
B<
-\frac{\lambda(1-s^2)^2}{40}
\cdot\frac35\cdot\frac{16}{323}
=-\frac6{8075}\lambda(1-s^2)^2.
\tag{11}
$$

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

The middle term in parentheses is negative and may be discarded. Furthermore,

$$
p(r)^2
=
\frac{(1-s^2)^2(1-x^2)^2(x+s)^2}
     {16(1+sx)^6},
$$

and

$$
(1+sx)^2-(x+s)^2=(1-s^2)(1-x^2)\ge0.
\tag{13}
$$

For $k=4,6$, set

$$
I_k(s)=
\int_{-1}^1\frac{(1-x^2)^9}{(1+sx)^k}\,dx.
$$

Equations (12)–(13) imply

$$
C\le
\frac{\lambda(1-s^2)^2}{Z}
\left(
\frac1{16}I_4(s)+\frac1{14}I_6(s)
\right).
\tag{14}
$$

The functions $I_k$ are even. For $0\le s<1$, pairing $x$ with $-x$ shows
that $I_k(s)$ is increasing in $s$, because the derivative of the paired
integrand is

$$
kx(1-x^2)^9
\left[
(1-sx)^{-k-1}-(1+sx)^{-k-1}
\right]\ge0
$$

for $0\le x\le1$. Hence $I_k(s)\le I_k(1)$. Two elementary beta integrals give

$$
\frac{I_4(1)}Z=\frac{12}{7},
\qquad
\frac{I_6(1)}Z=\frac92.
\tag{15}
$$

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

In particular, the inverse-$\chi^2$ moments in (4) and the bound (16) show
that the proposed estimator has finite risk.

### Risk comparison

Finally, substituting (11) and (16) into (1), with
$\varepsilon=1/500$, gives

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

This holds for every $\mu\in\mathbb R$ and every
$\sigma_1^2,\sigma_2^2>0$, completing the proof. $\square$

## Optional clipping

If a weight constrained to $[0,1]$ is preferred, replace the weight of
$\widehat\mu_*$ by its projection onto $[0,1]$. Since
$0<\theta<1$, projection cannot increase $(w-\theta)^2$ pointwise. The clipped
estimator therefore also strictly dominates the Graybill–Deal estimator.
