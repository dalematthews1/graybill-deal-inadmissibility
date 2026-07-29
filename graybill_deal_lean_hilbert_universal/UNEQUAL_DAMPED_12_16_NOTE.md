# A damped unequal-size candidate for \((\nu_1,\nu_2)=(12,16)\)

## Status

This note records an exact analytic certificate for the **first-order**
risk term of a new, endpoint-damped perturbation for sample sizes

$$
n_1=13,\qquad n_2=17
$$

(equivalently, residual degrees of freedom
\((\nu_1,\nu_2)=(12,16)\)).

The principal result established below is

$$
B_\theta<0\qquad(0<\theta<1).
$$

Unlike the earlier undamped candidate, the new perturbation also makes
both \(B_\theta\) and \(C_\theta\) vanish quadratically at
\(\theta=0,1\). Exact positive endpoint limits of
\(-2B_\theta/C_\theta\), together with continuity and compactness, then
give one parameter-independent \(\varepsilon>0\). A stronger ratio-free
bound below proves directly that the concrete choice

$$
\varepsilon=\frac1{2000000}
$$

works for every \(0<\theta<1\).

The coefficient calculations and endpoint limits are independently
checked by
[`numerics/check_unequal_damped_12_16.py`](numerics/check_unequal_damped_12_16.py).
They have not yet been formalized in Lean. Consequently, this note should
be read as a detailed proof candidate, not yet as part of the
machine-checked result.

## 1. Canonical quantities

Let

$$
a=6,\qquad b=8,\qquad A=a+b=14,
\qquad t=\frac aA=\frac37,\qquad q=1-t=\frac47.
$$

For the variance ratio parameter \(0<\theta<1\), put

$$
\alpha=\frac{\theta}{t},\qquad
\beta=\frac{1-\theta}{q}.
$$

If \(P\sim\operatorname{Beta}(6,8)\), define

$$
D=\alpha P+\beta(1-P),
\qquad
r=\frac{\alpha P}{D}.
$$

This \(r\) is the ordinary Graybill--Deal weight. In the notation using

$$
d=16\theta P+12(1-\theta)(1-P),
$$

we have

$$
D=\frac{28d}{12\cdot16}=\frac{7d}{48},
\qquad
r=\frac{16\theta P}{d}.
$$

The constants appearing after integration over the independent
\(\chi^2\) variables are

$$
k=\frac{3(\nu_1+\nu_2)}{\nu_1+\nu_2-2}
  =\frac{42}{13},
$$

and

$$
k_1=\frac3{26},\qquad
k_2=\frac{15}{26\cdot24}=\frac5{208}.
$$

For a function \(\phi\) and a constant \(c\), the two reduced risk
coefficients are

$$
B_\theta
=
\mathbb E\!\left[
  (r-\theta)\phi(r)\left(c-\frac{k}{D}\right)
\right],
$$

and

$$
C_\theta
=
\mathbb E\!\left[
  \phi(r)^2
  \left(
    c^2-\frac{84c}{13D}+\frac{245}{13D^2}
  \right)
\right].
$$

Up to the common positive scale in the canonical risk bridge, the
unclipped perturbation has risk difference

$$
2\varepsilon B_\theta+\varepsilon^2 C_\theta.
$$

## 2. The damped perturbation

Take

$$
\phi(r)
=
r(1-r)
\left[
  (t-r)+\kappa r(1-r)
\right].
$$

The factor \(r(1-r)\) is essential. It repairs the endpoint defect of the
undamped direction: when \(\theta\) approaches either \(0\) or \(1\),
the perturbation now vanishes at the same order as the available
first-order improvement.

At the pivot \(\theta=t\), one has \(D=1\), \(r=P\), and, writing
\(X=P-t\),

$$
\mathbb E[X^2\phi(P)]
=
-\mathbb E[X^3P(1-P)]
+\kappa\mathbb E[X^2P^2(1-P)^2].
$$

Thus the unique value making this moment zero is

$$
\kappa
=
\frac{\mathbb E[X^3P(1-P)]}
     {\mathbb E[X^2P^2(1-P)^2]}.
$$

Exact beta moments give

$$
\mathbb E[X^3P(1-P)]=\frac{11}{81634},
\qquad
\mathbb E[X^2P^2(1-P)^2]=\frac{111}{158270},
$$

and hence

$$
\boxed{\kappa=\frac{1045}{5439}}.
$$

For reference, the corresponding formula at arbitrary beta shapes is

$$
\kappa_d(a,b)
=
-\frac{
  (a-b)(a+b+5)
  (5a^2b+6a^2+5ab^2+6b^2)
}{
  (a+1)(a+b)(b+1)
  (a^2b+6a^2+ab^2-8ab+6b^2)
}.
$$

We choose

$$
\boxed{
c=k+\frac1A
=\frac{42}{13}+\frac1{14}
=\frac{601}{182}
}.
$$

This value is not forced by the pivot cancellation. It is a convenient
exact choice for which both one-sided power-series certificates below
are strictly negative. Notice that

$$
c-k=\frac1{14}>0.
$$

At the pivot,

$$
\mathbb E[X\phi(P)]=-\frac{2927}{924630}<0
$$

and therefore

$$
B_t
=
(c-k)\mathbb E[X\phi(P)]
=
-\frac{2927}{12944820}<0.
$$

## 3. The side \(\theta>t\)

For \(t<\theta<1\), introduce

$$
s
=
1-\frac{\beta}{\alpha}
=
\frac{\theta-t}{q\theta}
=
\frac{7\theta-3}{4\theta}.
$$

Then \(0<s<1\), and

$$
\theta=\frac{t}{1-qs},
\qquad
\alpha=\frac1{1-qs},
\qquad
\beta=\frac{1-s}{1-qs}.
$$

Set

$$
Y=1-P\sim\operatorname{Beta}(8,6).
$$

Direct substitution gives

$$
D=\frac{1-sY}{1-qs},
\qquad
r=\frac{1-Y}{1-sY},
$$

$$
r-\theta
=
\frac{(1-s)(q-Y)}
     {(1-qs)(1-sY)},
$$

and

$$
r(1-r)
=
\frac{(1-s)Y(1-Y)}
     {(1-sY)^2}.
$$

Define

$$
F_s(Y)
=
\bigl[-q+(1-ts)Y\bigr](1-sY)
+\kappa(1-s)Y(1-Y).
$$

Then

$$
(t-r)+\kappa r(1-r)
=
\frac{F_s(Y)}{(1-sY)^2}.
$$

Writing

$$
\delta=c-k=\frac1{14},
$$

the remaining affine factor becomes

$$
c-\frac{k}{D}
=
\frac{
  \delta+s(kq-cY)
}{
  1-sY
}.
$$

Consequently,

$$
\boxed{
B_\theta
=
\frac{(1-s)^2}{1-qs}\,H_+(s)
}
$$

where

$$
H_+(s)
=
\mathbb E_{Y\sim\operatorname{Beta}(8,6)}
\left[
\frac{
  (q-Y)Y(1-Y)F_s(Y)
  [\delta+s(kq-cY)]
}{
  (1-sY)^6
}
\right].
$$

The prefactor is strictly positive. It remains to prove \(H_+(s)<0\).

Expand

$$
F_s(y)=f_0(y)+sf_1(y)+s^2f_2(y)
$$

with

$$
\begin{aligned}
f_0(y)&=-q+(1+\kappa)y-\kappa y^2,\\
f_1(y)&=(q-t-\kappa)y+(\kappa-1)y^2,\\
f_2(y)&=ty^2.
\end{aligned}
$$

If

$$
(q-y)y(1-y)F_s(y)[\delta+s(kq-cy)]
=
\sum_{j=0}^3 g_j(y)s^j,
$$

then the absolutely convergent binomial expansion

$$
\frac1{(1-sy)^6}
=
\sum_{\ell=0}^{\infty}
\binom{\ell+5}{5}s^\ell y^\ell
$$

gives

$$
H_+(s)=\sum_{n=0}^{\infty}C_n^+s^n,
$$

where

$$
C_n^+
=
\sum_{j=0}^{\min(3,n)}
\binom{n-j+5}{5}
\mathbb E[Y^{n-j}g_j(Y)].
$$

The first three coefficients are

$$
C_0^+=-\frac{2927}{12944820},
$$

$$
C_1^+=-\frac{21079}{45306870},
$$

$$
C_2^+=-\frac{6257096}{5595398445}.
$$

For \(n\ge3\), let

$$
\mu_n^+=\mathbb E[Y^n]=\frac{(8)_n}{(14)_n}>0.
$$

Exact simplification gives

$$
\frac{C_n^+}{\mu_n^+}
=
-\frac{
  (n+1)(n+2)P_+(n)
}{
  989898
  (n+14)(n+15)(n+16)(n+17)(n+18)
},
$$

where

$$
\begin{aligned}
P_+(n)
={}&894726n^5+5235585n^4-77362658n^3\\
&+302400473n^2-158799882n+115066224.
\end{aligned}
$$

Put \(m=n-3\). Then

$$
\begin{aligned}
P_+(m+3)
={}&894726m^5+18656475m^4+65989702m^3\\
&+130434161m^2+494618400m+912979872.
\end{aligned}
$$

Every coefficient is positive, so \(P_+(n)>0\) for every integer
\(n\ge3\). Therefore

$$
C_n^+<0
\qquad(n\ge0),
$$

and hence

$$
H_+(s)<0
\qquad(0\le s<1).
$$

This proves \(B_\theta<0\) for \(t\le\theta<1\).

## 4. The side \(\theta<t\)

Interchanging the two samples sends

$$
(a,b,t,\kappa,\theta,r)
\longmapsto
(b,a,q,-\kappa,1-\theta,1-r).
$$

Under this map,

$$
r-\theta\longmapsto-(r-\theta),
\qquad
\phi(r)\longmapsto-\phi(r),
$$

so \(B_\theta\) is unchanged.

For the swapped problem, use

$$
t_-=\frac47,\qquad q_-=\frac37,\qquad
\kappa_-=-\frac{1045}{5439},
$$

and

$$
s_-=\frac{3-7\theta}{3(1-\theta)}.
$$

As \(\theta\) runs from \(t\) down to \(0\), \(s_-\) runs from \(0\)
up to \(1\). The derivation of the previous section now applies with
\(Y_-\sim\operatorname{Beta}(6,8)\).

It yields

$$
B_\theta
=
\frac{(1-s_-)^2}{1-q_-s_-}\,H_-(s_-).
$$

Again,

$$
H_-(s)=\sum_{n=0}^{\infty}C_n^-s^n.
$$

The first three coefficients are

$$
C_0^-=-\frac{2927}{12944820},
$$

$$
C_1^-=-\frac{19309}{90613740},
$$

$$
C_2^-=-\frac{2290163}{3730265630}.
$$

For \(n\ge3\), with

$$
\mu_n^-=\mathbb E[Y_-^n]=\frac{(6)_n}{(14)_n}>0,
$$

one obtains

$$
\frac{C_n^-}{\mu_n^-}
=
-\frac{
  (n+1)(n+2)P_-(n)
}{
  1154881
  (n+14)(n+15)(n+16)(n+17)(n+18)
},
$$

where

$$
\begin{aligned}
P_-(n)
={}&2024512n^5+45552308n^4-182753309n^3\\
&+407426571n^2-272952966n+134243928.
\end{aligned}
$$

For \(m=n-3\),

$$
\begin{aligned}
P_-(m+3)
={}&2024512m^5+75919988m^4+546080467m^3\\
&+1769089662m^2+2976843741m+2229578190.
\end{aligned}
$$

All coefficients are positive. Thus

$$
C_n^-<0
\qquad(n\ge0),
$$

so \(H_-(s)<0\) on \(0\le s<1\). This proves

$$
\boxed{B_\theta<0\quad\text{for every }0<\theta<1.}
$$

## 5. Endpoint asymptotics

The strict inequality \(B_\theta<0\) alone is insufficient for
inadmissibility. A single \(\varepsilon\) must be chosen before
\(\theta\) (and therefore before the unknown variances) is quantified.
For the earlier undamped direction, \(B_\theta\) vanishes only linearly
at an endpoint while \(C_\theta\) approaches a positive constant, so

$$
\inf_{0<\theta<1}\frac{-2B_\theta}{C_\theta}=0.
$$

The damping factor \(r(1-r)\) changes this.

Define

$$
\widehat B_\theta
=
\frac{B_\theta}{\theta^2(1-\theta)^2},
\qquad
\widehat C_\theta
=
\frac{C_\theta}{\theta^2(1-\theta)^2}.
$$

For the right-hand parametrization,

$$
\theta=\frac{t}{1-qs},
\qquad
1-\theta=\frac{q(1-s)}{1-qs},
$$

and hence

$$
\widehat B_\theta
=
\frac{(1-qs)^3}{t^2q^2}H_+(s).
$$

At \(s=1\),

$$
F_1(y)=-q(1-y)^2.
$$

The beta endpoint integrals are finite because the shape adjacent to
\(y=1\) is \(a=6>4\). Exact evaluation gives

$$
H_+(1)=-\frac{39076}{22295},
$$

and therefore

$$
\boxed{
\lim_{\theta\uparrow1}\widehat B_\theta
=
-\frac{29307}{12740}
}.
$$

For \(C_\theta\), define

$$
R_s(y)
=
c^2
-\frac{6Ac}{A-1}\frac{1-qs}{1-sy}
+\frac{15A^2}{(A-1)(A-2)}
 \frac{(1-qs)^2}{(1-sy)^2}.
$$

Then

$$
C_\theta
=
(1-s)^2
\mathbb E\left[
\frac{
  Y^2(1-Y)^2F_s(Y)^2
}{
  (1-sY)^8
}
R_s(Y)
\right].
$$

It follows that

$$
\widehat C_\theta
=
\frac{(1-qs)^4}{t^2q^2}
\mathbb E\left[
\frac{
  Y^2(1-Y)^2F_s(Y)^2
}{
  (1-sY)^8
}
R_s(Y)
\right].
$$

The exact endpoint value is

$$
\boxed{
\lim_{\theta\uparrow1}\widehat C_\theta
=
\frac{164411937}{4057690}
}.
$$

Consequently,

$$
\boxed{
\lim_{\theta\uparrow1}
\frac{-2B_\theta}{C_\theta}
=
\frac{6222853}{54803979}
>0
}.
$$

Using the swapped calculation at the left endpoint gives

$$
\boxed{
\lim_{\theta\downarrow0}\widehat B_\theta
=
-\frac{53468}{66885}
},
$$

$$
\boxed{
\lim_{\theta\downarrow0}\widehat C_\theta
=
\frac{18021716}{2028845}
},
$$

and

$$
\boxed{
\lim_{\theta\downarrow0}
\frac{-2B_\theta}{C_\theta}
=
\frac{2432794}{13516287}
>0
}.
$$

At the pivot, exact calculation gives

$$
C_t
=
\frac{2929078580439}{492344331547432},
$$

and

$$
\frac{-2B_t}{C_t}
=
\frac{3339772646756}{43936178706585}
>0.
$$

The endpoint values are not being used as a numerical certificate; their
purpose is to prove that the ratio does not collapse to zero at either
boundary.

## 6. Compactness and one fixed \(\varepsilon\)

The formulas in the two \(s\)-coordinates show that
\(\widehat B_\theta\) and \(\widehat C_\theta\) extend continuously to
\([0,1]\). At the endpoints this uses the cancellations

$$
F_1(y)=-q(1-y)^2
$$

and its swapped counterpart. Here is a direct domination argument, so
that this continuity does not rely only on a formal substitution
\(s=1\). Put

$$
e=1-s,\qquad u=1-y,\qquad h=1-sy=e+u-eu.
$$

Since \(r=u/h\) and \(1-r=e(1-u)/h\), the numerator \(F_s\) has the exact
form

$$
F_s(y)
=
t h^2-u h+\kappa e u(1-u).
$$

Because \(h\ge e\), \(h\ge u\), and \(eu\le h^2\), there is a fixed
constant \(M\) such that

$$
|F_s(y)|\le M h^2
\qquad(0\le s,y\le1).
$$

For \(H_+\), after including the
\(\operatorname{Beta}(8,6)\) density, this bounds the potentially
singular endpoint part by a constant multiple of

$$
\frac{u^6}{(e+u-eu)^4}
\le u^2.
$$

For \(\widehat C\), the risk quadratic is bounded by a constant multiple
of \(h^{-2}\); after using \(|F_s|\le Mh^2\) and including the same beta
density, the endpoint part is bounded by

$$
\frac{u^7}{(e+u-eu)^6}
\le u.
$$

Both dominating functions are integrable. The swapped side has endpoint
shape \(8\), so the same estimates are stronger there. Dominated
convergence therefore proves the asserted continuous extensions and
justifies the endpoint integrals. Equivalently, the required inverse
beta moments are finite because the two shapes are \(6\) and \(8\), both
greater than \(4\).

The series certificates prove that the continuous extension of
\(\widehat B\) is strictly negative everywhere, including the two exact
endpoint limits. Hence compactness gives a number \(b_0>0\) such that

$$
\widehat B_\theta\le-b_0
\qquad(0\le\theta\le1).
$$

The quadratic factor in \(C_\theta\) is strictly positive. In general it
is

$$
c^2-\frac{6Ac}{A-1}u
+\frac{15A^2}{(A-1)(A-2)}u^2,
\qquad u=\frac1D>0.
$$

Its discriminant is

$$
-\frac{12c^2A^2(2A+1)}
       {(A-1)^2(A-2)}
<0.
$$

Thus \(C_\theta>0\) in the interior, and the displayed endpoint values
are also positive. Continuity and compactness give a finite \(c_1>0\)
such that

$$
0<\widehat C_\theta\le c_1
\qquad(0\le\theta\le1).
$$

Choose one number

$$
0<\varepsilon<\frac{2b_0}{c_1}.
$$

It depends only on the fixed sample sizes, not on \(\mu\), the two
variances, or \(\theta\). For every \(0<\theta<1\),

$$
\begin{aligned}
2\varepsilon B_\theta+\varepsilon^2C_\theta
&=
\theta^2(1-\theta)^2
\left(
  2\varepsilon\widehat B_\theta
  +\varepsilon^2\widehat C_\theta
\right)\\
&\le
\theta^2(1-\theta)^2
\left(
  -2\varepsilon b_0+\varepsilon^2c_1
\right)
<0.
\end{aligned}
$$

This is the needed uniform-\(\varepsilon\) argument.

## 7. A stronger explicit, ratio-free bound

The compactness argument above proves existence, but the coefficient
certificate actually gives a direct uniform bound and even an explicit
working value of \(\varepsilon\).

Let

$$
b_0=\frac{2927}{12944820}.
$$

On either side of the pivot, every coefficient after the constant term
in \(H_\pm(s)\) is strictly negative. Therefore

$$
H_\pm(s)\le C_0^\pm=-b_0
\qquad(0\le s<1).
$$

Since \(0<1-q_\pm s\le1\), the exact prefactor for \(B\) gives

$$
\boxed{
B_\theta
\le
-b_0(1-s)^2
}
$$

in the appropriate one-sided \(s\)-coordinate.

It remains to bound \(C\) by the same endpoint factor. Write

$$
g(r)=t-r+\kappa r(1-r).
$$

For the original direction,

$$
g'(r)=-1+\kappa(1-2r)<0
$$

because \(0<\kappa=1045/5439<1\). Hence \(g\) decreases from
\(3/7\) to \(-4/7\), so

$$
|g(r)|\le\frac47.
$$

For the swapped direction, \(t=4/7\) and
\(\kappa=-1045/5439\); its derivative is again strictly negative and it
decreases from \(4/7\) to \(-3/7\). Thus the same bound holds on both
sides.

In either one-sided coordinate, put

$$
u=\frac1D=\frac{1-qs}{1-sY}.
$$

For \(0\le s,Y<1\),

$$
1-sY\ge1-Y
$$

and

$$
(1-qs)(1-Y)\le1-sY,
$$

the latter because the difference is

$$
(1-s)Y+qs(1-Y)\ge0.
$$

Consequently,

$$
u\le\frac1{1-Y}.
$$

The negative linear term in the risk quadratic may be discarded for an
upper bound:

$$
c^2-\frac{84c}{13}u+\frac{245}{13}u^2
\le
c^2+\frac{245}{13}u^2
\le
c^2+\frac{245}{13(1-Y)^2}.
$$

Since

$$
r(1-r)
=
\frac{(1-s)Y(1-Y)}{(1-sY)^2},
$$

we obtain

$$
\frac{C_\theta}{(1-s)^2}
\le
\frac{16}{49}
\mathbb E\left[
\frac{Y^2}{(1-Y)^2}
\left(
  c^2+\frac{245}{13(1-Y)^2}
\right)
\right].
$$

For the right side, \(Y\sim\operatorname{Beta}(8,6)\), and the exact
inverse beta moments are

$$
\mathbb E\left[\frac{Y^2}{(1-Y)^2}\right]=\frac{18}{5},
\qquad
\mathbb E\left[\frac{Y^2}{(1-Y)^4}\right]=\frac{468}{5}.
$$

They give

$$
M_+
:=
\frac{16}{49}
\mathbb E_{\operatorname{Beta}(8,6)}
\left[
\frac{Y^2}{(1-Y)^2}
\left(
  c^2+\frac{245}{13(1-Y)^2}
\right)
\right]
=
\frac{1194621192}{2028845}.
$$

For the left, swapped side, \(Y\sim\operatorname{Beta}(6,8)\), giving

$$
\mathbb E\left[\frac{Y^2}{(1-Y)^2}\right]=1,
\qquad
\mathbb E\left[\frac{Y^2}{(1-Y)^4}\right]=\frac{39}{5},
$$

and therefore

$$
M_-
:=
\frac{16}{49}
\mathbb E_{\operatorname{Beta}(6,8)}
\left[
\frac{Y^2}{(1-Y)^2}
\left(
  c^2+\frac{245}{13(1-Y)^2}
\right)
\right]
=
\frac{20921716}{405769}.
$$

In particular, \(M_-<M_+\), and on both sides

$$
\boxed{
C_\theta\le M_+(1-s)^2.
}
$$

It follows directly that

$$
\begin{aligned}
2\varepsilon B_\theta+\varepsilon^2C_\theta
&\le
(1-s)^2
\left(
  -2\varepsilon b_0+\varepsilon^2M_+
\right).
\end{aligned}
$$

Thus every fixed

$$
0<\varepsilon
<
\frac{2b_0}{M_+}
=
\boxed{
\frac{3462641}{4508500378608}
}
$$

works uniformly for all \(0<\theta<1\). In particular,

$$
\boxed{\varepsilon=\frac1{2000000}}
$$

is an exact admissible choice, since

$$
\frac1{2000000}
<
\frac{3462641}{4508500378608}.
$$

This argument is stronger than the preceding compactness step: it avoids
division by \(C_\theta\), does not require minimizing a transcendental
ratio, and supplies a concrete perturbation depending only on the two
sample sizes.

**Explicit ratio-free conclusion.** With

$$
\phi(r)
=
r(1-r)
\left[
  \frac37-r+\frac{1045}{5439}r(1-r)
\right],
\qquad
c=\frac{601}{182},
\qquad
\varepsilon=\frac1{2000000},
$$

the exact reduced coefficients satisfy

$$
\boxed{
2\varepsilon B_\theta+\varepsilon^2C_\theta<0
\quad\text{for every }0<\theta<1.
}
$$

## 8. Clipping and remaining formalization caveats

The actual proposed weight is

$$
w_\varepsilon
=
\operatorname{clip}_{[0,1]}
\left(
  r+\varepsilon\phi(r)(c-\widetilde q)
\right).
$$

In literal raw-sample coordinates,

$$
r=\frac{S_1^2/n_1}{S_1^2/n_1+S_2^2/n_2},
\qquad
\widetilde q
=
\frac{(\overline Y-\overline X)^2}
     {S_1^2/n_1+S_2^2/n_2},
$$

so the proposed estimator is

$$
\overline X+w_\varepsilon(\overline Y-\overline X),
$$

with \(n_1=13,n_2=17\),
\(t=3/7\), \(\kappa=1045/5439\), and \(c=601/182\).

Since \(0<\theta<1\), projection onto \([0,1]\) cannot increase the
pointwise distance to \(\theta\):

$$
|w_\varepsilon-\theta|
\le
\left|
  r+\varepsilon\phi(r)(c-\widetilde q)-\theta
\right|.
$$

Therefore clipping can only reduce the risk relative to the unclipped
competitor.

## Formalization status

Status: implemented and compiled through the literal raw-estimator theorem.

The former remaining obligations are now discharged as follows:

1. `UnequalDampedMomentIntegrals.lean`, `UnequalDampedReduced.lean`, and
   the one-sided series modules prove the exact \(B_\theta,C_\theta\)
   certificate and the global fixed-\(\varepsilon\) inequality.
2. `UnequalDampedCanonicalProduct.lean` and
   `UnequalDampedCanonicalLaws.lean` derive those moments from
   \(P\sim\operatorname{Beta}(6,8)\),
   \(L\sim\operatorname{Gamma}(14,1/2)\), and
   \(V\sim\operatorname{Gamma}(1/2,1/2)\), with the required
   independence.
3. `UnequalDampedCanonicalSummary.lean` proves the finite-risk,
   centered-cross-term, clipping, and estimator-level risk statements.
4. `UnequalDampedRawSummary.lean`, `UnequalDampedRawPositivity.lean`, and
   `UnequalDampedRawCoordinates.lean` derive the component laws from the
   two raw normal samples and identify the canonical and literal
   estimators almost everywhere.
5. `UnequalDampedRawRisk.lean` proves the final theorem
   `rawGraybillDealEstimator13_17_strictly_dominated`.

The explicit coefficient used by the final theorem is

$$
\varepsilon=\frac1{2{,}000{,}000},
$$

fixed uniformly over every common mean and every pair of strictly positive
population variances.  `UnequalDampedAxiomAudit.lean` reports only the
standard Lean/Mathlib axioms `propext`, `Classical.choice`, and
`Quot.sound`; no project axiom or proof placeholder is used.
