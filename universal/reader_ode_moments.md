# The universal analytic contradiction, in reader-level detail

This note expands the final analytic part of the proposed nonconstructive
proof that the Graybill--Deal estimator is inadmissible for every pair
\(n_1,n_2\geq2\).

It begins **after** the limiting-Bayes theorem has been applied. That
decision-theoretic argument is assumed to have produced a probability
measure \(\nu\) on \([0,1]\) satisfying the identity below. Everything in
this note is then elementary calculus and algebra. In particular, all
expectations are expectations under the single probability measure \(\nu\).

Put

$$
a=\frac{n_1-1}{2},\qquad
b=\frac{n_2-1}{2},\qquad
h=a+b,
\tag{1}
$$

and

$$
p=h+\frac32,\qquad
\lambda=p-1=h+\frac12.
\tag{2}
$$

Because \(n_1,n_2\geq2\), both \(a\) and \(b\) are strictly positive.
The identity forced by the assumed admissibility is

$$
A_\nu(r,q)
:=
\frac{\displaystyle
      \int_0^1\theta B_\theta(r,q)^{-p}\,\nu(d\theta)}
     {\displaystyle
      \int_0^1 B_\theta(r,q)^{-p}\,\nu(d\theta)}
=r
\tag{3}
$$

for every \(0<r<1\) and \(q\geq0\), where

$$
B_\theta(r,q)
=2ar(1-\theta)+2b(1-r)\theta+q\theta(1-\theta).
\tag{4}
$$

The goal is to show that no probability measure \(\nu\) can satisfy (3).

There is no hidden problem caused by atoms of \(\nu\) at \(0\) or \(1\).
For \(0<r<1\) and \(q\geq0\),

$$
B_\theta(r,q)
\geq
\min\{2ar,\,2b(1-r)\}>0,
\tag{5}
$$

because the first two terms in (4) form an affine interpolation between
\(2ar\) and \(2b(1-r)\), and the \(q\)-term is nonnegative. Thus all the
integrands used below are bounded when \((r,q)\) stays in a sufficiently
small neighborhood of a point under consideration. Differentiation under
the integral sign follows directly from dominated convergence.

Whenever a derivative in \(q\) is evaluated at \(q=0\), it is formally the
right derivative because the statistical coordinate has \(q\ge0\).
Equivalently, at each interior \(r\) the denominator in (5) remains
positive for all sufficiently small negative \(q\), so the displayed
integral formula has a local smooth extension across \(q=0\).

---

## Part I. The \(q=0\) differential equation for general \(a,b\)

### 1. Remove the irrelevant factor \(2\)

At \(q=0\), define

$$
u_\theta(r)
=ar(1-\theta)+b(1-r)\theta.
\tag{6}
$$

Then \(B_\theta(r,0)=2u_\theta(r)\). The factor \(2^{-p}\)
cancels between the numerator and denominator of (3), so

$$
\frac{E_\nu[\theta u_\theta(r)^{-p}]}
     {E_\nu[u_\theta(r)^{-p}]}
=r.
\tag{7}
$$

Define

$$
I(r)=E_\nu[u_\theta(r)^{-p}]
\tag{8}
$$

and

$$
F(r)=E_\nu[u_\theta(r)^{-\lambda}].
\tag{9}
$$

The reason for choosing the exponent \(-\lambda=-(p-1)\) is that

$$
u_\theta(r)^{-\lambda}
=u_\theta(r)\,u_\theta(r)^{-p}.
\tag{10}
$$

Equation (7) is precisely

$$
E_\nu[\theta u_\theta(r)^{-p}]=rI(r).
\tag{11}
$$

Therefore

$$
E_\nu[(1-\theta)u_\theta(r)^{-p}]
=I(r)-rI(r)
=(1-r)I(r).
\tag{12}
$$

Now multiply out (10), using the definition (6):

$$
\begin{aligned}
F(r)
&=E_\nu[u_\theta(r)u_\theta(r)^{-p}]\\
&=arE_\nu[(1-\theta)u_\theta(r)^{-p}]
  +b(1-r)E_\nu[\theta u_\theta(r)^{-p}]\\
&=ar(1-r)I(r)+b(1-r)rI(r)\\
&=(a+b)r(1-r)I(r)\\
&=hr(1-r)I(r).
\end{aligned}
\tag{13}
$$

This is the first relation between \(F\) and \(I\).

### 2. Differentiate \(F\)

The derivative of (6) with respect to \(r\) is

$$
\frac{\partial u_\theta(r)}{\partial r}
=a(1-\theta)-b\theta
=a-(a+b)\theta
=a-h\theta.
\tag{14}
$$

Consequently,

$$
\begin{aligned}
F'(r)
&=-\lambda
 E_\nu[(a-h\theta)u_\theta(r)^{-\lambda-1}]\\
&=-\lambda
 E_\nu[(a-h\theta)u_\theta(r)^{-p}]\\
&=-\lambda
 \left\{aI(r)-hE_\nu[\theta u_\theta(r)^{-p}]\right\}\\
&=-\lambda(a-hr)I(r),
\end{aligned}
\tag{15}
$$

where \(\lambda+1=p\) and (11) were used.

Divide (15) by (13). Since \(F(r)>0\),

$$
\begin{aligned}
\frac{F'(r)}{F(r)}
&=-\lambda\frac{a-hr}{hr(1-r)}\\
&=-\lambda
\left\{
\frac{a}{hr}-\frac{b}{h(1-r)}
\right\}.
\end{aligned}
\tag{16}
$$

To verify the partial fractions in the last line, combine them:

$$
\frac{a}{hr}-\frac{b}{h(1-r)}
=
\frac{a(1-r)-br}{hr(1-r)}
=
\frac{a-(a+b)r}{hr(1-r)}
=
\frac{a-hr}{hr(1-r)}.
$$

**WolframAlpha check**

```text
partial fractions (a-(a+b)r)/((a+b)r(1-r)) with respect to r
```

### 3. Solve the ODE

Because \(F'/F=(\log F)'\), integrating (16) gives

$$
\log F(r)
=-\frac{\lambda a}{h}\log r
 -\frac{\lambda b}{h}\log(1-r)
 +C.
\tag{17}
$$

The second logarithm also has a minus sign because

$$
\int\frac{1}{1-r}\,dr=-\log(1-r).
$$

Exponentiating (17),

$$
F(r)=C_0
r^{-\lambda a/h}
(1-r)^{-\lambda b/h},
\qquad C_0>0.
\tag{18}
$$

**WolframAlpha check**

```text
integrate -lam*a/((a+b)r) + lam*b/((a+b)(1-r)) with respect to r
```

---

## Part II. Center the ODE solution and obtain a moment transform

Define

$$
r_0=\frac{b}{h},
\qquad
c=\frac{ab}{h},
\qquad
Z=a-h\theta.
\tag{19}
$$

The choice \(r_0=b/h\) is important because it makes
\(u_\theta(r_0)\) independent of \(\theta\):

$$
\begin{aligned}
u_\theta(r_0)
&=a\frac bh(1-\theta)
  +b\left(1-\frac bh\right)\theta\\
&=\frac{ab}{h}(1-\theta)
  +\frac{ab}{h}\theta\\
&=\frac{ab}{h}=c.
\end{aligned}
\tag{20}
$$

Now write

$$
r=r_0+ct.
\tag{21}
$$

Since \(u_\theta(r)\) is affine in \(r\), (14) and (20) give

$$
\begin{aligned}
u_\theta(r_0+ct)
&=u_\theta(r_0)+ct(a-h\theta)\\
&=c(1+tZ).
\end{aligned}
\tag{22}
$$

It follows from (9) that

$$
\begin{aligned}
F(r_0+ct)
&=c^{-\lambda}E_\nu[(1+tZ)^{-\lambda}],\\
F(r_0)
&=E_\nu[c^{-\lambda}]
=c^{-\lambda},
\end{aligned}
$$

where the last equality uses the fact that \(\nu\) is a probability
measure. Dividing these two equalities gives

$$
\frac{F(r_0+ct)}{F(r_0)}
=E_\nu[(1+tZ)^{-\lambda}].
\tag{23}
$$

On the other hand,

$$
\frac{r_0+ct}{r_0}
=1+at,
\tag{24}
$$

because \(c/r_0=(ab/h)/(b/h)=a\), while

$$
\frac{1-r_0-ct}{1-r_0}
=1-bt,
\tag{25}
$$

because \(c/(1-r_0)=(ab/h)/(a/h)=b\).

Divide (18) at \(r=r_0+ct\) by (18) at \(r=r_0\), then use
(23)--(25). This gives the central transform identity

$$
\boxed{
E_\nu[(1+tZ)^{-\lambda}]
=(1+at)^{-\lambda a/h}
 (1-bt)^{-\lambda b/h}.
}
\tag{26}
$$

Since \(r=r_0+ct\), the exact interval inherited from \(0<r<1\) is

$$
-\frac1a<t<\frac1b.
$$

On this interval, \(\theta\in[0,1]\) implies \(Z\in[-b,a]\) and hence
\(1+tZ>0\). On every smaller closed interval containing zero,
\(1+tZ\) is uniformly bounded away from zero. Term-by-term
differentiation at zero is therefore justified by dominated convergence.

**WolframAlpha checks**

```text
simplify (b/(a+b) + (a*b/(a+b))*t)/(b/(a+b))
```

```text
simplify (1-b/(a+b) - (a*b/(a+b))*t)/(1-b/(a+b))
```

---

## Part III. Extract \(E[Z]\), \(E[Z^2]\), and \(E[Z^3]\)

Let

$$
G(t)
=(1+at)^{-\lambda a/h}
 (1-bt)^{-\lambda b/h}
\tag{27}
$$

denote the right side of (26), and let

$$
\ell(t)=\log G(t)
=-\frac{\lambda a}{h}\log(1+at)
 -\frac{\lambda b}{h}\log(1-bt).
\tag{28}
$$

For compactness, put

$$
d=a-b,\qquad
K=a^2-ab+b^2,\qquad
S=a^2+b^2.
\tag{29}
$$

### 1. Derivatives of the logarithm

Differentiate (28). At \(t=0\),

$$
\begin{aligned}
\ell'(0)
&=-\frac{\lambda a^2}{h}
  +\frac{\lambda b^2}{h}\\
&=\frac{\lambda(b^2-a^2)}{h}\\
&=\lambda(b-a)\\
&=-\lambda d.
\end{aligned}
\tag{30}
$$

For the second derivative,

$$
\begin{aligned}
\ell''(0)
&=\frac{\lambda(a^3+b^3)}{h}\\
&=\lambda(a^2-ab+b^2)\\
&=\lambda K,
\end{aligned}
\tag{31}
$$

where

$$
a^3+b^3=(a+b)(a^2-ab+b^2)=hK.
$$

For the third derivative,

$$
\begin{aligned}
\ell'''(0)
&=\frac{2\lambda(b^4-a^4)}{h}\\
&=\frac{2\lambda(b-a)(b+a)(a^2+b^2)}{h}\\
&=-2\lambda dS.
\end{aligned}
\tag{32}
$$

**WolframAlpha check**

```text
first three derivatives at t=0 of
log((1+a*t)^(-lam*a/(a+b))*(1-b*t)^(-lam*b/(a+b)))
```

### 2. Convert log derivatives into derivatives of \(G\)

Since \(G=e^\ell\) and \(G(0)=1\),

$$
G'(0)=\ell'(0),
\tag{33}
$$

$$
G''(0)=\ell''(0)+\ell'(0)^2,
\tag{34}
$$

and

$$
G'''(0)
=\ell'''(0)
 +3\ell'(0)\ell''(0)
 +\ell'(0)^3.
\tag{35}
$$

Substituting (30)--(32),

$$
G'(0)=-\lambda d,
\tag{36}
$$

$$
G''(0)=\lambda K+\lambda^2d^2,
\tag{37}
$$

and

$$
G'''(0)
=-\lambda d
\left\{
2S+3\lambda K+\lambda^2d^2
\right\}.
\tag{38}
$$

### 3. Derivatives of the left side of (26)

For a fixed \(Z\),

$$
\left.\frac{d}{dt}(1+tZ)^{-\lambda}\right|_{t=0}
=-\lambda Z,
$$

$$
\left.\frac{d^2}{dt^2}(1+tZ)^{-\lambda}\right|_{t=0}
=\lambda(\lambda+1)Z^2,
$$

and

$$
\left.\frac{d^3}{dt^3}(1+tZ)^{-\lambda}\right|_{t=0}
=-\lambda(\lambda+1)(\lambda+2)Z^3.
$$

Equate these expected derivatives with (36)--(38). The first derivative
gives

$$
-\lambda E_\nu[Z]=-\lambda d,
$$

so

$$
\boxed{E_\nu[Z]=d=a-b.}
\tag{39}
$$

The second derivative gives

$$
\lambda(\lambda+1)E_\nu[Z^2]
=\lambda K+\lambda^2d^2,
$$

so

$$
\boxed{
E_\nu[Z^2]
=\frac{K+\lambda d^2}{\lambda+1}.
}
\tag{40}
$$

The third derivative gives

$$
-\lambda(\lambda+1)(\lambda+2)E_\nu[Z^3]
=-\lambda d
\{2S+3\lambda K+\lambda^2d^2\},
$$

so

$$
\boxed{
E_\nu[Z^3]
=
\frac{d\{2S+3\lambda K+\lambda^2d^2\}}
     {(\lambda+1)(\lambda+2)}.
}
\tag{41}
$$

---

## Part IV. Compute the unequal-size obstruction

We need

$$
E_\nu[(\theta-r_0)\theta(1-\theta)].
\tag{42}
$$

Since \(Z=a-h\theta\), equations (19) give

$$
\theta=\frac{a-Z}{h},
\qquad
\theta-r_0=\frac{a-b-Z}{h}=\frac{d-Z}{h},
\qquad
1-\theta=\frac{b+Z}{h}.
\tag{43}
$$

Therefore

$$
(\theta-r_0)\theta(1-\theta)
=\frac{(d-Z)(a-Z)(b+Z)}{h^3}.
\tag{44}
$$

First expand the numerator:

$$
(a-Z)(b+Z)=ab+dZ-Z^2,
$$

and hence

$$
\begin{aligned}
(d-Z)(a-Z)(b+Z)
&=(d-Z)(ab+dZ-Z^2)\\
&=abd+(d^2-ab)Z-2dZ^2+Z^3.
\end{aligned}
\tag{45}
$$

Taking expectations and using \(E[Z]=d\), the first two terms combine:

$$
abd+(d^2-ab)E[Z]
=abd+(d^2-ab)d
=d^3.
$$

Thus

$$
E_\nu[(\theta-r_0)\theta(1-\theta)]
=\frac{d^3-2dE[Z^2]+E[Z^3]}{h^3}.
\tag{46}
$$

Substitute (40)--(41). After using a common denominator,

$$
\begin{aligned}
&d^3-2dE[Z^2]+E[Z^3]\\
&\quad
=\frac{d}{(\lambda+1)(\lambda+2)}
\big[
d^2(\lambda+1)(\lambda+2)
-2(K+\lambda d^2)(\lambda+2)\\
&\hspace{51mm}
+2S+3\lambda K+\lambda^2d^2
\big]\\
&\quad
=\frac{d}{(\lambda+1)(\lambda+2)}
\big[(2-\lambda)d^2+(\lambda-4)K+2S\big].
\end{aligned}
\tag{47}
$$

The remaining bracket has a particularly simple value. Since

$$
d^2=S-2ab,\qquad K=S-ab,
\tag{48}
$$

we obtain

$$
\begin{aligned}
(2-\lambda)d^2+(\lambda-4)K+2S
&=(2-\lambda)(S-2ab)
  +(\lambda-4)(S-ab)+2S\\
&=\big[(2-\lambda)+(\lambda-4)+2\big]S\\
&\quad
 +\big[-2(2-\lambda)-(\lambda-4)\big]ab\\
&=\lambda ab.
\end{aligned}
\tag{49}
$$

Therefore (46)--(49) give

$$
E_\nu[(\theta-r_0)\theta(1-\theta)]
=
\frac{\lambda ab(a-b)}
     {h^3(\lambda+1)(\lambda+2)}.
\tag{50}
$$

Finally, substitute

$$
\lambda=\frac{2h+1}{2},\qquad
\lambda+1=\frac{2h+3}{2},\qquad
\lambda+2=\frac{2h+5}{2}.
$$

This yields

$$
\boxed{
E_\nu[(\theta-r_0)\theta(1-\theta)]
=
\frac{2ab(a-b)(2h+1)}
     {h^3(2h+3)(2h+5)}.
}
\tag{51}
$$

**WolframAlpha checks**

```text
expand (d-z)(a-z)(b+z)
```

```text
simplify
(a-b)^3
-2(a-b)*(a^2-a*b+b^2+lam*(a-b)^2)/(lam+1)
+(a-b)*(2*(a^2+b^2)+3*lam*(a^2-a*b+b^2)+lam^2*(a-b)^2)
 /((lam+1)*(lam+2))
```

The expected simplified answer to the second query is

```text
a*b*lam*(a-b)/((lam+1)*(lam+2))
```

---

## Part V. Differentiate in \(q\): contradiction when \(a\neq b\)

At \(r=r_0=b/h\), equation (20) shows that

$$
B_\theta(r_0,0)=2u_\theta(r_0)=2c
\tag{52}
$$

for every \(\theta\), where \(c=ab/h\).

For fixed \(r=r_0\), write

$$
N(q)=E_\nu[\theta B_\theta(r_0,q)^{-p}],
\qquad
D(q)=E_\nu[B_\theta(r_0,q)^{-p}].
\tag{53}
$$

Then \(A_\nu(r_0,q)=N(q)/D(q)\). Since

$$
\frac{\partial B_\theta(r_0,q)}{\partial q}
=\theta(1-\theta),
$$

the chain rule gives

$$
N'(q)
=-pE_\nu[
\theta^2(1-\theta)B_\theta(r_0,q)^{-p-1}]
\tag{54}
$$

and

$$
D'(q)
=-pE_\nu[
\theta(1-\theta)B_\theta(r_0,q)^{-p-1}].
\tag{55}
$$

The quotient rule can be written as

$$
\partial_q A_\nu
=\frac{N'-A_\nu D'}{D}.
\tag{56}
$$

At \(q=0\),

$$
A_\nu(r_0,0)=r_0,\qquad
D(0)=(2c)^{-p},
\tag{57}
$$

and every occurrence of \(B_\theta(r_0,0)\) in (54)--(55) equals
\(2c\). Substitution into (56) gives

$$
\begin{aligned}
\partial_{q+}A_\nu(r_0,0)
&=
\frac{-p(2c)^{-p-1}
E_\nu[(\theta-r_0)\theta(1-\theta)]}
{(2c)^{-p}}\\
&=-\frac{p}{2c}
E_\nu[(\theta-r_0)\theta(1-\theta)].
\end{aligned}
\tag{58}
$$

Use \(c=ab/h\), \(p=(2h+3)/2\), and (51):

$$
\boxed{
\partial_{q+}A_\nu(r_0,0)
=
-\frac{(a-b)(2h+1)}
       {2h^2(2h+5)}.
}
\tag{59}
$$

Every factor in the denominator is strictly positive. Thus (59) is
nonzero exactly when \(a\neq b\), equivalently \(n_1\neq n_2\).

But (3) says \(A_\nu(r_0,q)=r_0\) for every \(q\geq0\).
The right derivative at \(q=0\) of this constant function must be zero.
Equation (59) is therefore a contradiction whenever the two sample sizes
are unequal.

**WolframAlpha check**

```text
simplify
-(a+b+3/2)/(2*a*b/(a+b))
 * 2*a*b*(a-b)*(2*(a+b)+1)
 / ((a+b)^3*(2*(a+b)+3)*(2*(a+b)+5))
```

The result should be

```text
-(a-b)(2(a+b)+1)/(2(a+b)^2(2(a+b)+5))
```

---

## Part VI. The equal-size diagonal \(a=b\)

When \(a=b\), formula (59) vanishes. This is expected from symmetry, so
we need one more derivative.

### 1. Specialize the transform

Now set \(b=a\). Then

$$
h=2a,\qquad
\lambda=2a+\frac12,\qquad
p=\lambda+1=2a+\frac32.
\tag{60}
$$

Define

$$
Y=1-2\theta.
\tag{61}
$$

The variable \(Z=a-h\theta\) from (19) becomes

$$
Z=a(1-2\theta)=aY.
$$

The exponents on the right side of (26) are both \(-\lambda/2\).
Replacing \(at\) by a new variable \(s\), equation (26) becomes

$$
\boxed{
E_\nu[(1+sY)^{-\lambda}]
=(1+s)^{-\lambda/2}(1-s)^{-\lambda/2}
=(1-s^2)^{-\lambda/2}.
}
\tag{62}
$$

### 2. Extract the second and fourth moments

The left side of (62), through fourth order, is

$$
\begin{aligned}
E_\nu[(1+sY)^{-\lambda}]
&=1-\lambda E[Y]s
 +\frac{\lambda(\lambda+1)}2E[Y^2]s^2\\
&\quad
-\frac{\lambda(\lambda+1)(\lambda+2)}6E[Y^3]s^3\\
&\quad
+\frac{\lambda(\lambda+1)(\lambda+2)(\lambda+3)}{24}
 E[Y^4]s^4
+O(s^5).
\end{aligned}
\tag{63}
$$

The right side is

$$
(1-s^2)^{-\lambda/2}
=1+\frac{\lambda}{2}s^2
 +\frac{\lambda(\lambda+2)}8s^4
 +O(s^6).
\tag{64}
$$

Comparing coefficients gives

$$
E[Y]=0,\qquad E[Y^3]=0,
\tag{65}
$$

$$
\frac{\lambda(\lambda+1)}2E[Y^2]
=\frac{\lambda}{2},
$$

and

$$
\frac{\lambda(\lambda+1)(\lambda+2)(\lambda+3)}{24}
E[Y^4]
=\frac{\lambda(\lambda+2)}8.
$$

Hence

$$
\boxed{
E[Y^2]=\frac1{\lambda+1}=\frac1p,
\qquad
E[Y^4]
=\frac3{(\lambda+1)(\lambda+3)}
=\frac3{p(p+2)}.
}
\tag{66}
$$

**WolframAlpha checks**

```text
series (1+s*y)^(-lam) at s=0 through s^4
```

```text
series (1-s^2)^(-lam/2) at s=0 through s^4
```

### 3. Rewrite \(B_\theta(r,q)\) in centered coordinates

Put

$$
x=r-\frac12
\tag{67}
$$

and

$$
C(Y)=\theta(1-\theta)=\frac{1-Y^2}{4}.
\tag{68}
$$

Since \(\theta=(1-Y)/2\), direct substitution in (4) gives

$$
\boxed{
B_\theta(r,q)=a+2axY+qC(Y).
}
\tag{69}
$$

At the central point \(r=1/2,q=0\), this is simply

$$
B_\theta(1/2,0)=a,
\tag{70}
$$

independently of \(\theta\).

**WolframAlpha check**

```text
expand 2*a*r*(1-(1-y)/2) + 2*a*(1-r)*(1-y)/2
substitute r=1/2+x
```

### 4. Compute the mixed derivative

Define

$$
\mathcal N(r,q)
=E_\nu[\theta B_\theta(r,q)^{-p}],
\qquad
\mathcal D(r,q)
=E_\nu[B_\theta(r,q)^{-p}],
\tag{71}
$$

so \(A_\nu=\mathcal N/\mathcal D\).
From (69),

$$
B_r=2aY,\qquad B_q=C(Y),\qquad B_{rq}=0.
\tag{72}
$$

At \(r=1/2,q=0\), equations (65) and (70) give

$$
\mathcal D=a^{-p},
\tag{73}
$$

and

$$
\mathcal D_r
=-2ap\,a^{-p-1}E[Y]
=0.
\tag{74}
$$

Also,

$$
E[\theta Y]
=E\left[\frac{1-Y}{2}Y\right]
=\frac12(E[Y]-E[Y^2])
=-\frac12E[Y^2].
\tag{75}
$$

Therefore

$$
\begin{aligned}
\mathcal N_r
&=-2ap\,a^{-p-1}E[\theta Y]\\
&=p\,a^{-p}E[Y^2].
\end{aligned}
\tag{76}
$$

The \(q\)-derivative of the denominator is

$$
\mathcal D_q
=-p\,a^{-p-1}E[C].
\tag{77}
$$

Next,

$$
\mathcal D_{rq}
=2ap(p+1)a^{-p-2}E[YC].
\tag{78}
$$

But \(C=(1-Y^2)/4\), so

$$
E[YC]=\frac14(E[Y]-E[Y^3])=0
\tag{79}
$$

by (65). Hence \(\mathcal D_{rq}=0\).

Similarly,

$$
\mathcal N_{rq}
=2ap(p+1)a^{-p-2}E[\theta YC].
\tag{80}
$$

Using \(\theta=(1-Y)/2\) and (79),

$$
\begin{aligned}
E[\theta YC]
&=\frac12E[(1-Y)YC]\\
&=\frac12\{E[YC]-E[Y^2C]\}\\
&=-\frac12E[Y^2C].
\end{aligned}
$$

Therefore

$$
\mathcal N_{rq}
=-p(p+1)a^{-p-1}E[Y^2C].
\tag{81}
$$

Differentiate \(A_\nu=\mathcal N/\mathcal D\), first in \(r\) and
then in \(q\). At a point where
\(\mathcal D_r=\mathcal D_{rq}=0\), the quotient rule reduces to

$$
A_{rq}
=\frac{\mathcal N_{rq}}{\mathcal D}
 -\frac{\mathcal N_r\mathcal D_q}{\mathcal D^2}.
\tag{82}
$$

For completeness, begin with

$$
A_r
=\frac{\mathcal N_r\mathcal D-\mathcal N\mathcal D_r}
       {\mathcal D^2}.
$$

Differentiating this expression in \(q\), and then setting
\(\mathcal D_r=\mathcal D_{rq}=0\), gives

$$
\begin{aligned}
A_{rq}
&=
\frac{\mathcal N_{rq}\mathcal D+\mathcal N_r\mathcal D_q}
     {\mathcal D^2}
-\frac{2\mathcal N_r\mathcal D\,\mathcal D_q}
      {\mathcal D^3}\\
&=\frac{\mathcal N_{rq}}{\mathcal D}
-\frac{\mathcal N_r\mathcal D_q}{\mathcal D^2},
\end{aligned}
$$

which proves (82).

Substitute (73), (76), (77), and (81):

$$
A_{rq}
=\frac{p}{a}
\left\{
-(p+1)E[Y^2C]
+pE[Y^2]E[C]
\right\}.
\tag{83}
$$

Write

$$
m_2=E[Y^2]=\frac1p,
\qquad
m_4=E[Y^4]=\frac3{p(p+2)}.
\tag{84}
$$

Since \(C=(1-Y^2)/4\),

$$
E[C]=\frac{1-m_2}{4},
\qquad
E[Y^2C]=\frac{m_2-m_4}{4}.
\tag{85}
$$

Thus

$$
A_{rq}
=\frac{p}{4a}
\left\{
-(p+1)(m_2-m_4)
+pm_2(1-m_2)
\right\}.
\tag{86}
$$

The two combinations of moments simplify to

$$
m_2-m_4
=\frac1p-\frac3{p(p+2)}
=\frac{p-1}{p(p+2)}
\tag{87}
$$

and

$$
m_2(1-m_2)
=\frac1p\left(1-\frac1p\right)
=\frac{p-1}{p^2}.
\tag{88}
$$

Substitute (87)--(88) into (86):

$$
\begin{aligned}
A_{rq}
&=\frac{p}{4a}
\frac{p-1}{p}
\left\{
-\frac{p+1}{p+2}+1
\right\}\\
&=\boxed{
\frac{p-1}{4a(p+2)}
}.
\end{aligned}
\tag{89}
$$

This number is strictly positive because \(a>0\) and \(p>1\).

But the identity (3) says \(A_\nu(r,q)=r\). Therefore

$$
\frac{\partial A_\nu}{\partial r}=1
$$

for every \(q\geq0\), and its right derivative with respect to \(q\)
must be zero:

$$
\partial_{q+}\partial_r A_\nu(1/2,0)=0.
$$

Equation (89) says the same derivative is strictly positive. This is the
required contradiction on the equal-size diagonal.

**WolframAlpha check**

```text
simplify
p/(4*a)
 * (-(p+1)*(1/p-3/(p*(p+2)))
    +p*(1/p)*(1-1/p))
```

The answer should be

```text
(p-1)/(4*a*(p+2))
```

---

## Part VII. Concrete checks

### Unequal pair \((n_1,n_2)=(2,3)\)

Here

$$
a=\frac12,\quad b=1,\quad h=\frac32,\quad
\lambda=2,\quad p=3,\quad r_0=\frac23.
$$

Formula (26) becomes

$$
E_\nu\left[
1+t\left(\frac12-\frac32\theta\right)
\right]^{-2}
=(1+t/2)^{-2/3}(1-t)^{-4/3}.
$$

If \(Z=\frac12-\frac32\theta\), the two sides expand as

$$
1-2E[Z]t+3E[Z^2]t^2-4E[Z^3]t^3+O(t^4)
$$

and

$$
1+t+\frac54t^2+\frac43t^3+O(t^4).
$$

Thus

$$
E[Z]=-\frac12,\qquad
E[Z^2]=\frac5{12},\qquad
E[Z^3]=-\frac13.
$$

Moreover,

$$
\left(\theta-\frac23\right)\theta(1-\theta)
=-\frac2{27}(1+Z-4Z^2-4Z^3),
$$

so direct substitution gives

$$
-\frac2{27}
\left(1-\frac12-\frac53+\frac43\right)
=-\frac1{81}.
$$

Formula (51) gives

$$
E_\nu[(\theta-\tfrac23)\theta(1-\theta)]
=-\frac1{81},
$$

and formula (59) gives

$$
\partial_{q+}A_\nu(2/3,0)=\frac1{18}.
$$

**WolframAlpha checks**

```text
series (1+t/2)^(-2/3)*(1-t)^(-4/3) at t=0 through t^3
```

```text
expand (-(1+2z)/3)*((1-2z)/3)*(2(1+z)/3)
```

```text
2*(1/2)*1*((1/2)-1)*(2*(3/2)+1)
/((3/2)^3*(2*(3/2)+3)*(2*(3/2)+5))
```

```text
-((1/2)-1)*(2*(3/2)+1)
/(2*(3/2)^2*(2*(3/2)+5))
```

### Equal pair \((n_1,n_2)=(2,2)\)

Here \(a=1/2\) and \(p=5/2\). Formula (89) gives

$$
\partial_{q+}\partial_r A_\nu(1/2,0)
=\frac16>0.
$$

**WolframAlpha check**

```text
((5/2)-1)/(4*(1/2)*((5/2)+2))
```

---

## Final logical structure

The final analytic argument has exactly two branches:

1. If \(n_1\neq n_2\), then \(a\neq b\), and (59) gives a nonzero
   right \(q\)-derivative of a function that (3) says is constant in \(q\).
2. If \(n_1=n_2\), then \(a=b\); the first derivative vanishes by
   symmetry, but (89) gives a strictly positive mixed derivative where
   (3) requires zero.

Thus no probability measure \(\nu\) satisfying (3) exists for any
\(a,b>0\). Combined with the preceding decision-theoretic implication

$$
\text{admissibility}\quad\Longrightarrow\quad
\text{existence of such a }\nu,
$$

this completes the analytic contradiction for every
\(n_1,n_2\geq2\).
