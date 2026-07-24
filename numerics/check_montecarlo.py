"""Fully independent Monte Carlo + quadrature check of the n=13 claim.

MC uses only bedrock normal theory (Xbar_i ~ N(mu, sig_i^2/n), S_i^2 ~
sig_i^2 chi2_nu / nu, all independent), plus one run from raw 13-observation
samples. Paired differences of squared errors, so the tiny risk gap is
resolvable. Compares against a 1-D quadrature of the paper's formulas (5)-(6).
"""
import numpy as np
from scipy import integrate
from scipy.special import betaln
from math import exp, sqrt

N_ = 13; NU = 12; A = 6.0; EPS = 5e-4
rng = np.random.default_rng(20260725)

def estimators(X1, X2, S1, S2):
    D = X2 - X1
    r = S1/(S1+S2)
    q = N_*D*D/(S1+S2)
    wt = r + EPS*r*(1-r)*(1-2*r)*(4-q)
    ws = np.clip(wt, 0.0, 1.0)
    return X1 + D*r, X1 + D*ws, X1 + D*wt

def mc_reduced(theta, lam=1.0, mu=0.0, ntot=40_000_000, chunk=4_000_000):
    s1sq, s2sq = theta*lam, (1-theta)*lam
    sums = np.zeros(3); sumsq = np.zeros(3); nn = 0
    sum_est = 0.0
    for _ in range(ntot//chunk):
        X1 = mu + sqrt(s1sq/N_)*rng.standard_normal(chunk)
        X2 = mu + sqrt(s2sq/N_)*rng.standard_normal(chunk)
        S1 = s1sq*rng.chisquare(NU, chunk)/NU
        S2 = s2sq*rng.chisquare(NU, chunk)/NU
        gd, st, ut = estimators(X1, X2, S1, S2)
        d_clip = (st-mu)**2 - (gd-mu)**2
        d_uncl = (ut-mu)**2 - (gd-mu)**2
        d_cvsu = (st-mu)**2 - (ut-mu)**2
        for i, d in enumerate((d_clip, d_uncl, d_cvsu)):
            sums[i] += d.sum(); sumsq[i] += (d*d).sum()
        sum_est += st.sum(); nn += chunk
    mean = sums/nn
    se = np.sqrt((sumsq/nn - mean**2)/nn)
    return mean, se, sum_est/nn

def mc_raw(theta, lam=1.0, mu=0.0, ntot=8_000_000, chunk=1_000_000):
    s1, s2 = sqrt(theta*lam), sqrt((1-theta)*lam)
    tot = 0.0; totsq = 0.0; nn = 0
    for _ in range(ntot//chunk):
        Xs1 = mu + s1*rng.standard_normal((chunk, N_))
        Xs2 = mu + s2*rng.standard_normal((chunk, N_))
        gd, st, _ = estimators(Xs1.mean(1), Xs2.mean(1),
                               Xs1.var(1, ddof=1), Xs2.var(1, ddof=1))
        d = (st-mu)**2 - (gd-mu)**2
        tot += d.sum(); totsq += (d*d).sum(); nn += chunk
    mean = tot/nn
    return mean, sqrt((totsq/nn - mean**2)/nn)

# 1-D quadrature of (5),(6): x-density K_a (1-x^2)^(a-1) on (-1,1)
logK = -betaln(A, A) - (2*A-1)*np.log(2.0)
Ka = exp(logK)
def BC_quad(theta):
    sgn = 2*theta - 1
    def integrand(x, which):
        dens = Ka*(1-x*x)**(A-1)
        d = (1+sgn*x)/2
        r = theta*((1+x)/2)/d
        p = r*(1-r)*(1-2*r)
        if which == 'B':
            return dens*(r-theta)*p*(1 - 3*NU/(8*(NU-1)*d))
        return dens*p*p*(1 - 3*NU/(4*(NU-1)*d) + 15*NU*NU/(64*(NU-1)*(NU-2)*d*d))
    Bg = integrate.quad(integrand, -1, 1, args=('B',), limit=200, epsabs=1e-15)[0]
    Cg = integrate.quad(integrand, -1, 1, args=('C',), limit=200, epsabs=1e-15)[0]
    return 4*Bg, 16*Cg  # B_theta, C_theta

print(f"{'theta':>6} {'lam':>4} {'mu':>3} | {'MC diff (clip)':>14} {'SE':>9} {'z':>8} | {'pred (lam/n)(2eB+e2C)':>21} | {'unclip diff':>12} {'clip-unclip':>12}")
for theta, lam, mu in [(0.5,1,0), (0.2,1,0), (0.05,1,0), (0.8,1,0), (0.97,1,0),
                       (0.35,9,0), (0.5,1,5)]:
    mean, se, avg_est = mc_reduced(theta, lam, mu)
    B, C = BC_quad(theta)
    pred = (lam/N_)*(2*EPS*B + EPS*EPS*C)
    print(f"{theta:>6} {lam:>4} {mu:>3} | {mean[0]:>14.3e} {se[0]:>9.1e} {mean[0]/se[0]:>8.1f} | {pred:>21.3e} | {mean[1]:>12.3e} {mean[2]:>12.3e}  Ebias={avg_est-mu:+.2e}")

print("\nraw 13-obs samples, theta=0.3:")
mean, se = mc_raw(0.3)
B, C = BC_quad(0.3)
print(f"MC diff = {mean:.3e} (SE {se:.1e}, z={mean/se:.1f}); predicted {(1/N_)*(2*EPS*B+EPS*EPS*C):.3e}")

# sup over theta of the exact (n/lam)*risk difference via (5)-(6), and inf of -2B/C
print("\nscan theta in (0,1): worst 2eB+e2C and inf -2B/C")
worst = (-np.inf, None); infr = (np.inf, None)
for theta in np.linspace(0.001, 0.999, 999):
    B, C = BC_quad(theta)
    val = 2*EPS*B + EPS*EPS*C
    if val > worst[0]: worst = (val, theta)
    if C > 0 and -2*B/C < infr[0]: infr = (-2*B/C, theta)
print(f"sup (2eB+e2C) = {worst[0]:.4e} at theta={worst[1]:.3f}  (must be < 0)")
print(f"inf -2B/C = {infr[0]:.6f} at theta={infr[1]:.3f}; paper's uniform lower bound 0.000587")
