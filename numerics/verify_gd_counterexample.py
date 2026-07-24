"""Exact and numerical checks for a Graybill--Deal counterexample.

The proposed equal-sample-size n=13 weight is

    w = r + eps * r(1-r)(1-2r) * (4 - q),

where eps=1/2000 and
q=n*(Xbar2-Xbar1)^2/(S1^2+S2^2).

This script checks the exact constants in the analytic proof and then performs
an independent deterministic generalized Gauss--Laguerre risk calculation.
"""

from fractions import Fraction
from math import comb

import numpy as np
from scipy.special import gamma, roots_genlaguerre


N = 13
NU = N - 1
A = Fraction(NU, 2)
EPS = Fraction(1, 2000)
K2 = Fraction(NU * NU, 4 * (NU - 1) * (NU - 2))


def exact_checks() -> None:
    # Integral constants in the proof.
    # Work first with g=p(r)*(1-q/4), then rescale h=4g.
    alpha = Fraction(2, 11)
    c = Fraction(1, 4)
    m1 = Fraction(1024, 45045)
    j4 = Fraction(256, 165)
    j6 = Fraction(64, 9)
    h_bound = j4 + 60 * c * c * K2 * j6

    # Keeping the first three series terms gives the uniform lower bound
    # I(s)/M1 >= 1489/5610.  The allowable step for h=4g is one quarter
    # of the corresponding step for g.
    ell = Fraction(1489, 5610)
    eps0 = m1 * ell / h_bound

    assert A == 6
    assert 1 - 3 * c * NU / (NU - 1) == alpha
    assert K2 == Fraction(18, 55)
    assert h_bound == Fraction(1696, 165)
    assert eps0 == Fraction(23824, 40585545)
    assert EPS < eps0

    # Explicit coefficients in the series for I(s).  Q1 is the only
    # negative coefficient; Q2 and every later coefficient are positive.
    q0 = Fraction(4, 11)
    q1 = -Fraction(116, 33)
    q2 = Fraction(232, 11)
    assert q0 > 0 and q1 < 0 and q2 > 0

    d = [
        Fraction(8232, 11),
        Fraction(20148, 11),
        Fraction(23236, 11),
        Fraction(13040, 11),
        Fraction(2880, 11),
    ]
    assert all(value > 0 for value in d)
    for m in range(3, 1000):
        numerator = sum(d[j] * comb(m - 3, j) for j in range(5))
        assert numerator > 0

    print(f"exact epsilon bound = {float(eps0):.12g} ({eps0})")
    print(f"chosen epsilon      = {float(EPS):.12g} ({EPS})")
    print(f"exact safety factor = {float(eps0 / EPS):.9g}")


def chi_square_rule(df: int, order: int) -> tuple[np.ndarray, np.ndarray]:
    shape = df / 2
    nodes, weights = roots_genlaguerre(order, shape - 1)
    return 2 * nodes, weights / gamma(shape)


def deterministic_risk_check(order: int = 70) -> None:
    u, wu = chi_square_rule(NU, order)
    v, wv = chi_square_rule(1, order)
    u1 = u[:, None, None]
    u2 = u[None, :, None]
    vv = v[None, None, :]
    weights = wu[:, None, None] * wu[None, :, None] * wv[None, None, :]

    theta_grid = np.unique(
        np.r_[
            np.geomspace(1e-7, 1e-3, 30),
            np.linspace(1e-3, 0.5, 500),
        ]
    )
    worst = (-np.inf, None)
    for theta in theta_grid:
        denom = theta * u1 + (1 - theta) * u2
        r = theta * u1 / denom
        q = NU * vv / denom
        p = r * (1 - r) * (1 - 2 * r)
        h0 = p * (4 - q)
        integrand = vv * (
            2 * float(EPS) * (r - theta) * h0
            + float(EPS) ** 2 * h0 * h0
        )
        scaled_difference = float(np.sum(weights * integrand))
        if scaled_difference > worst[0]:
            worst = (scaled_difference, theta)

    assert worst[0] < 0
    print(
        "largest quadrature value of n*(R_new-R_GD)/lambda "
        f"on the grid = {worst[0]:.12g} at theta={worst[1]:.12g}"
    )


if __name__ == "__main__":
    exact_checks()
    deterministic_risk_check()