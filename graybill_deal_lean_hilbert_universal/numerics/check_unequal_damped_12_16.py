#!/usr/bin/env python3
"""Exact checks for UNEQUAL_DAMPED_12_16_NOTE.md.

Requires sympy.  scipy and numpy are used only for the optional numerical
diagnostic at the end.
"""

from __future__ import annotations

import sympy as sp


p, y = sp.symbols("p y")
n, mshift = sp.symbols("n m", integer=True, nonnegative=True)

a = sp.Integer(6)
b = sp.Integer(8)
A = a + b
t = a / A
q = b / A

k = 3 * A / (A - 1)
c = k + 1 / A
delta = sp.factor(c - k)


def beta_p_moment(order: int, aa: sp.Expr = a, bb: sp.Expr = b) -> sp.Expr:
    """E[P^order] for P ~ Beta(aa,bb)."""

    return sp.rf(aa, order) / sp.rf(aa + bb, order)


def beta_p_expect(poly: sp.Expr, aa: sp.Expr = a, bb: sp.Expr = b) -> sp.Expr:
    """Exact expectation of a polynomial in p under Beta(aa,bb)."""

    pp = sp.Poly(sp.expand(poly), p)
    return sp.factor(
        sum(
            coefficient * beta_p_moment(power, aa, bb)
            for (power,), coefficient in pp.terms()
        )
    )


X = p - t
pq = p * (1 - p)
kappa_num = beta_p_expect(X**3 * pq)
kappa_den = beta_p_expect(X**2 * pq**2)
kappa = sp.factor(kappa_num / kappa_den)

assert kappa_num == sp.Rational(11, 81634)
assert kappa_den == sp.Rational(111, 158270)
assert kappa == sp.Rational(1045, 5439)
assert k == sp.Rational(42, 13)
assert c == sp.Rational(601, 182)
assert delta == sp.Rational(1, 14)

phi_pivot = pq * (-X + kappa * pq)
M1_pivot = beta_p_expect(X * phi_pivot)
B_pivot = sp.factor(delta * M1_pivot)

assert M1_pivot == -sp.Rational(2927, 924630)
assert B_pivot == -sp.Rational(2927, 12944820)


def poly_add(left: list[sp.Expr], right: list[sp.Expr]) -> list[sp.Expr]:
    out = [sp.Integer(0)] * max(len(left), len(right))
    for index, value in enumerate(left):
        out[index] += value
    for index, value in enumerate(right):
        out[index] += value
    return [sp.factor(value) for value in out]


def poly_mul(left: list[sp.Expr], right: list[sp.Expr]) -> list[sp.Expr]:
    out = [sp.Integer(0)] * (len(left) + len(right) - 1)
    for i, left_value in enumerate(left):
        for j, right_value in enumerate(right):
            out[i + j] += left_value * right_value
    return [sp.factor(value) for value in out]


def series_certificate(
    aa: sp.Integer, bb: sp.Integer, kkappa: sp.Expr
) -> tuple[list[sp.Expr], sp.Expr]:
    """Return C_0,C_1,C_2 and C_n/E[Y^n] for n >= 3.

    This is the theta > t certificate for a problem with shapes (aa,bb).
    The variable Y has distribution Beta(bb,aa).
    """

    AA = aa + bb
    tt = aa / AA
    qq = bb / AA
    kk = 3 * AA / (AA - 1)
    cc = kk + 1 / AA
    dd = 1 / AA

    # Polynomials are represented by ascending coefficients in y.
    xpoly = [qq, -1]
    y_one_minus_y = [0, 1, -1]
    W = poly_mul(xpoly, y_one_minus_y)

    f0 = [-qq, 1 + kkappa, -kkappa]
    f1 = [0, qq - tt - kkappa, kkappa - 1]
    f2 = [0, 0, tt]
    psi0 = [dd]
    psi1 = [kk * qq, -cc]

    g0 = poly_mul(W, poly_mul(f0, psi0))
    g1 = poly_add(
        poly_mul(W, poly_mul(f0, psi1)),
        poly_mul(W, poly_mul(f1, psi0)),
    )
    g2 = poly_add(
        poly_mul(W, poly_mul(f1, psi1)),
        poly_mul(W, poly_mul(f2, psi0)),
    )
    g3 = poly_mul(W, poly_mul(f2, psi1))
    gs = [g0, g1, g2, g3]

    # Y ~ Beta(bb,aa).
    def y_moment(order: int) -> sp.Expr:
        return sp.rf(bb, order) / sp.rf(AA, order)

    def raw_expect(poly: list[sp.Expr], shift: int = 0) -> sp.Expr:
        return sp.factor(
            sum(
                coefficient * y_moment(index + shift)
                for index, coefficient in enumerate(poly)
            )
        )

    first = []
    for nn in range(3):
        coefficient = sum(
            sp.binomial(nn - j + 5, 5) * raw_expect(gs[j], nn - j)
            for j in range(min(3, nn) + 1)
        )
        first.append(sp.factor(coefficient))

    # For generic n>=3, factor out E[Y^n]=(bb)_n/(AA)_n.
    def shifted_moment_ratio(offset: int) -> sp.Expr:
        return sp.rf(bb + n, offset) / sp.rf(AA + n, offset)

    def shifted_expect_ratio(poly: list[sp.Expr], shift: int) -> sp.Expr:
        # Every exponent index+shift is >=0 for n>=3.
        return sp.factor(
            sum(
                coefficient * shifted_moment_ratio(index + shift)
                for index, coefficient in enumerate(poly)
            )
        )

    generic = sp.Integer(0)
    for j in range(4):
        choose = sp.prod(n - j + 5 - index for index in range(5)) / sp.factorial(5)
        generic += choose * shifted_expect_ratio(gs[j], -j)

    return first, sp.factor(sp.cancel(generic))


plus_first, plus_generic = series_certificate(a, b, kappa)
minus_first, minus_generic = series_certificate(b, a, -kappa)

assert plus_first == [
    -sp.Rational(2927, 12944820),
    -sp.Rational(21079, 45306870),
    -sp.Rational(6257096, 5595398445),
]

assert minus_first == [
    -sp.Rational(2927, 12944820),
    -sp.Rational(19309, 90613740),
    -sp.Rational(2290163, 3730265630),
]

P_plus = (
    894726 * n**5
    + 5235585 * n**4
    - 77362658 * n**3
    + 302400473 * n**2
    - 158799882 * n
    + 115066224
)

P_minus = (
    2024512 * n**5
    + 45552308 * n**4
    - 182753309 * n**3
    + 407426571 * n**2
    - 272952966 * n
    + 134243928
)

expected_plus_generic = -(
    (n + 1) * (n + 2) * P_plus
) / (
    989898
    * (n + 14)
    * (n + 15)
    * (n + 16)
    * (n + 17)
    * (n + 18)
)

expected_minus_generic = -(
    (n + 1) * (n + 2) * P_minus
) / (
    1154881
    * (n + 14)
    * (n + 15)
    * (n + 16)
    * (n + 17)
    * (n + 18)
)

assert sp.factor(plus_generic - expected_plus_generic) == 0
assert sp.factor(minus_generic - expected_minus_generic) == 0

P_plus_shifted = sp.Poly(sp.expand(P_plus.subs(n, mshift + 3)), mshift)
P_minus_shifted = sp.Poly(sp.expand(P_minus.subs(n, mshift + 3)), mshift)

assert P_plus_shifted.all_coeffs() == [
    894726,
    18656475,
    65989702,
    130434161,
    494618400,
    912979872,
]

assert P_minus_shifted.all_coeffs() == [
    2024512,
    75919988,
    546080467,
    1769089662,
    2976843741,
    2229578190,
]


def beta_y_expect_rational(
    expression: sp.Expr, aa: sp.Integer, bb: sp.Integer
) -> sp.Expr:
    """Exact expectation for Y~Beta(bb,aa) in the endpoint formulas."""

    density = y ** (bb - 1) * (1 - y) ** (aa - 1) / sp.beta(bb, aa)
    integral = sp.integrate(sp.cancel(expression) * density, (y, 0, 1))
    return sp.factor(sp.expand_func(integral))


def endpoint_values(
    aa: sp.Integer, bb: sp.Integer
) -> tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]:
    """Endpoint corresponding to theta -> 1 for shapes (aa,bb)."""

    AA = aa + bb
    tt = aa / AA
    qq = bb / AA
    kk = 3 * AA / (AA - 1)
    cc = kk + 1 / AA
    dd = cc - kk

    F1 = -qq * (1 - y) ** 2
    psi1 = dd + kk * qq - cc * y
    H1_integrand = (
        (qq - y) * y * (1 - y) * F1 * psi1 / (1 - y) ** 6
    )
    H1 = beta_y_expect_rational(H1_integrand, aa, bb)
    B_scaled = sp.factor(tt * H1 / qq**2)

    risk_quadratic = (
        cc**2
        - 6 * AA * cc * tt / ((AA - 1) * (1 - y))
        + 15
        * AA**2
        * tt**2
        / ((AA - 1) * (AA - 2) * (1 - y) ** 2)
    )
    C_scaled = sp.factor(
        tt**2
        * beta_y_expect_rational(
            y**2 * risk_quadratic / (1 - y) ** 2, aa, bb
        )
    )
    ratio = sp.factor(-2 * B_scaled / C_scaled)
    return H1, B_scaled, C_scaled, ratio


right_endpoint = endpoint_values(a, b)
left_endpoint = endpoint_values(b, a)

assert right_endpoint == (
    -sp.Rational(39076, 22295),
    -sp.Rational(29307, 12740),
    sp.Rational(164411937, 4057690),
    sp.Rational(6222853, 54803979),
)

assert left_endpoint == (
    -sp.Rational(40101, 156065),
    -sp.Rational(53468, 66885),
    sp.Rational(18021716, 2028845),
    sp.Rational(2432794, 13516287),
)


# Exact C and ratio at the pivot.
D_pivot = sp.Integer(1)
risk_quadratic_pivot = (
    c**2 - 84 * c / (13 * D_pivot) + 245 / (13 * D_pivot**2)
)
C_pivot = sp.factor(beta_p_expect(phi_pivot**2) * risk_quadratic_pivot)
pivot_ratio = sp.factor(-2 * B_pivot / C_pivot)

assert C_pivot == sp.Rational(2929078580439, 492344331547432)
assert pivot_ratio == sp.Rational(3339772646756, 43936178706585)


# Ratio-free uniform bounds.
b0 = sp.Rational(2927, 12944820)
assert -plus_first[0] == b0
assert -minus_first[0] == b0
assert 0 < kappa < 1


def inverse_beta_bound(alpha: sp.Integer, beta: sp.Integer) -> sp.Expr:
    """The exact M bound for Y~Beta(alpha,beta)."""

    expression = (
        sp.Rational(16, 49)
        * y**2
        / (1 - y) ** 2
        * (c**2 + sp.Rational(245, 13) / (1 - y) ** 2)
    )
    density = y ** (alpha - 1) * (1 - y) ** (beta - 1) / sp.beta(
        alpha, beta
    )
    return sp.factor(
        sp.expand_func(sp.integrate(sp.cancel(expression) * density, (y, 0, 1)))
    )


M_plus = inverse_beta_bound(sp.Integer(8), sp.Integer(6))
M_minus = inverse_beta_bound(sp.Integer(6), sp.Integer(8))
uniform_epsilon_threshold = sp.factor(2 * b0 / M_plus)
explicit_epsilon = sp.Rational(1, 2_000_000)

# Component inverse moments, useful for a short formal proof of M_±.
assert beta_y_expect_rational(
    y**2 / (1 - y) ** 2, sp.Integer(6), sp.Integer(8)
) == sp.Rational(18, 5)
assert beta_y_expect_rational(
    y**2 / (1 - y) ** 4, sp.Integer(6), sp.Integer(8)
) == sp.Rational(468, 5)
assert beta_y_expect_rational(
    y**2 / (1 - y) ** 2, sp.Integer(8), sp.Integer(6)
) == 1
assert beta_y_expect_rational(
    y**2 / (1 - y) ** 4, sp.Integer(8), sp.Integer(6)
) == sp.Rational(39, 5)

assert M_plus == sp.Rational(1194621192, 2028845)
assert M_minus == sp.Rational(20921716, 405769)
assert M_minus < M_plus
assert uniform_epsilon_threshold == sp.Rational(
    3462641, 4508500378608
)
assert explicit_epsilon < uniform_epsilon_threshold

# Two elementary denominator inequalities used in the C bound.
svar, qvar = sp.symbols("s q", nonnegative=True)
assert sp.expand((1 - svar * y) - (1 - y)) == sp.expand(
    y * (1 - svar)
)
assert sp.expand(
    (1 - svar * y) - (1 - qvar * svar) * (1 - y)
) == sp.expand((1 - svar) * y + qvar * svar * (1 - y))


print("All exact symbolic checks passed.")
print(f"kappa = {kappa}")
print(f"c = {c}")
print(f"B(t) = {B_pivot}")
print(f"C(t) = {C_pivot}")
print(f"-2B(t)/C(t) = {pivot_ratio} = {float(pivot_ratio):.12f}")
print(
    "left endpoint ratio = "
    f"{left_endpoint[3]} = {float(left_endpoint[3]):.12f}"
)
print(
    "right endpoint ratio = "
    f"{right_endpoint[3]} = {float(right_endpoint[3]):.12f}"
)
print(f"M_plus = {M_plus}")
print(f"M_minus = {M_minus}")
print(
    "ratio-free epsilon threshold = "
    f"{uniform_epsilon_threshold} = "
    f"{float(uniform_epsilon_threshold):.12e}"
)
print(f"explicit epsilon = {explicit_epsilon}")


def optional_numerical_diagnostic() -> None:
    """Locate the apparent interior minimum; this is evidence, not proof."""

    try:
        import numpy as np
        from scipy.special import roots_jacobi
    except ImportError:
        return

    nodes, weights = roots_jacobi(500, float(b - 1), float(a - 1))
    p_nodes = (nodes + 1) / 2
    weights = weights / weights.sum()

    theta_grid = np.unique(
        np.r_[
            1 / (1 + np.exp(-np.linspace(-30, 30, 8000))),
            np.linspace(1e-7, 1 - 1e-7, 8000),
            float(t),
        ]
    )

    nu1 = 12.0
    nu2 = 16.0
    K = 3 * nu1 * nu2 / (nu1 + nu2 - 2)
    k1 = 3 / (nu1 + nu2 - 2)
    k2 = 15 / ((nu1 + nu2 - 2) * (nu1 + nu2 - 4))

    best = (float("inf"), None)
    for theta in theta_grid:
        dt = (
            theta * p_nodes / nu1
            + (1 - theta) * (1 - p_nodes) / nu2
        )
        d = nu1 * nu2 * dt
        r = nu2 * theta * p_nodes / d
        phi = r * (1 - r) * (
            float(t) - r + float(kappa) * r * (1 - r)
        )
        B_value = np.sum(
            weights
            * (r - theta)
            * phi
            * (float(c) - K / d)
        )
        C_value = np.sum(
            weights
            * phi**2
            * (
                float(c) ** 2
                - 2 * float(c) * k1 / dt
                + k2 / dt**2
            )
        )
        ratio = -2 * B_value / C_value
        if ratio < best[0]:
            best = (ratio, theta)

    print(
        "numerical diagnostic: min grid ratio "
        f"{best[0]:.12f} near theta={best[1]:.12f}"
    )


optional_numerical_diagnostic()
