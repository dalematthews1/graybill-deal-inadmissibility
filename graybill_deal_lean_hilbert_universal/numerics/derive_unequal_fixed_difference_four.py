#!/usr/bin/env python3
"""Exact symbolic certificate for the fixed-difference-four family.

This is scratch mathematics for the fixed sample-size imbalance

    (n1,n2) = (2m-1, 2m+3),  m >= 7.

It generalizes the exact one-sided coefficient calculation used for
the fixed (13,17) certificate. All calculations use SymPy exact
arithmetic. The quadratic-envelope formulas are also checked below.
"""

from __future__ import annotations

import sympy as sp


m, n, u, jshift = sp.symbols(
    "m n u j", integer=True, nonnegative=True
)
p, x = sp.symbols("p x")

a = m - 1
b = m + 1
A = 2 * m
t = sp.cancel(a / A)
q = sp.cancel(b / A)

k = sp.cancel(3 * A / (A - 1))
c = sp.cancel(k + 1 / A)
delta = sp.cancel(c - k)


def beta_moment(alpha: sp.Expr, total: sp.Expr, order: int) -> sp.Expr:
    return sp.cancel(sp.rf(alpha, order) / sp.rf(total, order))


def beta_expect_poly(
    expression: sp.Expr, alpha: sp.Expr, total: sp.Expr
) -> sp.Expr:
    poly = sp.Poly(sp.expand(expression), p)
    value = sum(
        coeff * beta_moment(alpha, total, power)
        for (power,), coeff in poly.terms()
    )
    return sp.factor(sp.cancel(value))


X = p - t
pq = p * (1 - p)
kappa_num = beta_expect_poly(X**3 * pq, a, A)
kappa_den = beta_expect_poly(X**2 * pq**2, a, A)
kappa = sp.factor(sp.cancel(kappa_num / kappa_den))

phi_pivot = pq * (-X + kappa * pq)
pivot_M1 = beta_expect_poly(X * phi_pivot, a, A)
pivot_M2 = beta_expect_poly(X**2 * phi_pivot, a, A)
pivot_B = sp.factor(sp.cancel(delta * pivot_M1))
b0 = sp.factor(-pivot_B)

# Exact quadratic kernel and common one-sided envelope.
ell = sp.factor(30 * m**2 / ((m - 1) * (2 * m - 1)))
quadratic_kernel = c**2 - 2 * k * c * x + ell * x**2
quadratic_kernel_square = (
    ell * (x - c * (m - 1) / (5 * m)) ** 2
    + c**2 * (4 * m + 1) / (5 * (2 * m - 1))
)
assert sp.factor(sp.cancel(quadratic_kernel - quadratic_kernel_square)) == 0

M_plus = sp.factor(
    q**2
    * (m + 1)
    * (m + 2)
    / ((m - 2) * (m - 3))
    * (c**2 + 60 * m**2 / ((m - 4) * (m - 5)))
)
M_minus = sp.factor(
    q**2 * (c**2 + 60 * m**2 / ((m - 2) * (m - 3)))
)
epsilon_safe = sp.factor(b0 / M_plus)
assert sp.limit(m**2 * epsilon_safe, m, sp.oo) == sp.Rational(1, 1104)

# Independent inverse-beta-moment assembly of the same envelopes.
plus_inverse_2 = (m + 1) * (m + 2) / ((m - 3) * (m - 2))
plus_inverse_4 = (
    (m + 1)
    * (m + 2)
    * (2 * m - 1)
    * (2 * m - 2)
    / ((m - 5) * (m - 4) * (m - 3) * (m - 2))
)
minus_inverse_2 = sp.Integer(1)
minus_inverse_4 = (2 * m - 1) * (2 * m - 2) / (
    (m - 3) * (m - 2)
)
assert sp.factor(
    sp.cancel(
        M_plus
        - q**2 * (c**2 * plus_inverse_2 + ell * plus_inverse_4)
    )
) == 0
assert sp.factor(
    sp.cancel(
        M_minus
        - q**2 * (c**2 * minus_inverse_2 + ell * minus_inverse_4)
    )
) == 0

M_difference_num, M_difference_den = sp.fraction(
    sp.factor(sp.cancel(M_plus - M_minus))
)
M_difference_shifted = sp.Poly(
    sp.expand(M_difference_num.subs(m, u + 7)), u
)
assert all(coefficient > 0 for coefficient in M_difference_shifted.coeffs())
assert all(
    coefficient > 0
    for coefficient in sp.Poly(
        sp.expand(sp.fraction(sp.factor(1 - kappa))[0].subs(m, u + 7)),
        u,
    ).coeffs()
)


def poly_add(left: list[sp.Expr], right: list[sp.Expr]) -> list[sp.Expr]:
    out = [sp.Integer(0)] * max(len(left), len(right))
    for index, value in enumerate(left):
        out[index] += value
    for index, value in enumerate(right):
        out[index] += value
    return [sp.factor(sp.cancel(value)) for value in out]


def poly_mul(left: list[sp.Expr], right: list[sp.Expr]) -> list[sp.Expr]:
    out = [sp.Integer(0)] * (len(left) + len(right) - 1)
    for i, left_value in enumerate(left):
        for j, right_value in enumerate(right):
            out[i + j] += left_value * right_value
    return [sp.factor(sp.cancel(value)) for value in out]


def series_certificate(
    aa: sp.Expr, bb: sp.Expr, kkappa: sp.Expr
) -> tuple[list[sp.Expr], sp.Expr]:
    """Return C0,C1,C2 and Cn/E[Y^n] for n >= 3.

    This is the theta >= aa/(aa+bb) chart.  Its transformed variable
    Y has law Beta(bb,aa).
    """

    AA = sp.expand(aa + bb)
    tt = sp.cancel(aa / AA)
    qq = sp.cancel(bb / AA)
    kk = sp.cancel(3 * AA / (AA - 1))
    cc = sp.cancel(kk + 1 / AA)
    dd = sp.cancel(1 / AA)

    # Ascending coefficients in y.
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

    def y_moment(order: int) -> sp.Expr:
        return beta_moment(bb, AA, order)

    def raw_expect(poly: list[sp.Expr], shift: int = 0) -> sp.Expr:
        return sp.factor(
            sp.cancel(
                sum(
                    coefficient * y_moment(index + shift)
                    for index, coefficient in enumerate(poly)
                )
            )
        )

    first: list[sp.Expr] = []
    for nn in range(3):
        coefficient = sum(
            sp.binomial(nn - jj + 5, 5)
            * raw_expect(gs[jj], nn - jj)
            for jj in range(min(3, nn) + 1)
        )
        first.append(sp.factor(sp.cancel(coefficient)))

    def shifted_moment_ratio(offset: int) -> sp.Expr:
        assert offset >= 0
        return sp.cancel(sp.rf(bb + n, offset) / sp.rf(AA + n, offset))

    def shifted_expect_ratio(
        poly: list[sp.Expr], shift: int
    ) -> sp.Expr:
        return sp.factor(
            sp.cancel(
                sum(
                    coefficient * shifted_moment_ratio(index + shift)
                    for index, coefficient in enumerate(poly)
                    if coefficient != 0
                )
            )
        )

    generic = sp.Integer(0)
    for jj in range(4):
        choose = (
            sp.prod(n - jj + 5 - index for index in range(5))
            / sp.factorial(5)
        )
        generic += choose * shifted_expect_ratio(gs[jj], -jj)

    return first, sp.factor(sp.cancel(generic))


plus_first, plus_generic = series_certificate(a, b, kappa)
minus_first, minus_generic = series_certificate(b, a, -kappa)


def fraction_data(expression: sp.Expr) -> tuple[sp.Expr, sp.Expr]:
    num, den = sp.fraction(sp.factor(sp.cancel(expression)))
    return sp.factor(num), sp.factor(den)


plus_num, plus_den = fraction_data(plus_generic)
minus_num, minus_den = fraction_data(minus_generic)

# Strip the known positive factor (n+1)(n+2) and the global minus sign.
plus_tail_poly = sp.factor(-plus_num / ((n + 1) * (n + 2)))
minus_tail_poly = sp.factor(-minus_num / ((n + 1) * (n + 2)))
plus_tail_core = sp.factor(plus_tail_poly / (m - 1))
minus_tail_core = sp.factor(minus_tail_poly / (m + 1))

plus_shifted = sp.Poly(
    sp.expand(plus_tail_core.subs({m: u + 7, n: jshift + 3})),
    u,
    jshift,
)
minus_shifted = sp.Poly(
    sp.expand(minus_tail_core.subs({m: u + 7, n: jshift + 3})),
    u,
    jshift,
)


def positive_first_numerator(expression: sp.Expr) -> tuple[sp.Expr, sp.Expr]:
    num, den = fraction_data(expression)
    # All six displayed first coefficients have a global minus sign.
    return sp.factor(-num), den


plus_first_data = [positive_first_numerator(value) for value in plus_first]
minus_first_data = [positive_first_numerator(value) for value in minus_first]
plus_first_shifted = [
    sp.Poly(sp.expand(num.subs(m, u + 7)), u)
    for num, _ in plus_first_data
]
minus_first_shifted = [
    sp.Poly(sp.expand(num.subs(m, u + 7)), u)
    for num, _ in minus_first_data
]

assert all(
    coefficient > 0
    for poly in plus_first_shifted + minus_first_shifted
    for coefficient in poly.coeffs()
)
assert all(coefficient > 0 for coefficient in plus_shifted.coeffs())
assert all(coefficient > 0 for coefficient in minus_shifted.coeffs())


def coefficient_sign_summary(poly: sp.Poly) -> tuple[int, int, int]:
    coeffs = poly.coeffs()
    return (
        sum(1 for coeff in coeffs if coeff > 0),
        sum(1 for coeff in coeffs if coeff == 0),
        sum(1 for coeff in coeffs if coeff < 0),
    )


if __name__ == "__main__":
    print("t =", t)
    print("q =", q)
    print("k =", k)
    print("c =", c)
    print("delta =", delta)
    print("kappa_num =", kappa_num)
    print("kappa_den =", kappa_den)
    print("kappa =", kappa)
    print("pivot_M2 =", pivot_M2)
    print("pivot_M1 =", pivot_M1)
    print("pivot_B =", pivot_B)
    print("b0 =", b0)
    print("ell =", ell)
    print("M_plus =", M_plus)
    print("M_minus =", M_minus)
    print("epsilon_safe =", epsilon_safe)
    print(
        "M_plus - M_minus shifted signs =",
        coefficient_sign_summary(M_difference_shifted),
    )
    print()

    for label, values in (
        ("plus_first", plus_first),
        ("minus_first", minus_first),
    ):
        print(label)
        for index, value in enumerate(values):
            print(f"  C{index} =", sp.factor(value))

    print()
    print("plus_generic =", plus_generic)
    print("plus_den =", plus_den)
    print("plus_tail_core =", plus_tail_core)
    print("plus_tail_core coefficients by n-power")
    plus_by_n = sp.Poly(plus_tail_core, n)
    for exponent in range(plus_by_n.degree() + 1):
        print(
            f"  n^{exponent}:",
            sp.factor(plus_by_n.coeff_monomial(n**exponent)),
        )
    print()
    print("minus_generic =", minus_generic)
    print("minus_den =", minus_den)
    print("minus_tail_core =", minus_tail_core)
    print("minus_tail_core coefficients by n-power")
    minus_by_n = sp.Poly(minus_tail_core, n)
    for exponent in range(minus_by_n.degree() + 1):
        print(
            f"  n^{exponent}:",
            sp.factor(minus_by_n.coeff_monomial(n**exponent)),
        )
    print()

    for label, shifted_values in (
        ("plus first shifted numerators", plus_first_shifted),
        ("minus first shifted numerators", minus_first_shifted),
    ):
        print(label)
        for index, poly in enumerate(shifted_values):
            print(
                f"  C{index}: signs={coefficient_sign_summary(poly)}",
                " expansion=",
                poly.as_expr(),
            )

    print("plus shifted degree =", plus_shifted.total_degree())
    print("plus shifted terms =", len(plus_shifted.terms()))
    print("plus shifted signs =", coefficient_sign_summary(plus_shifted))
    print("plus shifted negative terms =")
    for monomial, coefficient in plus_shifted.terms():
        if coefficient < 0:
            print(" ", monomial, coefficient)

    print("minus shifted degree =", minus_shifted.total_degree())
    print("minus shifted terms =", len(minus_shifted.terms()))
    print("minus shifted signs =", coefficient_sign_summary(minus_shifted))
    print("minus shifted negative terms =")
    for monomial, coefficient in minus_shifted.terms():
        if coefficient < 0:
            print(" ", monomial, coefficient)

    print("shift-base scan for tail coefficient positivity")
    for base in range(2, 8):
        plus_at_base = sp.Poly(
            sp.expand(
                plus_tail_core.subs(
                    {m: u + base, n: jshift + 3}
                )
            ),
            u,
            jshift,
        )
        minus_at_base = sp.Poly(
            sp.expand(
                minus_tail_core.subs(
                    {m: u + base, n: jshift + 3}
                )
            ),
            u,
            jshift,
        )
        print(
            f"  m >= {base}:",
            "plus",
            coefficient_sign_summary(plus_at_base),
            "minus",
            coefficient_sign_summary(minus_at_base),
        )
        if base == 6:
            print(
                "    plus negative terms at base 6:",
                [
                    (monomial, coefficient)
                    for monomial, coefficient in plus_at_base.terms()
                    if coefficient < 0
                ],
            )

    # Fixed-pair regression.
    assert sp.factor(kappa.subs(m, 7)) == sp.Rational(1045, 5439)
    assert sp.factor(c.subs(m, 7)) == sp.Rational(601, 182)
    assert sp.factor(pivot_B.subs(m, 7)) == -sp.Rational(
        2927, 12944820
    )
    assert sp.factor(M_plus.subs(m, 7)) == sp.Rational(
        1194621192, 2028845
    )
    assert sp.factor(M_minus.subs(m, 7)) == sp.Rational(
        20921716, 405769
    )
    assert sp.factor((2 * b0 / M_plus).subs(m, 7)) == sp.Rational(
        3462641, 4508500378608
    )
    expected_plus_first_m7 = [
        -sp.Rational(2927, 12944820),
        -sp.Rational(21079, 45306870),
        -sp.Rational(6257096, 5595398445),
    ]
    expected_minus_first_m7 = [
        -sp.Rational(2927, 12944820),
        -sp.Rational(19309, 90613740),
        -sp.Rational(2290163, 3730265630),
    ]
    assert [
        sp.factor(value.subs(m, 7)) for value in plus_first
    ] == expected_plus_first_m7
    assert [
        sp.factor(value.subs(m, 7)) for value in minus_first
    ] == expected_minus_first_m7
    fixed_plus_poly = (
        894726 * n**5
        + 5235585 * n**4
        - 77362658 * n**3
        + 302400473 * n**2
        - 158799882 * n
        + 115066224
    )
    fixed_minus_poly = (
        2024512 * n**5
        + 45552308 * n**4
        - 182753309 * n**3
        + 407426571 * n**2
        - 272952966 * n
        + 134243928
    )
    expected_plus_generic_m7 = -(
        (n + 1) * (n + 2) * fixed_plus_poly
    ) / (
        989898
        * (n + 14)
        * (n + 15)
        * (n + 16)
        * (n + 17)
        * (n + 18)
    )
    expected_minus_generic_m7 = -(
        (n + 1) * (n + 2) * fixed_minus_poly
    ) / (
        1154881
        * (n + 14)
        * (n + 15)
        * (n + 16)
        * (n + 17)
        * (n + 18)
    )
    assert sp.factor(
        plus_generic.subs(m, 7) - expected_plus_generic_m7
    ) == 0
    assert sp.factor(
        minus_generic.subs(m, 7) - expected_minus_generic_m7
    ) == 0
