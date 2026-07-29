#!/usr/bin/env python3
"""Exact and high-precision reconnaissance for a fixed-difference-four family.

The family is

    (n1, n2) = (2*m - 1, 2*m + 3),   m >= 7,

so the residual chi-square shapes are

    a = m - 1,  b = m + 1.

For every requested ``m`` this script:

* computes the pivot-orthogonalized ``kappa``, ``c``, pivot ``B`` and ``b0``
  exactly;
* computes the first three coefficients in both one-sided first-order series;
* computes the exact generic coefficient formula for n >= 3 and checks the
  shifted-numerator sign certificate;
* computes exact pivot and endpoint risk ratios; and
* uses Gauss-Jacobi quadrature on endpoint-aware theta grids, followed by
  bounded refinement and an mpmath evaluation, to diagnose the minimum of
  ``-2 B(theta) / C(theta)``.

The numerical part is reconnaissance, not a proof.  The series sign checks are
exact rational calculations.  Use ``--show-tail-formulas`` to print the full
per-m generic rational functions.

The script requires sympy and mpmath.  NumPy and SciPy are required for the
numerical scan.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from typing import Callable

import mpmath as mp
import sympy as sp

try:
    import numpy as np
    from scipy.optimize import minimize_scalar
    from scipy.special import roots_jacobi
except ImportError as exc:  # pragma: no cover - dependency failure is explicit
    raise SystemExit(
        "The numerical scan requires NumPy and SciPy in addition to sympy."
    ) from exc


p, y = sp.symbols("p y")
n = sp.symbols("n", integer=True, nonnegative=True)
z = sp.symbols("z", integer=True, nonnegative=True)
m_family = sp.symbols("m", integer=True, positive=True)


# Closed family formulas, independently checked from beta moments below.
KAPPA_FAMILY = sp.factor(
    (2 * m_family + 5)
    * (5 * m_family**2 - 4 * m_family + 3)
    / (
        m_family**2
        * (m_family**3 + 2 * m_family**2 - m_family + 10)
    )
)
C_FAMILY = sp.factor(
    (12 * m_family**2 + 2 * m_family - 1)
    / (2 * m_family * (2 * m_family - 1))
)
B_PIVOT_FAMILY = sp.factor(
    -(
        (m_family - 1)
        * (
            m_family**5
            + 3 * m_family**4
            - 10 * m_family**2
            - 17 * m_family
            + 15
        )
    )
    / (
        16
        * m_family**3
        * (2 * m_family + 1)
        * (2 * m_family + 3)
        * (m_family**3 + 2 * m_family**2 - m_family + 10)
    )
)


def beta_p_moment(order: int, aa: sp.Integer, bb: sp.Integer) -> sp.Expr:
    """Return E[P^order] for P ~ Beta(aa,bb)."""

    return sp.rf(aa, order) / sp.rf(aa + bb, order)


def beta_p_expect(
    polynomial: sp.Expr, aa: sp.Integer, bb: sp.Integer
) -> sp.Expr:
    """Take an exact beta expectation of a polynomial in p."""

    pp = sp.Poly(sp.expand(polynomial), p)
    return sp.factor(
        sum(
            coefficient * beta_p_moment(power, aa, bb)
            for (power,), coefficient in pp.terms()
        )
    )


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
    aa: sp.Integer, bb: sp.Integer, kappa: sp.Expr
) -> tuple[list[sp.Expr], sp.Expr]:
    """Return C_0,C_1,C_2 and C_n/E[Y^n] for n >= 3.

    This is the theta > pivot chart for shapes (aa,bb).  Here
    Y ~ Beta(bb,aa).  Interchanging aa and bb and negating kappa gives the
    opposite chart.
    """

    AA = aa + bb
    tt = aa / AA
    qq = bb / AA
    kk = 3 * AA / (AA - 1)
    cc = kk + 1 / AA
    dd = 1 / AA

    # Ascending polynomial coefficient lists in y.
    xpoly = [qq, -1]
    y_one_minus_y = [0, 1, -1]
    W = poly_mul(xpoly, y_one_minus_y)

    f0 = [-qq, 1 + kappa, -kappa]
    f1 = [0, qq - tt - kappa, kappa - 1]
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

    # Factor E[Y^n]=(bb)_n/(AA)_n out of the generic n >= 3 term.
    def shifted_moment_ratio(offset: int) -> sp.Expr:
        return sp.rf(bb + n, offset) / sp.rf(AA + n, offset)

    def shifted_expect_ratio(poly: list[sp.Expr], shift: int) -> sp.Expr:
        return sp.factor(
            sum(
                coefficient * shifted_moment_ratio(index + shift)
                for index, coefficient in enumerate(poly)
            )
        )

    generic = sp.Integer(0)
    for j in range(4):
        choose = (
            sp.prod(n - j + 5 - index for index in range(5))
            / sp.factorial(5)
        )
        generic += choose * shifted_expect_ratio(gs[j], -j)

    return first, sp.factor(sp.cancel(generic))


@dataclass(frozen=True)
class TailSignCertificate:
    formula: sp.Expr
    shifted_numerator_coefficients: tuple[sp.Expr, ...]
    shifted_denominator_coefficients: tuple[sp.Expr, ...]
    valid: bool


def tail_sign_certificate(generic: sp.Expr) -> TailSignCertificate:
    """Check negativity for n>=3 by shifting n=z+3.

    The returned certificate is sufficient when every shifted numerator
    coefficient is strictly negative and every shifted denominator coefficient
    is strictly positive.
    """

    numerator, denominator = sp.fraction(sp.cancel(generic))
    numerator = sp.factor(numerator)
    denominator = sp.factor(denominator)
    if denominator.subs(n, 3) < 0:
        numerator = -numerator
        denominator = -denominator

    shifted_numerator = sp.Poly(
        sp.expand(numerator.subs(n, z + 3)), z
    ).all_coeffs()
    shifted_denominator = sp.Poly(
        sp.expand(denominator.subs(n, z + 3)), z
    ).all_coeffs()
    valid = all(value < 0 for value in shifted_numerator) and all(
        value > 0 for value in shifted_denominator
    )
    return TailSignCertificate(
        formula=sp.factor(numerator / denominator),
        shifted_numerator_coefficients=tuple(shifted_numerator),
        shifted_denominator_coefficients=tuple(shifted_denominator),
        valid=valid,
    )


def beta_y_mixed_moment(
    y_power: int, inverse_one_minus_power: int, aa: int, bb: int
) -> sp.Expr:
    """E[Y^j/(1-Y)^d] for Y~Beta(bb,aa), exactly."""

    if aa <= inverse_one_minus_power:
        raise ValueError("requested inverse beta moment does not exist")
    AA = aa + bb
    j = y_power
    d = inverse_one_minus_power
    return sp.factor(
        sp.factorial(bb + j - 1)
        * sp.factorial(aa - d - 1)
        * sp.factorial(AA - 1)
        / (
            sp.factorial(bb - 1)
            * sp.factorial(aa - 1)
            * sp.factorial(AA + j - d - 1)
        )
    )


def beta_y_expect_over_power(
    numerator: sp.Expr, inverse_one_minus_power: int, aa: int, bb: int
) -> sp.Expr:
    polynomial = sp.Poly(sp.expand(numerator), y)
    return sp.factor(
        sum(
            coefficient
            * beta_y_mixed_moment(
                power, inverse_one_minus_power, aa, bb
            )
            for (power,), coefficient in polynomial.terms()
        )
    )


def endpoint_values(
    aa: sp.Integer, bb: sp.Integer
) -> tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]:
    """Return H, scaled B, scaled C and -2B/C at theta -> 1."""

    AA = aa + bb
    tt = aa / AA
    qq = bb / AA
    kk = 3 * AA / (AA - 1)
    cc = kk + 1 / AA
    dd = 1 / AA

    psi1 = dd + kk * qq - cc * y
    H1 = beta_y_expect_over_power(
        -qq * (qq - y) * y * psi1, 3, int(aa), int(bb)
    )
    B_scaled = sp.factor(tt * H1 / qq**2)

    moment2 = beta_y_mixed_moment(2, 2, int(aa), int(bb))
    moment3 = beta_y_mixed_moment(2, 3, int(aa), int(bb))
    moment4 = beta_y_mixed_moment(2, 4, int(aa), int(bb))
    C_scaled = sp.factor(
        tt**2
        * (
            cc**2 * moment2
            - 6 * AA * cc * tt / (AA - 1) * moment3
            + 15
            * AA**2
            * tt**2
            / ((AA - 1) * (AA - 2))
            * moment4
        )
    )
    ratio = sp.factor(-2 * B_scaled / C_scaled)
    return H1, B_scaled, C_scaled, ratio


@dataclass(frozen=True)
class ExactCase:
    m: int
    a: sp.Integer
    b: sp.Integer
    pivot: sp.Expr
    kappa: sp.Expr
    c: sp.Expr
    B_pivot: sp.Expr
    b0: sp.Expr
    C_pivot: sp.Expr
    pivot_ratio: sp.Expr
    plus_first: tuple[sp.Expr, ...]
    minus_first: tuple[sp.Expr, ...]
    plus_tail: TailSignCertificate
    minus_tail: TailSignCertificate
    left_endpoint: tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]
    right_endpoint: tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]


def exact_case(m_value: int) -> ExactCase:
    if m_value < 7:
        raise ValueError("the fixed-difference-four scan requires m >= 7")

    mm = sp.Integer(m_value)
    aa = mm - 1
    bb = mm + 1
    AA = aa + bb
    pivot = aa / AA
    X = p - pivot
    pq = p * (1 - p)

    kappa_num = beta_p_expect(X**3 * pq, aa, bb)
    kappa_den = beta_p_expect(X**2 * pq**2, aa, bb)
    kappa = sp.factor(kappa_num / kappa_den)
    c = sp.factor(3 * AA / (AA - 1) + 1 / AA)
    phi_pivot = pq * (-X + kappa * pq)
    B_pivot = sp.factor(beta_p_expect(X * phi_pivot, aa, bb) / AA)
    b0 = -B_pivot

    assert kappa == KAPPA_FAMILY.subs(m_family, mm)
    assert c == C_FAMILY.subs(m_family, mm)
    assert B_pivot == B_PIVOT_FAMILY.subs(m_family, mm)
    assert b0 > 0

    risk_quadratic_pivot = sp.factor(
        c**2
        - 6 * AA * c / (AA - 1)
        + 15 * AA**2 / ((AA - 1) * (AA - 2))
    )
    C_pivot = sp.factor(
        beta_p_expect(phi_pivot**2, aa, bb) * risk_quadratic_pivot
    )
    pivot_ratio = sp.factor(-2 * B_pivot / C_pivot)
    assert C_pivot > 0

    plus_first, plus_generic = series_certificate(aa, bb, kappa)
    minus_first, minus_generic = series_certificate(bb, aa, -kappa)
    plus_tail = tail_sign_certificate(plus_generic)
    minus_tail = tail_sign_certificate(minus_generic)

    # The constant coefficient is the pivot value in both charts.
    assert plus_first[0] == B_pivot
    assert minus_first[0] == B_pivot

    right_endpoint = endpoint_values(aa, bb)
    left_endpoint = endpoint_values(bb, aa)
    return ExactCase(
        m=m_value,
        a=aa,
        b=bb,
        pivot=pivot,
        kappa=kappa,
        c=c,
        B_pivot=B_pivot,
        b0=b0,
        C_pivot=C_pivot,
        pivot_ratio=pivot_ratio,
        plus_first=tuple(plus_first),
        minus_first=tuple(minus_first),
        plus_tail=plus_tail,
        minus_tail=minus_tail,
        left_endpoint=left_endpoint,
        right_endpoint=right_endpoint,
    )


class NumericalRisk:
    """Gauss-Jacobi evaluator for B(theta), C(theta), and their ratio."""

    def __init__(self, case: ExactCase, nodes: int):
        self.case = case
        aa = int(case.a)
        bb = int(case.b)
        jacobi_nodes, weights = roots_jacobi(nodes, bb - 1, aa - 1)
        self.p_nodes = (jacobi_nodes + 1.0) / 2.0
        self.weights = weights / weights.sum()
        self.nu1 = float(2 * aa)
        self.nu2 = float(2 * bb)
        self.pivot = float(case.pivot)
        self.kappa = float(case.kappa)
        self.c = float(case.c)
        self.K = (
            3.0
            * self.nu1
            * self.nu2
            / (self.nu1 + self.nu2 - 2.0)
        )
        self.k1 = 3.0 / (self.nu1 + self.nu2 - 2.0)
        self.k2 = 15.0 / (
            (self.nu1 + self.nu2 - 2.0)
            * (self.nu1 + self.nu2 - 4.0)
        )

    def BC(self, theta: float) -> tuple[float, float]:
        pp = self.p_nodes
        dt = (
            theta * pp / self.nu1
            + (1.0 - theta) * (1.0 - pp) / self.nu2
        )
        d = self.nu1 * self.nu2 * dt
        r = self.nu2 * theta * pp / d
        phi = r * (1.0 - r) * (
            self.pivot - r + self.kappa * r * (1.0 - r)
        )
        B_value = np.sum(
            self.weights
            * (r - theta)
            * phi
            * (self.c - self.K / d)
        )
        C_value = np.sum(
            self.weights
            * phi**2
            * (
                self.c**2
                - 2.0 * self.c * self.k1 / dt
                + self.k2 / dt**2
            )
        )
        return float(B_value), float(C_value)

    def ratio(self, theta: float) -> float:
        B_value, C_value = self.BC(theta)
        if not np.isfinite(B_value) or not np.isfinite(C_value):
            return float("inf")
        if C_value <= 0.0:
            return float("inf")
        return -2.0 * B_value / C_value


@dataclass(frozen=True)
class NumericalDiagnostic:
    theta: float
    B: float
    C: float
    ratio_double: float
    ratio_high_precision: mp.mpf
    maximum_grid_B: float
    minimum_grid_C: float
    endpoint_won: bool


def theta_grid(size: int, pivot: float) -> np.ndarray:
    """A linear/logit union, with exact pivot, away from roundoff endpoints."""

    linear = np.linspace(1.0e-8, 1.0 - 1.0e-8, size)
    logit_x = np.linspace(-18.0, 18.0, size)
    logistic = 1.0 / (1.0 + np.exp(-logit_x))
    return np.unique(np.r_[linear, logistic, pivot])


def high_precision_BC(
    case: ExactCase, theta: float, dps: int
) -> tuple[mp.mpf, mp.mpf]:
    """Evaluate B and C by independent adaptive quadrature."""

    with mp.workdps(dps):
        aa = int(case.a)
        bb = int(case.b)
        AA = aa + bb
        nu1 = mp.mpf(2 * aa)
        nu2 = mp.mpf(2 * bb)
        theta_mp = mp.mpf(repr(theta))
        pivot = mp.mpf(aa) / AA
        kappa = mp.mpf(str(sp.N(case.kappa, dps + 10)))
        c = mp.mpf(str(sp.N(case.c, dps + 10)))
        K = 3 * nu1 * nu2 / (nu1 + nu2 - 2)
        k1 = 3 / (nu1 + nu2 - 2)
        k2 = 15 / ((nu1 + nu2 - 2) * (nu1 + nu2 - 4))
        normalizer = mp.beta(aa, bb)

        def pair(pp: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
            dt = (
                theta_mp * pp / nu1
                + (1 - theta_mp) * (1 - pp) / nu2
            )
            d = nu1 * nu2 * dt
            r = nu2 * theta_mp * pp / d
            phi = r * (1 - r) * (
                pivot - r + kappa * r * (1 - r)
            )
            density = pp ** (aa - 1) * (1 - pp) ** (bb - 1) / normalizer
            B_integrand = (
                density * (r - theta_mp) * phi * (c - K / d)
            )
            C_integrand = density * phi**2 * (
                c**2 - 2 * c * k1 / dt + k2 / dt**2
            )
            return B_integrand, C_integrand

        B_value = mp.quad(lambda pp: pair(pp)[0], [0, pivot, 1])
        C_value = mp.quad(lambda pp: pair(pp)[1], [0, pivot, 1])
        return +B_value, +C_value


def numerical_diagnostic(
    case: ExactCase, nodes: int, grid_size: int, dps: int
) -> NumericalDiagnostic:
    evaluator = NumericalRisk(case, nodes)
    grid = theta_grid(grid_size, float(case.pivot))
    B_values = np.empty(grid.size)
    C_values = np.empty(grid.size)
    ratios = np.empty(grid.size)
    for index, theta in enumerate(grid):
        B_values[index], C_values[index] = evaluator.BC(float(theta))
        ratios[index] = (
            -2.0 * B_values[index] / C_values[index]
            if C_values[index] > 0.0
            else float("inf")
        )

    # Refine the best few local grid minima.  This catches separate basins
    # without turning the reconnaissance into a large global optimization.
    local_indices = [
        index
        for index in range(1, grid.size - 1)
        if ratios[index] <= ratios[index - 1]
        and ratios[index] <= ratios[index + 1]
    ]
    local_indices.sort(key=lambda index: ratios[index])
    candidates: list[tuple[float, float]] = [
        (float(ratios[index]), float(grid[index]))
        for index in np.argsort(ratios)[:5]
    ]
    for index in local_indices[:8]:
        result = minimize_scalar(
            evaluator.ratio,
            bounds=(float(grid[index - 1]), float(grid[index + 1])),
            method="bounded",
            options={"xatol": 1.0e-14, "maxiter": 200},
        )
        candidates.append((float(result.fun), float(result.x)))

    left_ratio = float(case.left_endpoint[3])
    right_ratio = float(case.right_endpoint[3])
    candidates.extend([(left_ratio, 0.0), (right_ratio, 1.0)])
    ratio_double, theta = min(candidates)
    endpoint_won = theta in (0.0, 1.0)

    if endpoint_won:
        if theta == 0.0:
            B_value = float(case.left_endpoint[1])
            C_value = float(case.left_endpoint[2])
            ratio_high = mp.mpf(str(sp.N(case.left_endpoint[3], dps)))
        else:
            B_value = float(case.right_endpoint[1])
            C_value = float(case.right_endpoint[2])
            ratio_high = mp.mpf(str(sp.N(case.right_endpoint[3], dps)))
    else:
        B_value, C_value = evaluator.BC(theta)
        B_high, C_high = high_precision_BC(case, theta, dps)
        ratio_high = -2 * B_high / C_high

    return NumericalDiagnostic(
        theta=theta,
        B=B_value,
        C=C_value,
        ratio_double=ratio_double,
        ratio_high_precision=ratio_high,
        maximum_grid_B=float(np.max(B_values)),
        minimum_grid_C=float(np.min(C_values)),
        endpoint_won=endpoint_won,
    )


def exact_sign_status(case: ExactCase) -> tuple[bool, bool, bool]:
    plus_head = all(value < 0 for value in case.plus_first)
    minus_head = all(value < 0 for value in case.minus_first)
    tails = case.plus_tail.valid and case.minus_tail.valid
    return plus_head, minus_head, tails


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--m-min", type=int, default=7)
    parser.add_argument("--m-max", type=int, default=20)
    parser.add_argument(
        "--nodes",
        type=int,
        default=320,
        help="Gauss-Jacobi nodes per beta integral (default: 320)",
    )
    parser.add_argument(
        "--grid-size",
        type=int,
        default=3000,
        help="points in each of the linear and logit grids (default: 3000)",
    )
    parser.add_argument(
        "--dps",
        type=int,
        default=80,
        help="mpmath digits for the independent minimum check (default: 80)",
    )
    parser.add_argument(
        "--show-tail-formulas",
        action="store_true",
        help="print the exact generic plus/minus formulas for n>=3",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.m_min < 7 or args.m_max < args.m_min:
        raise SystemExit("require 7 <= m-min <= m-max")

    print("Fixed-difference-four family:")
    print("  (n1,n2)=(2m-1,2m+3), a=m-1, b=m+1")
    print(f"  kappa(m) = {KAPPA_FAMILY}")
    print(f"  c(m) = {C_FAMILY}")
    print(f"  B_pivot(m) = {B_PIVOT_FAMILY}")
    print(
        "  numerical settings: "
        f"nodes={args.nodes}, grid={2 * args.grid_size}+pivot, "
        f"high-precision dps={args.dps}"
    )

    failures: list[str] = []
    numerical_rows: list[tuple[ExactCase, NumericalDiagnostic]] = []
    for m_value in range(args.m_min, args.m_max + 1):
        case = exact_case(m_value)
        plus_head, minus_head, tails = exact_sign_status(case)
        if not plus_head:
            failures.append(f"m={m_value}: plus head is not all negative")
        if not minus_head:
            failures.append(f"m={m_value}: minus head is not all negative")
        if not case.plus_tail.valid:
            failures.append(
                f"m={m_value}: plus shifted-tail coefficient test failed"
            )
        if not case.minus_tail.valid:
            failures.append(
                f"m={m_value}: minus shifted-tail coefficient test failed"
            )

        diagnostic = numerical_diagnostic(
            case, args.nodes, args.grid_size, args.dps
        )
        numerical_rows.append((case, diagnostic))
        if diagnostic.ratio_high_precision <= 0:
            failures.append(f"m={m_value}: nonpositive numerical min ratio")
        if diagnostic.minimum_grid_C <= 0:
            failures.append(f"m={m_value}: nonpositive C on numerical grid")

        pair = (2 * m_value - 1, 2 * m_value + 3)
        print()
        print(f"m={m_value:2d}, pair={pair}, shapes=({case.a},{case.b})")
        print(f"  kappa={case.kappa}, c={case.c}, b0={case.b0}")
        print(f"  plus first  = {list(case.plus_first)}")
        print(f"  minus first = {list(case.minus_first)}")
        print(
            "  exact coefficient signs: "
            f"plus-head={plus_head}, minus-head={minus_head}, "
            f"both-tails={tails}"
        )
        print(
            "  exact ratios: "
            f"left={float(case.left_endpoint[3]):.12f}, "
            f"pivot={float(case.pivot_ratio):.12f}, "
            f"right={float(case.right_endpoint[3]):.12f}"
        )
        location = (
            "endpoint"
            if diagnostic.endpoint_won
            else f"theta={diagnostic.theta:.12f}"
        )
        print(
            "  numerical min -2B/C: "
            f"{mp.nstr(diagnostic.ratio_high_precision, 18)} "
            f"at {location} "
            f"(double={diagnostic.ratio_double:.15f})"
        )
        print(
            "  numerical grid checks: "
            f"max B={diagnostic.maximum_grid_B:.3e}, "
            f"min C={diagnostic.minimum_grid_C:.3e}"
        )
        if args.show_tail_formulas:
            print(f"  plus generic n>=3 = {case.plus_tail.formula}")
            print(f"  minus generic n>=3 = {case.minus_tail.formula}")
            print(
                "  plus shifted numerator coefficients = "
                f"{list(case.plus_tail.shifted_numerator_coefficients)}"
            )
            print(
                "  minus shifted numerator coefficients = "
                f"{list(case.minus_tail.shifted_numerator_coefficients)}"
            )

    best_case, best_diagnostic = max(
        numerical_rows,
        key=lambda item: item[1].ratio_high_precision,
    )
    weakest_case, weakest_diagnostic = min(
        numerical_rows,
        key=lambda item: item[1].ratio_high_precision,
    )
    print()
    print("Scan summary")
    print(
        "  strongest numerical margin: "
        f"m={best_case.m}, pair={(2 * best_case.m - 1, 2 * best_case.m + 3)}, "
        f"min ratio={mp.nstr(best_diagnostic.ratio_high_precision, 18)}"
    )
    print(
        "  weakest numerical margin: "
        f"m={weakest_case.m}, "
        f"pair={(2 * weakest_case.m - 1, 2 * weakest_case.m + 3)}, "
        f"min ratio={mp.nstr(weakest_diagnostic.ratio_high_precision, 18)}"
    )
    if failures:
        print("  FAILURES:")
        for failure in failures:
            print(f"    - {failure}")
        raise SystemExit(1)
    print(
        "  no failure on the scanned range: all exact head/tail sign tests "
        "passed and every numerical minimum was positive"
    )


if __name__ == "__main__":
    main()
