#!/usr/bin/env python3
"""Real and half-integer audit of the fixed-difference-four certificate.

The completed theorem is parameterized by an integer ``m`` and covers the
odd sample-size pairs ``(2m-1,2m+3)``.  The full diagonal ``(n,n+4)`` uses
the same formulas with the real parameter ``m=(n+1)/2``.  This script checks
the exact head and tail sign certificates for real ``m``, evaluates the
quadratic envelopes, scans representative Beta-law risks, and investigates
how far the current certificate may extend below ``m=7``.

The exact polynomial checks are proof reconnaissance.  The quadrature and
dense floating-point scans are diagnostics rather than proofs.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import numpy as np
import sympy as sp
from scipy.optimize import brentq
from scipy.special import roots_jacobi


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "fd4derive", HERE / "derive_unequal_fixed_difference_four.py"
)
assert SPEC is not None and SPEC.loader is not None
D = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(D)

m, n, u, v = D.m, D.n, D.u, D.jshift


def real_roots(poly: sp.Expr, variable: sp.Symbol) -> list[float]:
    roots = sp.nroots(sp.Poly(poly, variable), n=30, maxsteps=300)
    return sorted(
        float(sp.re(root))
        for root in roots
        if abs(float(sp.im(root))) < 1e-18
    )


def last_root_below(
    poly: sp.Expr, variable: sp.Symbol, ceiling: float = 7.0
) -> float | None:
    roots = [r for r in real_roots(poly, variable) if r < ceiling + 1e-12]
    return max(roots) if roots else None


HEAD_LABELS = (
    "zero",
    "plus-one",
    "plus-two",
    "minus-zero",
    "minus-one",
    "minus-two",
)
HEAD = tuple(D.plus_first) + tuple(D.minus_first)


def coefficient_in_v(poly: sp.Poly, exponent: int) -> sp.Expr:
    return sp.Poly(poly.as_expr(), v).coeff_monomial(v**exponent)


PLUS_V_COEFFS = tuple(
    coefficient_in_v(D.plus_shifted, exponent) for exponent in range(6)
)
MINUS_V_COEFFS = tuple(
    coefficient_in_v(D.minus_shifted, exponent) for exponent in range(6)
)


def shifted_tail_coefficients_at(
    shifted: sp.Poly, m_value: sp.Rational | float
) -> list[float]:
    uu = sp.Rational(m_value) - 7 if isinstance(m_value, sp.Rational) else m_value - 7
    pv = sp.Poly(sp.expand(shifted.as_expr().subs(u, uu)), v)
    return [float(value) for value in pv.all_coeffs()]


def basic_values(mm: sp.Expr) -> dict[str, float]:
    values = {
        "kappa": D.kappa,
        "b0": D.b0,
        "Mplus": D.M_plus,
        "Mminus": D.M_minus,
        "epsilon": D.epsilon_safe,
        "Mdiff": D.M_plus - D.M_minus,
    }
    return {key: float(sp.N(value.subs(m, mm), 25)) for key, value in values.items()}


def numerical_BC_scan(
    m_value: float, nodes: int = 160, grid_points: int = 801
) -> tuple[float, float, float, float]:
    """Return max B, min C, min(-2B/C), and its theta on an interior grid."""

    aa = m_value - 1.0
    bb = m_value + 1.0
    AA = 2.0 * m_value
    pivot = aa / AA
    kappa = float(D.kappa.subs(m, m_value))
    c = float(D.c.subs(m, m_value))
    jacobi_nodes, weights = roots_jacobi(nodes, bb - 1.0, aa - 1.0)
    pp = (jacobi_nodes + 1.0) / 2.0
    weights = weights / weights.sum()
    nu1 = 2.0 * aa
    nu2 = 2.0 * bb
    K = 3.0 * nu1 * nu2 / (nu1 + nu2 - 2.0)
    k1 = 3.0 / (nu1 + nu2 - 2.0)
    k2 = 15.0 / ((nu1 + nu2 - 2.0) * (nu1 + nu2 - 4.0))

    near = np.geomspace(1e-9, 1e-2, 90)
    linear = np.linspace(0.01, 0.99, grid_points)
    theta_grid = np.unique(
        np.concatenate((near, linear, 1.0 - near, np.array([pivot])))
    )
    B_values = []
    C_values = []
    ratios = []
    for theta in theta_grid:
        dt = theta * pp / nu1 + (1.0 - theta) * (1.0 - pp) / nu2
        denom = nu1 * nu2 * dt
        r = nu2 * theta * pp / denom
        phi = r * (1.0 - r) * (
            pivot - r + kappa * r * (1.0 - r)
        )
        B = float(
            np.sum(weights * (r - theta) * phi * (c - K / denom))
        )
        C = float(
            np.sum(
                weights
                * phi**2
                * (c**2 - 2.0 * c * k1 / dt + k2 / dt**2)
            )
        )
        B_values.append(B)
        C_values.append(C)
        ratios.append(-2.0 * B / C)
    argmin = int(np.argmin(ratios))
    return (
        max(B_values),
        min(C_values),
        ratios[argmin],
        float(theta_grid[argmin]),
    )


print("HEAD NUMERATOR ROOT THRESHOLDS")
for label, coefficient in zip(HEAD_LABELS, HEAD):
    numerator, denominator = sp.fraction(sp.factor(coefficient))
    positive_numerator = sp.factor(-numerator)
    print(
        label,
        "last root < 7 =",
        last_root_below(positive_numerator, m),
        "denominator@7 =",
        sp.sign(denominator.subs(m, 7)),
    )

print("\nSHIFTED TAIL CERTIFICATE ROOT THRESHOLDS")
for chart, coefficients in (("plus", PLUS_V_COEFFS), ("minus", MINUS_V_COEFFS)):
    roots = []
    for exponent, coefficient in enumerate(coefficients):
        root_u = last_root_below(coefficient, u, ceiling=0.0)
        root_m = None if root_u is None else root_u + 7.0
        roots.append(root_m)
        print(chart, f"v^{exponent}", "last m-root < 7 =", root_m)
    finite_roots = [root for root in roots if root is not None]
    print(chart, "sufficient all-v-coeff threshold =", max(finite_roots))

print("\nOTHER ALGEBRAIC THRESHOLDS")
threshold_exprs = {
    "b0 numerator": sp.factor(sp.fraction(sp.cancel(D.b0))[0]),
    "1-kappa numerator": sp.factor(
        sp.fraction(sp.factor(sp.cancel(1 - D.kappa)))[0]
    ),
    "Mplus-Mminus numerator": sp.factor(
        sp.fraction(sp.factor(sp.cancel(D.M_plus - D.M_minus)))[0]
    ),
    "plus-tail n-leading": sp.Poly(D.plus_tail_core, n).LC(),
    "minus-tail n-leading": sp.Poly(D.minus_tail_core, n).LC(),
}
for label, expression in threshold_exprs.items():
    print(label, "last root < 7 =", last_root_below(expression, m))

print("\nACTUAL TAIL POLYNOMIAL SCAN (integer n=3,...,200000)")
plus_tail_fn = sp.lambdify((m, n), D.plus_tail_core, "numpy")
minus_tail_fn = sp.lambdify((m, n), D.minus_tail_core, "numpy")
n_grid = np.arange(3.0, 200001.0)
for mm in (4.5, 5.0, 5.5, 5.75, 6.0, 6.1, 6.17856449, 6.25, 7.0):
    plus_values = plus_tail_fn(mm, n_grid)
    minus_values = minus_tail_fn(mm, n_grid)
    plus_arg = int(n_grid[int(np.argmin(plus_values))])
    minus_arg = int(n_grid[int(np.argmin(minus_values))])
    print(
        f"m={mm:.9f}",
        f"plusMin={float(np.min(plus_values)):.8g}@n={plus_arg}",
        f"minusMin={float(np.min(minus_values)):.8g}@n={minus_arg}",
    )

m_scan = np.linspace(4.5, 7.0, 501)
last_crossings = []
for nn in range(3, 1001):
    values = plus_tail_fn(m_scan, float(nn))
    for index in np.flatnonzero((values[:-1] <= 0.0) & (values[1:] > 0.0)):
        root = brentq(
            lambda mm: float(plus_tail_fn(mm, float(nn))),
            float(m_scan[index]),
            float(m_scan[index + 1]),
        )
        last_crossings.append((root, nn))
if last_crossings:
    print(
        "plus actual-tail largest sampled crossing =",
        max(last_crossings),
        "(searched n=3,...,1000)",
    )

print("\nHALF-INTEGER EXACT/SYMBOLIC AUDIT")
for twice_m in range(15, 32, 2):
    mm = sp.Rational(twice_m, 2)
    head_negative = all(sp.factor(value.subs(m, mm)) < 0 for value in HEAD)
    plus_coeffs = shifted_tail_coefficients_at(D.plus_shifted, mm)
    minus_coeffs = shifted_tail_coefficients_at(D.minus_shifted, mm)
    vals = basic_values(mm)
    risk_endgame = -vals["b0"] ** 2 / vals["Mplus"]
    print(
        f"m={float(mm):4.1f} pair=({twice_m-1},{twice_m+3})",
        f"head={head_negative}",
        f"tail-v-coeffs={min(plus_coeffs)>0 and min(minus_coeffs)>0}",
        f"kappa={vals['kappa']:.7f}",
        f"b0={vals['b0']:.8g}",
        f"M-/M+={vals['Mminus']/vals['Mplus']:.7f}",
        f"eps={vals['epsilon']:.8g}",
        f"riskEnd={risk_endgame:.8g}",
    )

print("\nNUMERICAL B/C AUDIT (HALF-INTEGERS AND REAL OFF-GRID)")
for mm in (
    5.25, 5.4, 5.40380554, 5.41, 5.5, 6.0, 6.25, 6.5, 6.75,
    6.9, 7.0, 7.1, 7.5, 8.5, 10.25, 15.5, 30.3,
):
    max_B, min_C, min_ratio, theta = numerical_BC_scan(mm)
    head_ok = all(float(value.subs(m, mm)) < 0.0 for value in HEAD)
    plus_ok = min(shifted_tail_coefficients_at(D.plus_shifted, mm)) > 0.0
    minus_ok = min(shifted_tail_coefficients_at(D.minus_shifted, mm)) > 0.0
    vals = basic_values(mm)
    envelope_ok = (
        vals["b0"] > 0.0
        and vals["Mplus"] > 0.0
        and vals["Mminus"] > 0.0
        and vals["Mdiff"] > 0.0
        and vals["epsilon"] > 0.0
    )
    print(
        f"m={mm:5.2f}",
        f"head={head_ok}",
        f"tailCert=({plus_ok},{minus_ok})",
        f"env={envelope_ok}",
        f"maxB={max_B:.4e}",
        f"minC={min_C:.4e}",
        f"minRatio={min_ratio:.7g}@{theta:.5f}",
    )

print("\nDENSE REAL GRID m in [7,100]")
grid = np.concatenate(
    (np.linspace(7.0, 10.0, 301), np.geomspace(10.0, 100.0, 301))
)
failures = []
minimum_data = {
    "head margin": (float("inf"), None),
    "plus tail shifted coefficient": (float("inf"), None),
    "minus tail shifted coefficient": (float("inf"), None),
    "b0": (float("inf"), None),
    "Mplus-Mminus": (float("inf"), None),
}
for mm in grid:
    head_margin = min(-float(value.subs(m, mm)) for value in HEAD)
    plus_margin = min(shifted_tail_coefficients_at(D.plus_shifted, mm))
    minus_margin = min(shifted_tail_coefficients_at(D.minus_shifted, mm))
    vals = basic_values(mm)
    checks = (
        head_margin > 0.0,
        plus_margin > 0.0,
        minus_margin > 0.0,
        0.0 < vals["kappa"] < 1.0,
        vals["b0"] > 0.0,
        vals["Mplus"] > 0.0,
        vals["Mminus"] > 0.0,
        vals["Mdiff"] > 0.0,
        vals["epsilon"] > 0.0,
    )
    if not all(checks):
        failures.append((mm, checks))
    for label, value in (
        ("head margin", head_margin),
        ("plus tail shifted coefficient", plus_margin),
        ("minus tail shifted coefficient", minus_margin),
        ("b0", vals["b0"]),
        ("Mplus-Mminus", vals["Mdiff"]),
    ):
        if value < minimum_data[label][0]:
            minimum_data[label] = (value, mm)
print("failures =", failures[:5], "count =", len(failures))
for label, datum in minimum_data.items():
    print(label, "minimum/value-location =", datum)
