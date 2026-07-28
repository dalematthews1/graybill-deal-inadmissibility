"""Exact checks for the universal Graybill--Deal reader edition.

This script verifies the bespoke algebra in the proof:

1. the (r,q,t) Jacobian and density exponents;
2. the q=0 transform moments for general unequal shapes;
3. the unequal q-derivative obstruction;
4. the equal-shape mixed derivative obstruction.

It does not, and cannot, verify the cited Lehmann--Casella complete-class
theorem.  Requires SymPy.
"""

import sympy as sp


# ---------------------------------------------------------------------------
# I. Change of variables and density bookkeeping
# ---------------------------------------------------------------------------

r, q, t = sp.symbols("r q t", positive=True)
a, b = sp.symbols("a b", positive=True)
theta = sp.symbols("theta", positive=True)

g1 = r * t
g2 = (1 - r) * t
w = q * t

jacobian = sp.det(
    sp.Matrix(
        [
            [sp.diff(g1, z) for z in (r, q, t)],
            [sp.diff(g2, z) for z in (r, q, t)],
            [sp.diff(w, z) for z in (r, q, t)],
        ]
    )
)
assert sp.factor(jacobian) == -t**2

p = a + b + sp.Rational(3, 2)
t_exponent = (a - 1) + (b - 1) + sp.Rational(1, 2) + 2
assert sp.simplify(t_exponent - (p - 1)) == 0

A = a * r / theta + b * (1 - r) / (1 - theta) + q / 2
B = (
    2 * a * r * (1 - theta)
    + 2 * b * (1 - r) * theta
    + q * theta * (1 - theta)
)
assert sp.factor(A - B / (2 * theta * (1 - theta))) == 0

# The original Gamma normalizers contribute theta^(-a)(1-theta)^(-b);
# integrating t contributes A^(-p), hence [theta(1-theta)]^p.
assert sp.simplify(p - a - (b + sp.Rational(3, 2))) == 0
assert sp.simplify(p - b - (a + sp.Rational(3, 2))) == 0

density_constant = (
    2**p
    * a**a
    * b**b
    * sp.gamma(p)
    / (sp.sqrt(2 * sp.pi) * sp.gamma(a) * sp.gamma(b))
)
special_23 = {a: sp.Rational(1, 2), b: sp.Integer(1)}
assert sp.simplify(density_constant.subs(special_23) - 8 / sp.pi) == 0


# ---------------------------------------------------------------------------
# II. General q=0 transform moments
# ---------------------------------------------------------------------------

h = a + b
lam = h + sp.Rational(1, 2)
r0 = b / h
c = a * b / h

# For
#   G(s)=(1+a s)^(-lam a/h)(1-b s)^(-lam b/h),
# calculate the first three derivatives via log derivatives.
ell1 = -lam * a**2 / h + lam * b**2 / h
ell2 = lam * (a**3 + b**3) / h
ell3 = 2 * lam * (b**4 - a**4) / h

ez1 = sp.factor(-ell1 / lam)
ez2 = sp.factor((ell2 + ell1**2) / (lam * (lam + 1)))
ez3 = sp.factor(
    -(ell3 + 3 * ell1 * ell2 + ell1**3)
    / (lam * (lam + 1) * (lam + 2))
)

assert sp.factor(ez1 - (a - b)) == 0

expected_ez2 = (
    a**2 - a * b + b**2 + lam * (a - b) ** 2
) / (lam + 1)
expected_ez3 = (
    (a - b)
    * (
        2 * (a**2 + b**2)
        + 3 * lam * (a**2 - a * b + b**2)
        + lam**2 * (a - b) ** 2
    )
    / ((lam + 1) * (lam + 2))
)
assert sp.factor(ez2 - expected_ez2) == 0
assert sp.factor(ez3 - expected_ez3) == 0


# ---------------------------------------------------------------------------
# III. Unequal-size obstruction
# ---------------------------------------------------------------------------

z = sp.symbols("z")
theta_from_z = (a - z) / h
target = sp.Poly(
    sp.expand((theta_from_z - r0) * theta_from_z * (1 - theta_from_z)),
    z,
)
moments = [sp.Integer(1), ez1, ez2, ez3]
target_expectation = sp.factor(
    sum(coef * moments[k] for (k,), coef in target.terms())
)

expected_target = (
    2
    * a
    * b
    * (a - b)
    * (2 * h + 1)
    / (h**3 * (2 * h + 3) * (2 * h + 5))
)
assert sp.factor(target_expectation - expected_target) == 0

q_derivative = sp.factor(-p / (2 * c) * expected_target)
expected_q_derivative = (
    -(a - b) * (2 * h + 1) / (2 * h**2 * (2 * h + 5))
)
assert sp.factor(q_derivative - expected_q_derivative) == 0
assert sp.factor(expected_target.subs(special_23) + sp.Rational(1, 81)) == 0
assert sp.factor(
    expected_q_derivative.subs(special_23) - sp.Rational(1, 18)
) == 0


# ---------------------------------------------------------------------------
# IV. Equal-size mixed derivative
# ---------------------------------------------------------------------------

pe = 2 * a + sp.Rational(3, 2)
ey2 = 1 / pe
ey4 = 3 / (pe * (pe + 2))
ec = (1 - ey2) / 4
ey2c = (ey2 - ey4) / 4

mixed = sp.factor(
    pe / a * (-(pe + 1) * ey2c + pe * ey2 * ec)
)
expected_mixed = (pe - 1) / (4 * a * (pe + 2))
assert sp.factor(mixed - expected_mixed) == 0
assert sp.factor(
    expected_mixed.subs(a, sp.Rational(1, 2)) - sp.Rational(1, 6)
) == 0


print("density Jacobian and exponents: passed")
print("special density constant C_(1/2,1) = 8/pi")
print("unequal expectation =", sp.factor(expected_target))
print("unequal q derivative =", sp.factor(expected_q_derivative))
print("(n1,n2)=(2,3): expectation=-1/81 and q derivative=1/18")
print("equal mixed derivative =", sp.factor(expected_mixed))
print("(n1,n2)=(2,2): mixed derivative=1/6")
