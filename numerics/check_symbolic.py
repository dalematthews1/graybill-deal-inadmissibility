"""Independent symbolic verification of the series/sign certificate in the
Graybill-Deal counterexample note (Sections 4, 5, 7).

Everything here is derived from equation (8)'s integrand, which I re-derived
by hand from (5) via r-theta = (1-s^2)x/(2(1+sx)), p(r) = -(1-s^2)(1-x^2)(s+x)
/(4(1+sx)^3), d=(1+sx)/2, density K_a (1-x^2)^(a-1).

I(s) = int_{-1}^{1} (1-x^2)^a * x (s+x)(alpha+sx) / (1+sx)^5 dx,  a = nu/2.

Pairing x,-x:  I(s) = int_0^1 (1-x^2)^a N(x,s) (1-s^2 x^2)^{-5} dx,
N(x,s) = x[(s+x)(alpha+sx)(1-sx)^5 - (s-x)(alpha-sx)(1+sx)^5].

Coefficient of z^m (z=s^2):
c_m = sum_{p,q even} n_{p,q} C(m-p/2+4,4) M_{q/2+m-p/2},  M_t=int_0^1 x^{2t}(1-x^2)^a dx.
M ratio: M_{j+1}/M_j = (2j+1)/(2j+nu+3).
"""
import sympy as sp
from sympy import Rational as R, binomial, symbols, expand, simplify, factor

s, x, al, nu, m = symbols('s x alpha nu m')

N = expand(x*((s+x)*(al+s*x)*(1-s*x)**5 - (s-x)*(al-s*x)*(1+s*x)**5))
P = sp.Poly(N, s, x)

# collect n_{p,q}
coeffs = {}
for (p, q), cval in zip(P.monoms(), P.coeffs()):
    assert p % 2 == 0 and q % 2 == 0, (p, q)  # even in s and x as claimed
    coeffs[(p, q)] = cval

def M_ratio_to(t, target, nu_val):
    """M_t / M_target, exact, for a = nu/2."""
    r = sp.Integer(1)
    if t < target:
        for j in range(t, target):   # M_j/M_{j+1} = (2j+nu+3)/(2j+1)
            r *= R(2*j + nu_val + 3, 1) / (2*j + 1) if isinstance(nu_val, int) else (2*j + nu + 3)/(2*j + 1)
    else:
        for j in range(target, t):
            r *= R(2*j + 1, 1)/(2*j + nu_val + 3) if isinstance(nu_val, int) else (2*j + 1)/(2*j + nu + 3)
    return r

def Qm(m_val, nu_val):
    """c_m / M_{m+1} exact; nu_val int or the symbol nu."""
    alpha_val = (nu_val - 4)/(4*(nu_val - 1)) if not isinstance(nu_val, int) else R(nu_val-4, 4*(nu_val-1))
    tot = sp.Integer(0)
    for (p, q), cval in coeffs.items():
        k = m_val - p//2
        if k < 0:
            continue
        t = q//2 + k
        term = cval.subs(al, alpha_val) * binomial(k+4, 4) * M_ratio_to(t, m_val+1, nu_val)
        tot += term
    return sp.simplify(tot)

print("=== n=13 (nu=12): claimed Q0,Q1,Q2 ===")
q0, q1, q2 = Qm(0, 12), Qm(1, 12), Qm(2, 12)
print("Q0 =", q0, " claimed 4/11   ->", q0 == R(4,11))
print("Q1 =", q1, " claimed -116/33->", q1 == R(-116,33))
print("Q2 =", q2, " claimed 232/11 ->", q2 == R(232,11))

print("\n=== n=13: tail formula (10) for m=3..40 ===")
D13 = [8232, 20148, 23236, 13040, 2880]
ok = True
for mm in range(3, 41):
    lhs = (2*mm+1) * Qm(mm, 12)
    rhs = R(1,11) * sum(D13[j]*sp.binomial(mm-3, j) for j in range(5))
    if sp.simplify(lhs - rhs) != 0:
        ok = False
        print("MISMATCH at m =", mm, lhs, rhs)
print("all m=3..40 match:", ok, "(rational-function degree bound => identity for all m>=3)")

print("\n=== moments and exact constants (n=13) ===")
a6 = 6
M1 = sp.integrate(x**2*(1-x**2)**6, (x, 0, 1))
M2 = sp.integrate(x**4*(1-x**2)**6, (x, 0, 1))
M3 = sp.integrate(x**6*(1-x**2)**6, (x, 0, 1))
print("M1 =", M1, "claimed 1024/45045 ->", M1 == R(1024,45045))
print("M2/M1 =", M2/M1, "claimed 3/17 ->", sp.simplify(M2/M1 - R(3,17)) == 0)
print("M3/M1 =", M3/M1, "claimed 15/323 ->", sp.simplify(M3/M1 - R(15,323)) == 0)

# quadratic lower bound and its min
z = symbols('z')
L = R(4,11) - R(116,187)*z + R(3480,3553)*z**2
zstar = sp.solve(sp.diff(L, z), z)[0]
Lmin = sp.simplify(L.subs(z, zstar))
print("z* =", zstar, "claimed 19/60 ->", zstar == R(19,60))
print("L(z*) =", Lmin, "claimed 1489/5610 ->", Lmin == R(1489,5610))
# check quadratic term coeff matches Q2*M3/M1 and linear Q1*M2/M1
print("lin coeff -116/187 == Q1*M2/M1 ->", sp.simplify(R(-116,33)*R(3,17) + R(116,187)) == 0)
print("quad coeff 3480/3553 == Q2*M3/M1 ->", sp.simplify(R(232,11)*R(15,323) - R(3480,3553)) == 0)

# J4, J6 exact at s=1, and K2, H
J4 = sp.integrate((1-x**2)**7/(1+x)**4, (x, -1, 1))
J6 = sp.integrate((1-x**2)**7/(1+x)**6, (x, -1, 1))
print("J4 =", J4, "claimed 256/165 ->", J4 == R(256,165))
print("J6 =", J6, "claimed 64/9  ->", J6 == R(64,9))
K2 = R(144, 4*11*10)
H = J4 + R(15,4)*K2*J6
print("K2 =", K2, "claimed 18/55 ->", K2 == R(18,55))
print("H  =", H,  "claimed 1696/165 ->", H == R(1696,165))
bound_g = 4*M1*Lmin/H
bound_h = bound_g/4
print("4*M1*Lmin/H =", bound_g, "claimed 95296/40585545 ->", bound_g == R(95296,40585545))
print("M1*Lmin/H   =", bound_h, "claimed 23824/40585545 ->", bound_h == R(23824,40585545))
print("eps=1/2000 < bound ->", R(1,2000) < bound_h)

print("\n=== Section 7: general-nu Q0,Q1,Q2 symbolically in nu ===")
Q0s, Q1s, Q2s = Qm(0, nu), Qm(1, nu), Qm(2, nu)
print("Q0(nu) ok:", sp.simplify(Q0s - (nu-4)/(2*(nu-1))) == 0)
print("Q1(nu) ok:", sp.simplify(Q1s + (nu**2+4*nu+40)/(6*(nu-1))) == 0)
print("Q2(nu) ok:", sp.simplify(Q2s - (5*nu**2-19*nu-28)/(2*(nu-1))) == 0)

print("\n=== Section 7: D_j(nu) formulas, m=3..12 symbolically in nu ===")
Dj = [308*nu**2-896*nu-672, 712*nu**2-1774*nu-648, 798*nu**2-1804*nu-320,
      440*nu**2-928*nu-64, 96*nu**2-192*nu]
okg = True
for mm in range(3, 13):
    lhs = (2*mm+1)*Qm(mm, nu)*4*(nu-1)
    rhs = sum(Dj[j]*sp.binomial(mm-3, j) for j in range(5))
    if sp.simplify(lhs - rhs) != 0:
        okg = False
        print("GEN MISMATCH m =", mm)
print("general-nu tail matches m=3..12:", okg)
# spot-check higher m at specific nu values incl. odd nu (half-integer a)
okn = True
for nv in [9, 10, 11, 15, 20, 50, 134, 135, 200]:
    for mm in [15, 25, 40]:
        lhs = (2*mm+1)*Qm(mm, nv)*4*(nv-1)
        rhs = sum(Dj[j].subs(nu, nv)*sp.binomial(mm-3, j) for j in range(5))
        if sp.simplify(lhs - rhs) != 0:
            okn = False
            print("MISMATCH nu,m =", nv, mm)
print("high-m spot checks at nu in {9..200}:", okn)

print("\n=== Section 7: positivity of D_j and Q2 for nu>=8 ===")
for j, d in enumerate(Dj):
    roots = sp.solve(d, nu)
    mx = max(sp.re(sp.N(rt)) for rt in roots)
    print(f"D{j}: largest real root ~ {float(mx):.3f}  (<8 -> positive for nu>=8: {float(mx) < 8})")
rQ2 = max(float(sp.re(sp.N(rt))) for rt in sp.solve(5*nu**2-19*nu-28, nu))
print(f"Q2: largest root ~ {rQ2:.3f} (<8: {rQ2 < 8})")

print("\n=== Section 7: ell_nu = min_[0,1] L_nu > 0 for all nu>=8 ===")
def Lnu(nv):
    return (R(nv-4, 2*(nv-1)) - R(nv**2+4*nv+40, 2*(nv-1)*(nv+5))*z
            + R(15*(5*nv**2-19*nv-28), 2*(nv-1)*(nv+5)*(nv+7))*z**2)
bad = []
ellmin = None
for nv in range(8, 1001):
    Lz = Lnu(nv)
    aq = Lz.coeff(z, 2); bq = Lz.coeff(z, 1); cq = Lz.coeff(z, 0)
    zs = -bq/(2*aq)
    cands = [cq, aq+bq+cq] + ([sp.simplify(Lz.subs(z, zs))] if 0 <= zs <= 1 else [])
    mn = min(cands)
    if mn <= 0:
        bad.append(nv)
    if ellmin is None or mn < ellmin[0]:
        ellmin = (mn, nv)
print("nu=8..1000 all positive:", not bad, " smallest ell:", sp.nsimplify(ellmin[0]), "at nu =", ellmin[1], "=", float(ellmin[0]))
# nu>=135: vertex right of 1 iff nu^3-139nu^2+638nu+1120>0; check + monotone
vp = nu**3 - 139*nu**2 + 638*nu + 1120
print("vertex poly at 135:", vp.subs(nu, 135), "> 0; derivative min on [135,inf):",
      sp.minimum(sp.diff(vp, nu), nu, sp.Interval(135, sp.oo)))
print("L_nu(1) numerator 6(12nu^2-61nu-140) at nu=8:", 6*(12*64-61*8-140), "> 0, increasing in nu")
# discriminant sign claim
Lsym = ((nu-4)/(2*(nu-1)) - (nu**2+4*nu+40)/(2*(nu-1)*(nu+5))*z
        + 15*(5*nu**2-19*nu-28)/(2*(nu-1)*(nu+5)*(nu+7))*z**2)
disc = sp.discriminant(sp.together(Lsym), z)
Npoly = nu**5 - 285*nu**4 + 992*nu**3 + 9812*nu**2 - 17280*nu - 22400
print("discriminant has sign of N(nu):", sp.factor(sp.simplify(disc / Npoly)))
print("N(nu) < 0 for nu=8..134:", all(Npoly.subs(nu, nv) < 0 for nv in range(8, 135)))
print("\nALL SYMBOLIC CHECKS DONE")
