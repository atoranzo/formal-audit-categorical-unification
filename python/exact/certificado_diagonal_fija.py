"""Exact certificate (SymPy 1.14 and exact rational arithmetic) of the decrease of J in the Remark
'The diagonal must scale, or be scalar' (Section 6 of the paper): with a FIXED non-scalar diagonal
of self-couplings, strengthening the couplings from c = 0.33 to c = 0.38 DECREASES J (n = 2).
Data of the remark, all rational:
  A(c) = D + c W, D = diag(-23/100, 31/100), W = [[0,-19/100],[-83/100,0]],
  E = [[461/100,259/100],[259/100,146/100]] (positive definite).
With two units there is one bipartition, B = diag(x, y), and J(c) = 1/2 log(min f / det E), where
  f(x, y) = det(E + (A - B) P (A - B)^T)   (the residual determinant)
and P is the stationary covariance, P = A P A^T + E, solved exactly; P > 0 also shows spr(A) < 1.
../high_precision/contraejemplo_diagonal_fija.py computes the same two values by exact elimination
and 50-digit root finding, which is not a certificate. This script certifies them:
 (1) For fixed y, f is a quadratic in x, f = f2(y) x^2 + f1(y) x + f0(y), and the exact identity
     f2(y) = P11 E22 + det(P) (A22 - y)^2 gives f2(y) >= P11 E22 > 0.
 (2) Hence the minimum of f over x is g(y) = N(y) / (4 f2(y)), with N = 4 f2 f0 - f1^2, attained
     at x*(y) = -f1(y) / (2 f2(y)).
 (3) deg N = deg f2 + 2, with positive leading coefficients, so g(y) -> +infinity as |y| -> infinity
     and the minimum of g over y is attained at a real zero of h = N' f2 - N f2', a polynomial of
     degree 5 (g' = h / (4 f2^2)).
 (4) h has exactly one real zero, and it is simple: a Sturm sequence of h, computed here with exact
     rationals, counts its distinct real zeros, and SymPy's Poly.count_roots counts them again. The
     zero is isolated exactly (Poly.intervals) in an interval [a, b] of width below 1e-40, where h
     changes sign and the Sturm sequence counts one zero (both checked exactly).
 (5) Exact rational interval arithmetic on [a, b] gives a lower bound LB <= min f. The exact value
     UB = g(y_r) at the rational midpoint y_r of [a, b] is a value of f, attained at
     (x*(y_r), y_r), so min f <= UB. Since log t <= t - 1, the interval
     [1/2 log(LB/det E), 1/2 log(UB/det E)], which contains J, has width at most
     (UB - LB)/(2 LB), checked to be below 1e-40.
 (6) The decrease J(0.33) > J(0.38) is certified by LB(0.33) > UB(0.38): E is the same at both
     values of c, so the residual determinants are compared directly, without logarithms.
The values of J printed are the ends of that interval, evaluated with mpmath's interval arithmetic
(outward rounding) at 60 digits; their ten-decimal truncations and six-decimal roundings are compared
with the values printed in the paper. Natural logarithms (nats). Every printed line is computed from
exact rationals, so the output is the same on every run.
Run: python3 -I certificado_diagonal_fija.py"""
from fractions import Fraction as Fr
import math

import mpmath
import sympy as sp

mpmath.mp.dps = 60
mpmath.iv.dps = 60

R = sp.Rational
x, y = sp.symbols('x y', real=True)
D = sp.diag(R(-23, 100), R(31, 100))
W = sp.Matrix([[0, R(-19, 100)], [R(-83, 100), 0]])
E = sp.Matrix([[R(461, 100), R(259, 100)], [R(259, 100), R(146, 100)]])

RESULTS = []


def check(name, cond):
    cond = bool(cond)
    RESULTS.append(cond)
    print(f"[{'ok' if cond else 'FAIL'}] {name}")
    return cond


def fr(q):
    """SymPy Rational (or integer) -> Fraction, exactly."""
    q = sp.Rational(q)
    return Fr(int(q.p), int(q.q))


# ---------------------------------------------------------------- polynomials over Q (Fractions)
def p_eval(p, t):
    """Horner evaluation of p (list of Fractions, highest degree first) at the rational t."""
    v = Fr(0)
    for c in p:
        v = v * t + c
    return v


def p_rem(u, v):
    """Remainder of the division of u by v (lists of Fractions, highest degree first, v[0] != 0)."""
    u = list(u)
    while len(u) >= len(v):
        q = u[0] / v[0]
        for i in range(len(v)):
            u[i] -= q * v[i]
        assert u[0] == 0
        u.pop(0)
    while u and u[0] == 0:
        u.pop(0)
    return u


def sturm_chain(p):
    """Sturm sequence p, p', -rem(p, p'), ... with exact rationals."""
    n = len(p) - 1
    chain = [list(p), [c * (n - i) for i, c in enumerate(p[:-1])]]
    while True:
        r = p_rem(chain[-2], chain[-1])
        if not r:
            return chain
        chain.append([-c for c in r])


def variations(signs):
    s = [v for v in signs if v != 0]
    return sum(1 for u, v in zip(s, s[1:]) if u != v)


def sign(q):
    return (q > 0) - (q < 0)


def var_at(chain, t):
    return variations([sign(p_eval(p, t)) for p in chain])


def var_at_inf(chain, plus):
    return variations([sign(p[0]) * (1 if (plus or (len(p) - 1) % 2 == 0) else -1) for p in chain])


def poly_interval(p, a, b):
    """Exact enclosure [lo, hi] of the polynomial p (SymPy Poly in y) on [a, b], term by term."""
    lo = hi = Fr(0)
    for (k,), c in p.terms():
        c = fr(c)
        if k == 0:
            mlo = mhi = Fr(1)
        else:
            va, vb = a ** k, b ** k
            if k % 2 == 0 and a < 0 < b:
                mlo, mhi = Fr(0), max(va, vb)
            else:
                mlo, mhi = min(va, vb), max(va, vb)
        if c >= 0:
            lo, hi = lo + c * mlo, hi + c * mhi
        else:
            lo, hi = lo + c * mhi, hi + c * mlo
    return lo, hi


def iv_of(q):
    return mpmath.iv.mpf(q.numerator) / mpmath.iv.mpf(q.denominator)


def stationary(A):
    """P = A P A^T + E, exactly: (I - A kron A) vec P = vec E, vec by rows."""
    K = sp.eye(4) - sp.kronecker_product(A, A)
    P = K.LUsolve(E.reshape(4, 1)).reshape(2, 2)
    return P


def analyse(c, label):
    A = D + c * W
    tr, dt = A.trace(), A.det()
    # (0) stability and the stationary covariance, exactly
    check(f"c = {label}: Jury criterion |det A| < 1 and |tr A| < 1 + det A (spr(A) < 1)",
          abs(dt) < 1 and abs(tr) < 1 + dt)
    disc = float(tr) ** 2 - 4 * float(dt)
    rho = max(abs((float(tr) + math.sqrt(disc)) / 2), abs((float(tr) - math.sqrt(disc)) / 2))
    P = stationary(A)
    check(f"c = {label}: P = A P A^T + E and P symmetric, exactly (spr(A) = {rho:.6f})",
          sp.expand(A * P * A.T + E - P) == sp.zeros(2, 2) and P == P.T)
    detP = P.det()
    check(f"c = {label}: P > 0 (P11 > 0 and det P > 0)", P[0, 0] > 0 and detP > 0)
    # (1) f is quadratic in x with leading coefficient f2(y) = P11 E22 + det(P) (A22 - y)^2
    B = sp.diag(x, y)
    M = A - B
    f = sp.expand((E + M * P * M.T).det())
    fx = sp.Poly(f, x)
    check(f"c = {label}: f is a quadratic in x", fx.degree() == 2)
    f2 = sp.Poly(fx.coeff_monomial(x ** 2), y)
    f1 = sp.Poly(fx.coeff_monomial(x), y)
    f0 = sp.Poly(fx.coeff_monomial(1), y)
    ident = sp.Poly(P[0, 0] * E[1, 1] + detP * (A[1, 1] - y) ** 2, y)
    check(f"c = {label}: f2(y) = P11 E22 + det(P) (A22 - y)^2 >= P11 E22 > 0 (exact identity)",
          (f2 - ident).is_zero and P[0, 0] * E[1, 1] > 0)
    # (2)-(3) g = N / (4 f2) and h = N' f2 - N f2'
    N = 4 * f2 * f0 - f1 ** 2
    check(f"c = {label}: deg N = deg f2 + 2 = 4, positive leading coefficients (g -> +inf)",
          N.degree() == 4 and f2.degree() == 2 and N.LC() > 0 and f2.LC() > 0)
    h = N.diff(y) * f2 - N * f2.diff(y)
    check(f"c = {label}: h = N' f2 - N f2' has degree 5", h.degree() == 5)
    # (4) one real zero of h: Sturm sequence (exact rationals) and SymPy; exact isolation
    hc = [fr(t) for t in h.all_coeffs()]
    chain = sturm_chain(hc)
    n_sturm = var_at_inf(chain, False) - var_at_inf(chain, True)
    check(f"c = {label}: Sturm sequence: h has exactly {n_sturm} real zero, simple (gcd(h, h') = 1)",
          n_sturm == 1 and len(chain[-1]) == 1)
    check(f"c = {label}: SymPy Poly.count_roots: {h.count_roots()} real zero", h.count_roots() == 1)
    ivs = h.intervals(eps=R(1, 10 ** 40))
    check(f"c = {label}: Poly.intervals isolates one simple real zero", len(ivs) == 1 and ivs[0][1] == 1)
    (a, b), _ = ivs[0]
    a, b = fr(a), fr(b)
    check(f"c = {label}: isolating interval [a, b] of width below 1e-40, h(a) h(b) < 0, "
          f"one zero in (a, b) by the Sturm sequence",
          0 < b - a < Fr(1, 10 ** 40) and p_eval(hc, a) * p_eval(hc, b) < 0
          and var_at(chain, a) - var_at(chain, b) == 1)
    # (5) lower bound by interval arithmetic, upper bound by an attained value
    Nlo, _ = poly_interval(N, a, b)
    _, f2hi = poly_interval(f2, a, b)
    f2lo, _ = poly_interval(f2, a, b)
    check(f"c = {label}: on [a, b], N >= N_lo > 0 and f2 >= f2_lo > 0 (rational interval arithmetic)",
          Nlo > 0 and f2lo > 0)
    LB = Nlo / (4 * f2hi)
    yr = (a + b) / 2
    UB = p_eval([fr(t) for t in N.all_coeffs()], yr) / (4 * p_eval([fr(t) for t in f2.all_coeffs()], yr))
    xr = -p_eval([fr(t) for t in f1.all_coeffs()], yr) / (2 * p_eval([fr(t) for t in f2.all_coeffs()], yr))
    fval = f.subs({x: R(xr.numerator, xr.denominator), y: R(yr.numerator, yr.denominator)})
    check(f"c = {label}: UB = g(y_r) = f(x*(y_r), y_r) is attained (exact), and LB <= UB",
          fr(fval) == UB and LB <= UB)
    width_bound = (UB - LB) / (2 * LB)
    check(f"c = {label}: width of the interval of J <= (UB - LB)/(2 LB) < 1e-40 (exact)",
          width_bound < Fr(1, 10 ** 40))
    dE = fr(E.det())
    Jlo = (mpmath.iv.log(iv_of(LB / dE)) / 2).a
    Jhi = (mpmath.iv.log(iv_of(UB / dE)) / 2).b
    return dict(LB=LB, UB=UB, Jlo=mpmath.mpf(Jlo), Jhi=mpmath.mpf(Jhi), xr=xr, yr=yr, a=a, b=b,
                width_bound=width_bound)


def trunc10(v):
    return int(mpmath.floor(v * 10 ** 10))


res = {}
for c, label, paper10, paper6 in ((R(33, 100), '0.33', 1040827049, '0.104083'),
                                  (R(38, 100), '0.38', 997015975, '0.099702')):
    r = analyse(c, label)
    res[label] = r
    print(f"     minimizer: x = {float(r['xr']):.9f}, y = {float(r['yr']):.9f}")
    print(f"     J(A({label})) in [{mpmath.nstr(r['Jlo'], 20)}, {mpmath.nstr(r['Jhi'], 20)}], "
          f"width at most {float(r['width_bound']):.1e}")
    p6 = mpmath.mpf(paper6)
    check(f"c = {label}: J = 0.{paper10:010d}... to ten decimals and {paper6} to six, "
          f"as printed in the paper",
          trunc10(r['Jlo']) == trunc10(r['Jhi']) == paper10
          and p6 - mpmath.mpf('5e-7') <= r['Jlo'] and r['Jhi'] < p6 + mpmath.mpf('5e-7'))

LB33, UB38 = res['0.33']['LB'], res['0.38']['UB']
margin = (LB33 - UB38) / UB38
check("the decrease J(A(0.33)) > J(A(0.38)) is certified: LB(0.33) > UB(0.38), exactly "
      f"(relative margin in the residual determinant {float(margin):.4%})", LB33 > UB38)
ok = all(RESULTS)
print(f"checks passed: {sum(RESULTS)} of {len(RESULTS)}")
print("TODAS LAS COMPROBACIONES:", "sí" if ok else "NO")
raise SystemExit(0 if ok else 1)
