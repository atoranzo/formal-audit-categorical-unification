"""Check (SymPy: exact elimination, then 50-digit numerical root finding; not a certificate) of a
counterexample (Remark 'The diagonal must scale, or be scalar', Section 6 of the paper):
strengthening only the off-diagonal couplings with a FIXED non-scalar diagonal can DECREASE J
(n = 2).
A(c) = D + c W, D = diag(-23/100, 31/100), W = [[0,-19/100],[-83/100,0]],
E = [[461/100,259/100],[259/100,146/100]] (positive definite).
With two units there is one bipartition; B = diag(x, y). J(c) = 1/2 log min_{x,y} f_c(x,y)/det E,
f_c = det(E + (A-B) P (A-B)^T), P = stationary covariance (exact rational).
f_c, the residual determinant, is a coercive polynomial in (x, y), and the objective is an
increasing function of it. Its global minimum is located among its real critical points, found
by exact elimination (resultant) and 50-digit root finding; what is not certified is that the
root finding, with its residual filter |df/dy| < 1e-25, finds all of them.
The script also computes, exactly, the matrix S = W Q A^T + A Q W^T + 2c E of the proof of part (b)
of the Proposition on monotonicity under scaling, with Q = c^2 P(c), at c = 0.33 and c = 0.38,
and prints its eigenvalues: det S < 0 (exact), so S has eigenvalues of both signs (it is
indefinite), unlike the case of a scalar diagonal covered by that proposition. Printed messages:
'autovalores de S en c = ...' = eigenvalues of S at c = ..., 'es indefinida' = is indefinite.
Run: python3 -I contraejemplo_diagonal_fija.py"""
import sympy as sp

x, y = sp.symbols('x y', real=True)
D = sp.diag(sp.Rational(-23, 100), sp.Rational(31, 100))
W = sp.Matrix([[0, sp.Rational(-19, 100)], [sp.Rational(-83, 100), 0]])
E = sp.Matrix([[sp.Rational(461, 100), sp.Rational(259, 100)], [sp.Rational(259, 100), sp.Rational(146, 100)]])
assert E.det() > 0 and E[0, 0] > 0


def lyap(A):
    p11, p12, p22 = sp.symbols('p11 p12 p22')
    Pm = sp.Matrix([[p11, p12], [p12, p22]])
    sol = sp.solve(list(A * Pm * A.T + E - Pm), [p11, p12, p22], dict=True)
    assert len(sol) == 1
    return Pm.subs(sol[0])


def J_exact(c):
    A = D + c * W
    rho = max(abs(complex(ev)) for ev in A.eigenvals())
    assert rho < 1
    P = lyap(A)
    B = sp.diag(x, y)
    f = sp.expand((E + (A - B) * P * (A - B).T).det())
    gx, gy = sp.diff(f, x), sp.diff(f, y)
    res = sp.Poly(sp.resultant(gx, gy, x), y)   # exact elimination of x
    best = None
    for yr in res.nroots(n=50, maxsteps=500):
        if abs(sp.im(yr)) > 1e-30:
            continue
        yv = sp.re(yr)
        for xr in sp.Poly(gx.subs(y, yv), x).nroots(n=50, maxsteps=500):
            if abs(sp.im(xr)) > 1e-30:
                continue
            xv = sp.re(xr)
            if abs(gy.subs({x: xv, y: yv})) < sp.Float('1e-25'):
                val = f.subs({x: xv, y: yv})
                if best is None or val < best:
                    best = val
    return sp.N(sp.log(best / E.det()) / 2, 15)


def S_exact(c):
    """S = W Q A^T + A Q W^T + 2c E with Q = c^2 P(c), exactly (rational entries)."""
    A = D + c * W
    Q = c ** 2 * lyap(A)
    S = W * Q * A.T + A * Q * W.T + 2 * c * E
    assert all(entry.is_Rational for entry in S) and S == S.T
    return S


c1, c2 = sp.Rational(33, 100), sp.Rational(38, 100)
J1, J2 = J_exact(c1), J_exact(c2)
print("J(0.33) =", J1)
print("J(0.38) =", J2)
decrece = bool(J1 > J2)
print("J decrece al reforzar los acoplamientos con la diagonal fija:", "sí" if decrece else "NO")
indefinida = True
for c in (c1, c2):
    S = S_exact(c)
    tr, det = S.trace(), S.det()            # exact rationals
    disc = sp.sqrt(tr ** 2 - 4 * det)
    lo, hi = sp.N((tr - disc) / 2, 30), sp.N((tr + disc) / 2, 30)
    indefinida &= bool(det < 0)
    print(f"autovalores de S en c = {float(c):.2f}: {float(lo):.6f} y {float(hi):.6f}; "
          f"det S = {float(det):.6f} < 0 (exacto): {'sí' if det < 0 else 'NO'}")
print("S es indefinida en c = 0.33 y en c = 0.38:", "sí" if indefinida else "NO")
print("TODAS LAS COMPROBACIONES:", "sí" if (decrece and indefinida) else "NO")
raise SystemExit(0 if (decrece and indefinida) else 1)
