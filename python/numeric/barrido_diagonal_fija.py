"""Numerical check (a grid in c; not a certificate) of the sentence of the Remark 'The diagonal must
scale, or be scalar' (Section 6 of the paper) on the extent of the decrease of J: "The decrease is
local: J(A(c)) increases again for larger c, and S is indefinite on a wider range of c than the
decrease, so the indefiniteness of S does not by itself make J decrease" [N].
Data of the remark, all rational, as in ../high_precision/contraejemplo_diagonal_fija.py and
../exact/certificado_diagonal_fija.py (n = 2):
  A(c) = D + c W, D = diag(-23/100, 31/100), W = [[0,-19/100],[-83/100,0]],
  E = [[461/100,259/100],[259/100,146/100]] (positive definite),
and S = W Q A^T + A Q W^T + 2c E, with Q = c^2 P(c), the matrix of the proof of part (b) of the
Proposition on monotonicity under scaling. On the grid c = 0.005, 0.010, ..., 0.600 (120 points)
the script checks:
 (1) A(c) is stable (Jury criterion |det A| < 1 and |tr A| < 1 + det A, exact), and the stationary
     covariance P(c), the solution of P = A P A^T + E computed in exact rationals, is positive
     definite, at every point;
 (2) its values of J at c = 0.33 and c = 0.38 agree to 1e-10 with those certified exactly by
     ../exact/certificado_diagonal_fija.py (0.1040827049... and 0.0997015975...);
 (3) J decreases only on one run of consecutive steps, from c = 0.340 to c = 0.380, and increases
     on every other step of the grid: on every step before the run and on every step after it, up
     to c = 0.600; a golden-section search between the neighbouring points of the grid locates the
     local maximum and the local minimum of J at the two ends of the run;
 (4) S is indefinite (det S < 0, exact) at every point from c = 0.005 to c = 0.395, and positive
     definite (det S > 0 and tr S > 0, exact) at every point from c = 0.400 to c = 0.600;
 (5) so S is indefinite on a wider range of c than the decrease: that range contains the run of
     (3) and also steps of the grid on which J increases.
How J is computed. With two units there is one bipartition and B = diag(x, y); J(c) =
1/2 log(min f / det E), where f(x, y) = det(E + (A - B) P (A - B)^T) is the residual determinant.
For fixed y, f is a quadratic in x with leading coefficient P11 E22 + det(P) (A22 - y)^2 > 0 (the
identity checked by the certificate), so its minimum over x is g(y) = f0 - f1^2/(4 f2), where
f2, f1 and f0 are obtained from f at x = -1, 0 and 1. The minimum of g over y is searched in
floating point on a grid of y in [-8, 8] with step 0.001: every local minimum of the grid values is
refined by golden-section search and the least value is kept. The script checks that this minimum
lies inside the grid, where g is larger at both ends, and that g has a single local minimum on the
grid of y at every point of the grid of c. This part is numerical: it does not certify that the
minimum over y is global, and the statements checked hold at the points of the grid. The exact
parts are named above: the stability of A(c), P(c) > 0, and the signs of det S and tr S, from the
exact rational entries of P(c) and S. The script also prints J and the eigenvalues of S at ten
values of c. Natural logarithms (nats).
Printed lines: '[ok]' or '[FAIL]' before each check; 'checks passed', and the verdict line of the
archive, 'TODAS LAS COMPROBACIONES: sí' (all checks: yes).
Run: python3 -I barrido_diagonal_fija.py"""
from fractions import Fraction as Fr
import math

import numpy as np

D = ((Fr(-23, 100), Fr(0)), (Fr(0), Fr(31, 100)))
W = ((Fr(0), Fr(-19, 100)), (Fr(-83, 100), Fr(0)))
E = ((Fr(461, 100), Fr(259, 100)), (Fr(259, 100), Fr(146, 100)))
# values certified by ../exact/certificado_diagonal_fija.py (its printed intervals, 20 digits)
J_CERT = {Fr(33, 100): 0.10408270490793657722, Fr(38, 100): 0.099701597502688759378}
GRID = [Fr(k, 200) for k in range(1, 121)]          # c = 0.005, 0.010, ..., 0.600
YS = np.linspace(-8.0, 8.0, 16001)                  # grid of y, step 0.001
PHI = (math.sqrt(5.0) - 1.0) / 2.0

RESULTS = []


def check(name, cond):
    cond = bool(cond)
    RESULTS.append(cond)
    print(f"[{'ok' if cond else 'FAIL'}] {name}")
    return cond


def add(X, Y):
    return tuple(tuple(X[i][j] + Y[i][j] for j in range(2)) for i in range(2))


def scal(k, X):
    return tuple(tuple(k * X[i][j] for j in range(2)) for i in range(2))


def mul(X, Y):
    return tuple(tuple(sum(X[i][k] * Y[k][j] for k in range(2)) for j in range(2)) for i in range(2))


def tr_(X):
    return tuple(tuple(X[j][i] for j in range(2)) for i in range(2))


def det(X):
    return X[0][0] * X[1][1] - X[0][1] * X[1][0]


def A_of(c):
    return add(D, scal(c, W))


def lyap(A):
    """The symmetric P with P = A P A^T + E, exactly: a 3 x 3 linear system in (p11, p12, p22)."""
    (a11, a12), (a21, a22) = A
    M = [[1 - a11 * a11, -2 * a11 * a12, -a12 * a12, E[0][0]],
         [-a11 * a21, 1 - (a11 * a22 + a12 * a21), -a12 * a22, E[0][1]],
         [-a21 * a21, -2 * a21 * a22, 1 - a22 * a22, E[1][1]]]
    for col in range(3):                              # Gauss-Jordan elimination in rationals
        piv = next(r for r in range(col, 3) if M[r][col] != 0)
        M[col], M[piv] = M[piv], M[col]
        M[col] = [v / M[col][col] for v in M[col]]
        for r in range(3):
            if r != col and M[r][col] != 0:
                M[r] = [vr - M[r][col] * vc for vr, vc in zip(M[r], M[col])]
    p11, p12, p22 = M[0][3], M[1][3], M[2][3]
    P = ((p11, p12), (p12, p22))
    assert add(mul(mul(A, P), tr_(A)), E) == P      # P = A P A^T + E holds exactly
    return P


def exact_parts(c):
    A = A_of(c)
    stable = abs(det(A)) < 1 and abs(A[0][0] + A[1][1]) < 1 + det(A)
    P = lyap(A)
    pos = P[0][0] > 0 and det(P) > 0
    Q = scal(c * c, P)
    S = add(add(mul(mul(W, Q), tr_(A)), mul(mul(A, Q), tr_(W))), scal(2 * c, E))
    assert S == tr_(S)
    return A, P, stable, pos, S


def g_factory(A, P):
    """g(y) = min over x of f(x, y), vectorized in y (floating point)."""
    (a11, a12), (a21, a22) = [[float(v) for v in row] for row in A]
    (p11, p12), (_, p22) = [[float(v) for v in row] for row in P]
    (e11, e12), (_, e22) = [[float(v) for v in row] for row in E]

    def f(x, y):
        m11, m12, m21, m22 = a11 - x, a12, a21, a22 - y
        r11 = e11 + p11 * m11 * m11 + 2 * p12 * m11 * m12 + p22 * m12 * m12
        r12 = e12 + p11 * m11 * m21 + p12 * (m11 * m22 + m12 * m21) + p22 * m12 * m22
        r22 = e22 + p11 * m21 * m21 + 2 * p12 * m21 * m22 + p22 * m22 * m22
        return r11 * r22 - r12 * r12

    def g(y):
        fm, f0, fp = f(-1.0, y), f(0.0, y), f(1.0, y)
        f2, f1 = (fp + fm) / 2 - f0, (fp - fm) / 2
        return f0 - f1 * f1 / (4 * f2), f2

    return g


def golden_min(fun, lo, hi, iters=100):
    for _ in range(iters):
        m1, m2 = hi - PHI * (hi - lo), lo + PHI * (hi - lo)
        if fun(m1) < fun(m2):
            hi = m2
        else:
            lo = m1
    return (lo + hi) / 2


def J_of(c, A=None, P=None):
    """J(A(c)) in floating point, and the number of local minima of g on the y-grid."""
    if A is None:
        A = A_of(c)
        P = lyap(A)
    g = g_factory(A, P)
    vals, f2 = g(YS)
    assert np.all(f2 > 0)
    loc = (np.nonzero((vals[1:-1] < vals[:-2]) & (vals[1:-1] < vals[2:]))[0] + 1).tolist()
    best = min(vals[0], vals[-1])
    gmin = math.inf
    for k in loc:
        yk = golden_min(lambda t: g(t)[0], YS[k - 1], YS[k + 1])
        gmin = min(gmin, g(yk)[0], vals[k])
    interior = gmin < best
    return 0.5 * math.log(gmin / float(det(E))), len(loc), interior


def main():
    rows = [(c,) + exact_parts(c) for c in GRID]
    check("grid of c: 0.005 to 0.600 with step 0.005, 120 points; A(c) is stable at every point "
          "(Jury criterion, exact)", all(r[3] for r in rows))
    check("P(c) = A P A^T + E, solved exactly, is positive definite at every point (P11 > 0 and det P > 0)",
          all(r[4] for r in rows))
    Js, nloc, inner = [], [], []
    for c, A, P, _, _, _ in rows:
        j, n, i = J_of(c, A, P)
        Js.append(j); nloc.append(n); inner.append(i)
    check("the minimum over y lies inside the grid of y at every point, and g has one local minimum "
          "on that grid", all(inner) and all(n == 1 for n in nloc))
    ok_cert = all(abs(Js[GRID.index(c)] - v) < 1e-10 for c, v in J_CERT.items())
    check(f"J(0.33) = {Js[GRID.index(Fr(33, 100))]:.10f} and J(0.38) = {Js[GRID.index(Fr(38, 100))]:.10f}: "
          "within 1e-10 of the values certified by certificado_diagonal_fija.py", ok_cert)
    steps = range(len(GRID) - 1)
    dec = [i for i in steps if Js[i + 1] < Js[i]]
    run = bool(dec) and dec == list(range(dec[0], dec[-1] + 1))
    i0, i1 = (dec[0], dec[-1] + 1) if dec else (0, 0)
    c0, c1 = float(GRID[i0]), float(GRID[i1])
    check(f"J decreases on the grid only on one run of consecutive steps, from c = {c0:.3f} to "
          f"c = {c1:.3f} ({len(dec)} of the {len(GRID) - 1} steps)", run)
    check(f"J increases on every other step: on the {i0} steps before the run, from c = {float(GRID[0]):.3f}, "
          f"and on the {len(GRID) - 1 - i1} steps after it, up to c = {float(GRID[-1]):.3f}; "
          f"J(0.40) = {Js[GRID.index(Fr(2, 5))]:.6f} > J(0.38) = {Js[GRID.index(Fr(38, 100))]:.6f}",
          run and i0 > 0 and i1 < len(GRID) - 1 and
          all(Js[i + 1] > Js[i] for i in range(0, i0)) and
          all(Js[i + 1] > Js[i] for i in range(i1, len(GRID) - 1)))
    inner_run = run and 0 < i0 and i1 < len(GRID) - 1
    if inner_run:
        Jf = lambda t: J_of(Fr(t))[0]
        a0, b0, a1, b1 = (float(GRID[i]) for i in (i0 - 1, i0 + 1, i1 - 1, i1 + 1))
        cmax = golden_min(lambda t: -Jf(t), a0, b0)
        cmin = golden_min(Jf, a1, b1)
        Jmax, Jmin = Jf(cmax), Jf(cmin)
        print(f"     local maximum of J between c = {a0:.3f} and c = {b0:.3f}: c = {cmax:.4f}, J = {Jmax:.6f}")
        print(f"     local minimum of J between c = {a1:.3f} and c = {b1:.3f}: c = {cmin:.4f}, J = {Jmin:.6f}")
    check("these extrema lie between the neighbouring points of the grid, at the ends of the run",
          inner_run and a0 < cmax < b0 and a1 < cmin < b1 and Jmax >= Js[i0] and Jmin <= Js[i1])
    indef = [det(r[5]) < 0 for r in rows]
    posdef = [det(r[5]) > 0 and r[5][0][0] + r[5][1][1] > 0 for r in rows]
    k1 = indef.index(False) if False in indef else len(GRID)
    s_ok = 0 < k1 < len(GRID) and all(indef[:k1]) and all(posdef[k1:])
    last_indef = float(GRID[k1 - 1]) if k1 > 0 else math.nan
    first_pd = float(GRID[k1]) if k1 < len(GRID) else math.nan
    check(f"S is indefinite (det S < 0, exact) at every point from c = {float(GRID[0]):.3f} to "
          f"c = {last_indef:.3f} ({k1} points), and positive definite (det S > 0, tr S > 0, exact) "
          f"at every point from c = {first_pd:.3f} to c = {float(GRID[-1]):.3f} "
          f"({len(GRID) - k1} points)", s_ok)
    up = [i for i in range(k1 - 1) if Js[i + 1] > Js[i]]
    check(f"S is indefinite on a wider range of c than the decrease: [{float(GRID[0]):.3f}, "
          f"{last_indef:.3f}] contains [{c0:.3f}, {c1:.3f}], and J increases on {len(up)} of "
          f"its {max(k1 - 1, 0)} steps", run and s_ok and i1 <= k1 - 1 and len(up) > 0)
    print("     c      J(A(c))    eigenvalues of S (from its exact trace and determinant)")
    for c in (Fr(1, 10), Fr(2, 10), Fr(3, 10), Fr(33, 100), Fr(35, 100), Fr(38, 100), Fr(4, 10),
              Fr(45, 100), Fr(5, 10), Fr(6, 10)):
        i = GRID.index(c)
        S = rows[i][5]
        t, d = float(S[0][0] + S[1][1]), float(det(S))
        disc = math.sqrt(t * t - 4 * d)
        print(f"     {float(c):.2f}   {Js[i]:.6f}   {(t - disc) / 2:+.6f} and {(t + disc) / 2:.6f}")
    n_ok = sum(RESULTS)
    print(f"checks passed: {n_ok} of {len(RESULTS)}")
    allok = n_ok == len(RESULTS)
    print("TODAS LAS COMPROBACIONES:", "sí" if allok else "NO")
    return 0 if allok else 1


if __name__ == "__main__":
    raise SystemExit(main())
