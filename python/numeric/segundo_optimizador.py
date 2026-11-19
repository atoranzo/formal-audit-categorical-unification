"""The second check of the four-unit networks (numerical illustration, not a certificate).
Table 6 of the paper (Section 5.4; Table 5 in version 1.0) reports J for the networks
A = 0.2 I + 0.3 M_Gamma, Gamma in {C4 (ring), K13 (star), P4 (path), 2K2 (split)}, E = I,
computed by pistas_numerico.py. Version 1.0 cited a second check of these values, run during
the internal review and not archived then: section (1) of a working script, verif_gauss.py.
This script repeats that computation exactly: the same seed (1811), the same random restarts,
drawn in the same order, the same BFGS options and the same alternating scheme.

J = min over the seven bipartitions pi of J_pi, and
J_pi = min over B with no coupling across pi of 1/2 log det(E + (A-B) P (A-B)^T) / det E,
with P the stationary covariance (P = A P A^T + E). For each bipartition the check computes
- the BFGS value: SciPy's BFGS (gtol 1e-12, maxiter 50000) from the predictor
  B = A - A_cross(pi) and from 12 random restarts (that predictor plus Gaussian noise of
  standard deviation 0.7 on its free entries); the least value found;
- the alternating value: 400 steps of an alternating weighted least-squares scheme from the
  same predictor (with S = E + (A-B) P (A-B)^T fixed, minimize tr(S^{-1}(A-B) P (A-B)^T) over
  the free entries of B, a linear solve; then recompute S);
and keeps the smaller of the two. This script prints, to seven decimals, J as the check gave
it (the value kept), and separately the alternating scheme alone and BFGS alone (each the
least over the bipartitions), and checks that each agrees to seven decimals with the values
that the original check printed (version 1.0 cited only their agreement to seven digits).

What is shared with pistas_numerico.py: the networks, the enumeration of bipartitions and the
objective are the same code, reformatted; the BFGS search is SciPy's BFGS on that objective
from the same first predictor, with its own seed, restarts and iteration cap. The alternating
scheme is code of its own: a different algorithm, not an independent implementation of the
whole check. Each step of the alternating scheme cannot increase log det S, since
log det X <= log det S + tr(S^{-1} X) - n; the script checks that the objective does not
increase along the 400 steps, up to a relative tolerance of 1e-12 (absolute 1e-15 near 0).
Every value printed is the objective at a candidate B, so it is an upper bound for J (before
rounding), not a certified minimum. Labels of the printed lines (Spanish, as in the original
check): 'conservado' = value kept, 'alterno' = alternating scheme alone, 'archivado' = value
printed by the original check, 'coincide a siete decimales' = agrees to seven decimals,
'el esquema alterno no aumenta el objetivo' = the alternating scheme does not increase the
objective.
Run: python3 -I segundo_optimizador.py"""
import itertools
import numpy as np
from scipy.optimize import minimize
from scipy.linalg import solve_discrete_lyapunov

rng = np.random.default_rng(1811)          # the seed of the original check
ld = lambda X: np.linalg.slogdet(X)[1]
RTOL, ATOL = 1e-12, 1e-15                  # tolerance of the monotonicity guard


def bipartitions(n):
    seen = set()
    for r in range(1, n // 2 + 1):
        for M in itertools.combinations(range(n), r):
            Mc = tuple(sorted(set(range(n)) - set(M)))
            key = min(M, Mc)
            if key in seen:
                continue
            seen.add(key)
            yield set(M)


def mask_of(M, n):
    return np.array([[(i in M) == (j in M) for j in range(n)] for i in range(n)])


def J_pi(A, E, P, M, starts=8):
    """The inner problem for one bipartition, as in the original check, with the BFGS value
    and the alternating value returned separately (the check kept their minimum)."""
    n = A.shape[0]
    mask = mask_of(M, n)
    idx = np.argwhere(mask)

    def f(v):
        B = np.zeros((n, n)); B[idx[:, 0], idx[:, 1]] = v
        return 0.5 * (ld(E + (A - B) @ P @ (A - B).T) - ld(E))
    bfgs = np.inf
    v0s = [A[idx[:, 0], idx[:, 1]].copy()] + [A[idx[:, 0], idx[:, 1]] + rng.normal(0, 0.7, len(idx)) for _ in range(starts)]
    for v0 in v0s:
        r = minimize(f, v0, method='BFGS', options={'gtol': 1e-12, 'maxiter': 50000})
        bfgs = min(bfgs, r.fun)
    # alternating scheme: for fixed S, minimise tr(S^{-1}(A-B)P(A-B)^T) over B with mask
    B = np.where(mask, A, 0.0)
    monotone = True
    prev = None
    for _ in range(400):
        S = E + (A - B) @ P @ (A - B).T
        val = 0.5 * (ld(S) - ld(E))         # objective at the current B (guard only)
        if prev is not None and val - prev > max(RTOL * max(abs(prev), abs(val)), ATOL):
            monotone = False
        prev = val
        Si = np.linalg.inv(S)
        H = np.kron(P, Si)                 # acts on vec(B) column-major
        g = (np.kron(P, Si) @ A.flatten(order='F'))
        sel = mask.flatten(order='F')
        Hs = H[np.ix_(sel, sel)]; gs = g[sel]
        b = np.linalg.solve(Hs, gs)
        Bn = np.zeros(n * n); Bn[sel] = b
        B = Bn.reshape((n, n), order='F')
    alt = 0.5 * (ld(E + (A - B) @ P @ (A - B).T) - ld(E))
    if alt - prev > max(RTOL * max(abs(prev), abs(alt)), ATOL):
        monotone = False
    return bfgs, alt, monotone


def analyse(A, E, starts=8):
    n = A.shape[0]
    P = solve_discrete_lyapunov(A, E)
    kept = alt_all = bfgs_all = np.inf
    monotone = True
    for M in bipartitions(n):
        bfgs, alt, mono = J_pi(A, E, P, M, starts)
        kept = min(kept, min(bfgs, alt))     # the value of the original check
        alt_all = min(alt_all, alt)
        bfgs_all = min(bfgs_all, bfgs)
        monotone &= mono
    return kept, alt_all, bfgs_all, monotone


def mk(n, edges, c=0.3, a=0.2):
    A = np.eye(n) * a
    for i, j in edges:
        A[i, j] = c; A[j, i] = c
    return A


# J as the original check printed it (seven decimals); version 1.0 cited only the agreement
archived = {'ring': '0.2212930', 'star': '0.1134987', 'path': '0.1058709', 'split': '0.0000000'}
ex = {'ring': [(0, 1), (1, 2), (2, 3), (3, 0)], 'star': [(0, 1), (0, 2), (0, 3)],
      'path': [(0, 1), (1, 2), (2, 3)], 'split': [(0, 1), (2, 3)]}
ok = True
print("== Segundo optimizador de la tabla 6 (c=0.3, a=0.2, E=I; semilla 1811, 12 reinicios): J por red")
for k, e in ex.items():
    kept, alt, bfgs, monotone = analyse(mk(4, e), np.eye(4), starts=12)
    agree = all(abs(round(v, 7) - float(archived[k])) < 1e-12 for v in (kept, alt, bfgs))
    ok &= agree and monotone
    print(f"  {k:6s} conservado={kept:.7f}  alterno={alt:.7f}  BFGS={bfgs:.7f}  archivado={archived[k]}  "
          f"coincide a siete decimales: {'sí' if agree else 'NO'}  "
          f"el esquema alterno no aumenta el objetivo: {'sí' if monotone else 'NO'}")
print("TODAS LAS COMPROBACIONES:", "sí" if ok else "NO")
raise SystemExit(0 if ok else 1)
