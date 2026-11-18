"""Numerical illustration (not a certificate) of part (a) of the Proposition on monotonicity
under scaling (Section 6 of the paper), which is proved analytically there:
for a stable (A,E) and t in [0, 1/rho(A)), J(tA) is nondecreasing in t, and strictly
increasing when the undirected support of A is connected.
Proof idea (on paper): P_t = sum_j t^{2j} A^j E A^{jT} is Loewner-nondecreasing; with
B = tB' (B' in the same block subspace) the residual is E + t^2 (A-B') P_t (A-B')^T,
nondecreasing in t for every B'; min over B' and over bipartitions preserves it.
Deformation t -> tA keeps the support, so P_n (n >= 4) stays in the band.
Checks: (1) Loewner monotonicity of P_t; (2) J(tA) increasing on a grid for P4, C4,
P5, C5, P6 (diagonal 0.2, couplings 0.3, E = I) and for random connected systems
with random E; (3) w_min(tA) = t^2 w_min(A).  Run: python3 -I monotonia_escalado.py"""
import itertools
import numpy as np
from scipy.optimize import minimize
from scipy.linalg import solve_discrete_lyapunov

rng = np.random.default_rng(20261118)


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


def ld(X):
    return np.linalg.slogdet(X)[1]


def J_and_wmin(A, E, restarts=4):
    n = A.shape[0]
    P = solve_discrete_lyapunov(A, E)
    best, wmin = np.inf, np.inf
    for M in bipartitions(n):
        mask = np.array([[(i in M) == (j in M) for j in range(n)] for i in range(n)])
        idx = np.argwhere(mask)
        wmin = min(wmin, float((np.where(mask, 0.0, A) ** 2).sum()))

        def f(v):
            B = np.zeros((n, n))
            B[idx[:, 0], idx[:, 1]] = v
            return 0.5 * (ld(E + (A - B) @ P @ (A - B).T) - ld(E))
        starts = [A[idx[:, 0], idx[:, 1]]] + [A[idx[:, 0], idx[:, 1]] + rng.normal(0, 0.4, len(idx))
                                              for _ in range(restarts)]
        for v0 in starts:
            r = minimize(f, v0, method='BFGS', options={'gtol': 1e-12, 'maxiter': 20000})
            best = min(best, r.fun)
    return best, wmin


def mk(n, edges, c=0.3, a=0.2):
    A = np.eye(n) * a
    for i, j in edges:
        A[i, j] = c
        A[j, i] = c
    return A


def connected(A):
    n = A.shape[0]
    adj = (np.abs(A) + np.abs(A.T) > 0) & ~np.eye(n, dtype=bool)
    seen, todo = {0}, [0]
    while todo:
        v = todo.pop()
        for w in np.nonzero(adj[v])[0]:
            if w not in seen:
                seen.add(int(w))
                todo.append(int(w))
    return len(seen) == n


ok = True
systems = {
    'P4': mk(4, [(0, 1), (1, 2), (2, 3)]),
    'C4': mk(4, [(0, 1), (1, 2), (2, 3), (3, 0)]),
    'P5': mk(5, [(0, 1), (1, 2), (2, 3), (3, 4)]),
    'C5': mk(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]),
    'P6': mk(6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]),
}
Es = {k: np.eye(v.shape[0]) for k, v in systems.items()}
for i in range(5):
    n = 4
    while True:
        A = rng.normal(0, 0.35, (n, n)) * (rng.random((n, n)) < 0.55)
        if connected(A):
            break
    rho = max(abs(np.linalg.eigvals(A)))
    if rho >= 0.9:
        A = A * 0.85 / rho
    G = rng.normal(0, 1, (n, n))
    systems[f'aleat{i}'] = A
    Es[f'aleat{i}'] = G @ G.T + 0.3 * np.eye(n)

print("== (1) Monotonía de Loewner de P_t (mínimo autovalor de P_t2 - P_t1)")
for name, A in systems.items():
    E = Es[name]
    rho = max(abs(np.linalg.eigvals(A)))
    ts = np.linspace(0.0, 0.95 / rho if rho > 0 else 2.0, 12)
    Ps = [solve_discrete_lyapunov(t * A, E) for t in ts]
    m = min(np.linalg.eigvalsh(Ps[k + 1] - Ps[k]).min() for k in range(len(ts) - 1))
    cond = m >= -1e-10
    ok &= cond
    print(f"{name:7s} rho={rho:.3f}  min eig(dP)={m:.3e}  {'sí' if cond else 'NO'}")

print("== (2)-(3) J(tA) creciente y w_min(tA) = t^2 w_min(A)")
for name, A in systems.items():
    E = Es[name]
    rho = max(abs(np.linalg.eigvals(A)))
    tmax = min(0.95 / rho, 3.0) if rho > 0 else 3.0
    ts = np.linspace(0.15, 1.0, 6) * tmax
    J0, w0 = J_and_wmin(A, E)
    vals = []
    wok = True
    for t in ts:
        Jt, wt = J_and_wmin(t * A, E)
        vals.append(Jt)
        wok &= abs(wt - t * t * w0) <= 1e-12 * max(1.0, w0)
    inc = all(vals[k + 1] > vals[k] + 1e-9 for k in range(len(vals) - 1))
    cond = inc and wok and connected(A)
    ok &= cond
    print(f"{name:7s} conexo={connected(A)}  J(tA)=" + ", ".join(f"{v:.5f}" for v in vals)
          + f"  estrictamente creciente={'sí' if inc else 'NO'}  w_min escala t^2={'sí' if wok else 'NO'}")

print("TODAS LAS COMPROBACIONES:", "sí" if ok else "NO")
