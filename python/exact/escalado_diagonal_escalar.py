"""Checks for part (b) of the Proposition on monotonicity under scaling (Section 6 of the paper):
fixed SCALAR self-coupling, scaled couplings.
A(c) = a I + c W, |a| < 1, W with zero diagonal, E > 0, Q(c) = c^2 P(c).
(1) Exact polynomial identity (SymPy, generic symbolic 3x3 W, P, E):
      S := W Q A^T + A Q W^T + 2 c E
         = c [ (1 - a^2) P + c^2 W P W^T + E ] + c (A P A^T + E - P),
    so S = c[(1-a^2)P + c^2 W P W^T + E] > 0 whenever P solves the Lyapunov equation.
(2) Exact check, on a rational 2x2 instance with symbolic c, that Q' = A Q' A^T + S
    (differentiating Q = A Q A^T + c^2 E), hence Q' = sum_j A^j S A^{jT} > 0.
(3) Numerical illustration (not a certificate): J(aI + cW) increases strictly in c for
    P4, C4, P5, C5 (a = 0.2, E = I) and for random connected W with random E.
Run: python3 -I escalado_diagonal_escalar.py"""
import itertools
import numpy as np
import sympy as sp
from scipy.optimize import minimize
from scipy.linalg import solve_discrete_lyapunov

OK = True


def check(name, cond):
    global OK
    OK = OK and bool(cond)
    print(f"[{'ok' if cond else 'FALLO'}] {name}")


# ---------------- (1) generic symbolic identity, n = 3 ----------------
a, c = sp.symbols('a c', real=True)
w = sp.symbols('w12 w13 w21 w23 w31 w32', real=True)
W = sp.Matrix([[0, w[0], w[1]], [w[2], 0, w[3]], [w[4], w[5], 0]])
p = sp.symbols('p11 p12 p13 p22 p23 p33', real=True)
P = sp.Matrix([[p[0], p[1], p[2]], [p[1], p[3], p[4]], [p[2], p[4], p[5]]])
e = sp.symbols('e11 e12 e13 e22 e23 e33', real=True)
E = sp.Matrix([[e[0], e[1], e[2]], [e[1], e[3], e[4]], [e[2], e[4], e[5]]])
I3 = sp.eye(3)
A = a * I3 + c * W
Q = c**2 * P
S = W * Q * A.T + A * Q * W.T + 2 * c * E
RHS = c * ((1 - a**2) * P + c**2 * W * P * W.T + E) + c * (A * P * A.T + E - P)
check("(1) S = c[(1-a^2)P + c^2 W P W^T + E] + c (A P A^T + E - P)  (generic 3x3, exact)",
      sp.expand(S - RHS) == sp.zeros(3, 3))

# ---------------- (2) Q' = A Q' A^T + S on a rational 2x2 instance ----------------
cc = sp.symbols('c', positive=True)
a0 = sp.Rational(1, 5)
W2 = sp.Matrix([[0, sp.Rational(1, 2)], [sp.Rational(-1, 3), 0]])
E2 = sp.Matrix([[2, sp.Rational(1, 2)], [sp.Rational(1, 2), 1]])
A2 = a0 * sp.eye(2) + cc * W2
q11, q12, q22 = sp.symbols('q11 q12 q22')
Pg = sp.Matrix([[q11, q12], [q12, q22]])
sol = sp.solve(list(A2 * Pg * A2.T + E2 - Pg), [q11, q12, q22], dict=True)
check("(2) unique symmetric Lyapunov solution (symbolic c)", len(sol) == 1)
P2 = sp.simplify(Pg.subs(sol[0]))
Q2 = sp.simplify(cc**2 * P2)
dQ = sp.simplify(sp.diff(Q2, cc))
S2 = W2 * Q2 * A2.T + A2 * Q2 * W2.T + 2 * cc * E2
check("(2) Q'(c) = A Q'(c) A^T + S(c)  (exact, symbolic c)",
      sp.simplify(dQ - (A2 * dQ * A2.T + S2)) == sp.zeros(2, 2))
S2f = sp.simplify(cc * ((1 - a0**2) * P2 + cc**2 * W2 * P2 * W2.T + E2))
check("(2) S(c) = c[(1-a^2)P + c^2 W P W^T + E]  (exact, symbolic c)",
      sp.simplify(S2 - S2f) == sp.zeros(2, 2))

# ---------------- (3) numerical monotonicity in c ----------------
rng = np.random.default_rng(11)


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


def J(Am, Em, restarts=4):
    n = Am.shape[0]
    Pm = solve_discrete_lyapunov(Am, Em)
    ld = lambda X: np.linalg.slogdet(X)[1]
    best = np.inf
    for M in bipartitions(n):
        mask = np.array([[(i in M) == (j in M) for j in range(n)] for i in range(n)])
        idx = np.argwhere(mask)

        def f(v):
            B = np.zeros((n, n))
            B[idx[:, 0], idx[:, 1]] = v
            return 0.5 * (ld(Em + (Am - B) @ Pm @ (Am - B).T) - ld(Em))
        for v0 in [Am[idx[:, 0], idx[:, 1]]] + [Am[idx[:, 0], idx[:, 1]] + rng.normal(0, 0.4, len(idx))
                                                for _ in range(restarts)]:
            r = minimize(f, v0, method='BFGS', options={'gtol': 1e-12, 'maxiter': 20000})
            best = min(best, r.fun)
    return best


def adj(n, edges):
    Wm = np.zeros((n, n))
    for i, j in edges:
        Wm[i, j] = 1.0
        Wm[j, i] = 1.0
    return Wm


cases = {
    'P4': (adj(4, [(0, 1), (1, 2), (2, 3)]), np.eye(4)),
    'C4': (adj(4, [(0, 1), (1, 2), (2, 3), (3, 0)]), np.eye(4)),
    'P5': (adj(5, [(0, 1), (1, 2), (2, 3), (3, 4)]), np.eye(5)),
    'C5': (adj(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]), np.eye(5)),
}
for k in range(4):
    while True:
        Wr = rng.normal(0, 1, (4, 4)) * (rng.random((4, 4)) < 0.6)
        np.fill_diagonal(Wr, 0.0)
        g = (np.abs(Wr) + np.abs(Wr.T)) > 0
        seen, todo = {0}, [0]
        while todo:
            v = todo.pop()
            for u in np.nonzero(g[v])[0]:
                if int(u) not in seen:
                    seen.add(int(u))
                    todo.append(int(u))
        if len(seen) == 4:
            break
    G = rng.normal(0, 1, (4, 4))
    cases[f'aleat{k}'] = (Wr, G @ G.T + 0.3 * np.eye(4))
a_num = 0.2
for name, (Wm, Em) in cases.items():
    # admissible interval: rho(aI + cW) < 1; take c up to 90% of its right end
    cs = np.linspace(0.01, 3.0, 600)
    cmax = max(cv for cv in cs if max(abs(np.linalg.eigvals(a_num * np.eye(len(Wm)) + cv * Wm))) < 1)
    grid = np.linspace(0.08, 0.9, 6) * cmax
    vals = [J(a_num * np.eye(len(Wm)) + cv * Wm, Em) for cv in grid]
    inc = all(vals[i + 1] > vals[i] + 1e-9 for i in range(len(vals) - 1))
    check(f"(3) {name}: J(aI + cW) strictly increasing in c on a 6-point grid  "
          + ", ".join(f"{v:.5f}" for v in vals), inc)

print("TODAS LAS COMPROBACIONES:", "sí" if OK else "NO")
