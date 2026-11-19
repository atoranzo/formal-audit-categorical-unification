"""Exact comparison (SymPy 1.14, rational arithmetic, no optimization) of J on two of the four-unit
networks of Section 5.4 of the paper: J(C4) > J(P4), the ring above the path.
Networks of Table 6 (Section 5.4): A = 0.2 I + 0.3 M_Gamma, with M_Gamma the adjacency matrix of the
graph Gamma on the units 0, 1, 2, 3 (the ring C4: edges 01, 12, 23, 30; the path P4: edges 01, 12,
23), and E = I; for a bipartition pi, A_cross(pi) is the part of A that couples the two blocks.
 (1) A is symmetric and E = I, so the stationary covariance is P = (I - A^2)^{-1}; P = A P A^T + E
     is checked exactly.
 (2) Upper bound for J(P4): the bipartition pi = {0}|{1,2,3} attains w_min(P4) = 9/50, and the
     predictor that the proof of Theorem 36 (the min-cut sandwich) takes there, B = A - A_cross(pi),
     has no coupling across pi, so
     J(P4) <= 1/2 log det(E + (A - B) P (A - B)^T) / det E = 1/2 log det(I + A_cross P A_cross^T),
     and this determinant is computed exactly: 637088/511841.
 (3) Lower bound for J(C4): the lower bound of Theorem 36, J >= 1/2 log(1 + w_min/kappa_E), with
     kappa_E = 1 for E = I and w_min the least ||A_cross(pi)||_F^2 over the seven bipartitions,
     computed exactly: w_min(C4) = 9/25, so J(C4) >= 1/2 log(34/25).
 (4) 637088/511841 < 34/25, exactly; hence J(P4) < J(C4).
The inequality of (3) is Theorem 36 of the paper (checked in Lean with Mathlib as QAudit.sandwich),
not recomputed here; this script computes its ingredients and the
comparison exactly. The values printed, 1/2 log(637088/511841) and 1/2 log(34/25), are evaluated
with mpmath's interval arithmetic (outward rounding) at 60 digits and compared with the six decimals
printed in the paper; the value of J(C4) printed in Table 6, an upper bound found numerically, is
checked to lie above the exact lower bound. Natural logarithms (nats).
Run: python3 -I anillo_frente_camino.py"""
import itertools

import mpmath
import sympy as sp

mpmath.mp.dps = 60
mpmath.iv.dps = 60

R = sp.Rational
N_UNITS = 4

RESULTS = []


def check(name, cond):
    cond = bool(cond)
    RESULTS.append(cond)
    print(f"[{'ok' if cond else 'FAIL'}] {name}")
    return cond


def network(edges, a=R(1, 5), c=R(3, 10)):
    M = sp.zeros(N_UNITS, N_UNITS)
    for i, j in edges:
        M[i, j] = M[j, i] = 1
    return a * sp.eye(N_UNITS) + c * M


def bipartitions():
    """The seven bipartitions {S, complement} of {0, 1, 2, 3}, each once: S runs over the nonempty
    subsets of {0, 1, 2}, and unit 3 is in the complement."""
    return [frozenset(S) for r in range(1, N_UNITS) for S in itertools.combinations(range(N_UNITS - 1), r)]


def show(S):
    T = sorted(set(range(N_UNITS)) - S)
    return '{%s}|{%s}' % (','.join(map(str, sorted(S))), ','.join(map(str, T)))


def cross(A, S):
    """A_cross(S | complement): the entries of A that couple the two blocks."""
    return sp.Matrix(N_UNITS, N_UNITS, lambda i, j: A[i, j] if ((i in S) != (j in S)) else 0)


def iv_half_log(q):
    v = mpmath.iv.log(mpmath.iv.mpf(int(q.p)) / mpmath.iv.mpf(int(q.q))) / 2
    return mpmath.mpf(v.a), mpmath.mpf(v.b)


E = sp.eye(N_UNITS)
C4 = network([(0, 1), (1, 2), (2, 3), (3, 0)])
P4 = network([(0, 1), (1, 2), (2, 3)])
PARTS = bipartitions()
check(f"seven bipartitions of four units, each once: {len(PARTS)}",
      len(PARTS) == len(set(PARTS)) == 7 and not ({frozenset(range(N_UNITS)) - S for S in PARTS} & set(PARTS)))

# (1) stationary covariances
P = {}
for name, A in (('C4', C4), ('P4', P4)):
    P[name] = (sp.eye(N_UNITS) - A ** 2).inv()
    check(f"{name}: P = (I - A^2)^-1 solves P = A P A^T + E exactly, P symmetric and positive definite",
          A * P[name] * A.T + E - P[name] == sp.zeros(N_UNITS, N_UNITS) and P[name] == P[name].T
          and all(P[name][:k, :k].det() > 0 for k in range(1, N_UNITS + 1)))

# (2) J(P4) <= 1/2 log det(I + A_cross P A_cross^T) for pi = {0}|{1,2,3}
S0 = frozenset({0})
w_P4 = {S: sum(cross(P4, S)[i, j] ** 2 for i in range(N_UNITS) for j in range(N_UNITS)) for S in PARTS}
check(f"P4: {show(S0)} attains w_min(P4) = {min(w_P4.values())} (exact): it is a cut of the proof of "
      f"Theorem 36", w_P4[S0] == min(w_P4.values()) == R(9, 50))
Ac = cross(P4, S0)
Bp = P4 - Ac
check("P4: B = A - A_cross({0}|{1,2,3}) has no coupling across the bipartition (B is in its predictor class)",
      all(Bp[i, j] == 0 for i in range(N_UNITS) for j in range(N_UNITS) if (i in S0) != (j in S0)))
ratio_P4 = (E + (P4 - Bp) * P['P4'] * (P4 - Bp).T).det() / E.det()
check(f"P4: det(E + (A - B) P (A - B)^T) / det E = {ratio_P4} (exact)", ratio_P4 == R(637088, 511841))

# (3) w_min(C4) over the seven bipartitions, exactly
w = {}
for S in PARTS:
    Ax = cross(C4, S)
    w[S] = sum(Ax[i, j] ** 2 for i in range(N_UNITS) for j in range(N_UNITS))
wmin = min(w.values())
others = [show(S) for S in PARTS if w[S] != wmin]
check(f"C4: w_min = min over the seven bipartitions of ||A_cross||_F^2 = {wmin} (exact), attained by "
      f"every bipartition but {' and '.join(others)}", wmin == R(9, 25))
kappa_E = 1  # lambda_max(E) / lambda_min(E) for E = I
bound_C4 = 1 + wmin / kappa_E
check(f"C4: 1 + w_min/kappa_E = {bound_C4} (kappa_E = 1 for E = I)", bound_C4 == R(34, 25))

# (4) the comparison, exactly
check(f"637088/511841 < 34/25 exactly ({637088 * 25} < {34 * 511841}): J(P4) < J(C4)",
      ratio_P4 < bound_C4)

up_lo, up_hi = iv_half_log(ratio_P4)
lo_lo, lo_hi = iv_half_log(bound_C4)
print(f"     J(P4) <= 1/2 log(637088/511841) in [{mpmath.nstr(up_lo, 15)}, {mpmath.nstr(up_hi, 15)}]")
print(f"     J(C4) >= 1/2 log(34/25)         in [{mpmath.nstr(lo_lo, 15)}, {mpmath.nstr(lo_hi, 15)}]")
check("the two bounds are 0.109447 and 0.153742 to six decimals, as printed in the paper",
      mpmath.mpf('0.1094465') <= up_lo and up_hi < mpmath.mpf('0.1094475')
      and mpmath.mpf('0.1537415') <= lo_lo and lo_hi < mpmath.mpf('0.1537425'))
check("the value 0.221293 of J(C4) in Table 6 (an upper bound found numerically) is above the exact "
      "lower bound 1/2 log(34/25)", lo_hi < mpmath.mpf('0.221293'))

ok = all(RESULTS)
print(f"checks passed: {sum(RESULTS)} of {len(RESULTS)}")
print("TODAS LAS COMPROBACIONES:", "sí" if ok else "NO")
raise SystemExit(0 if ok else 1)
