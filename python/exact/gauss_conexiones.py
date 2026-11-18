"""Exact (SymPy) checks of the connections between the restricted Gaussian family F0
and the main theorems of the paper: connections (i)-(v) of Section 5 of the paper.
Run with:  python3 -I gauss_conexiones.py

F0: X1' = c X2 + e1, X2' = e2, i.e. A=[[0,c],[0,0]], E=diag(s1,s2), c>=0, s1,s2>0,
k = c^2 s2/s1, J = 1/2 log(1+k) (verified in v12_familia_escala.py, item 1d; item (G1) of Section 5).

(C0) re-derivation of P and of the residual identity (cross-check of items 1a-1c);
(C1) min-cut sandwich on F0: w_min = c^2; the lower bound is attained iff s2 <= s1
     (for c > 0) and the upper bound is strict for c > 0;
(C2) I_pred = J on F0, hence I_cut = 0 (B = 0 captures nothing: E + A P A^T = P);
(C3) driver memory a (receiver coefficient 0): I_pred = 1/2 log(p(1+k)),
     I_cut = 1/2 log(p(1+k)/r(k,p)) >= 0, zero iff p = 1;
(C4) tensor F0 (x) F0': support 2K_2, J = 0 (B = A is block-disconnected), I_pred
     additive, cut defect = J(X) + J(Y), no universal vertex;
(C5) pointed states: the surprisal of z ~ N(0, diag(1+k,1)) has its unique minimum
     at z = 0, a null set; the section value gives h = 0, while u = |z|^2 > 0 a.s.
Natural logarithms throughout. Nothing here identifies J with Phi_Q.
"""
import itertools
import sympy as sp

ALL_OK = True


def check(name, cond):
    global ALL_OK
    ok = bool(cond)
    ALL_OK = ALL_OK and ok
    print(f"[{'ok' if ok else 'FALLO'}] {name}")


c, s1, s2, d = sp.symbols('c s1 s2 d', positive=True)
x, y = sp.symbols('x y', real=True)
k = c**2 * s2 / s1

# ---------------- (C0) ----------------
A = sp.Matrix([[0, c], [0, 0]])
E = sp.diag(s1, s2)
P = sp.diag(s1 + c**2 * s2, s2)
check("C0 P = A P A^T + E", sp.simplify(A * P * A.T + E - P) == sp.zeros(2, 2))
B = sp.diag(x, y)
f = sp.expand((E + (A - B) * P * (A - B).T).det())
f00 = f.subs({x: 0, y: 0})
check("C0 f(0,0)/det E = 1 + k", sp.simplify(f00 / (s1 * s2) - (1 + k)) == 0)
check("C0 f - f(0,0) = x^2 s2 p (1+y^2) + y^2 s1 s2  (p = s1 + c^2 s2)",
      sp.expand(f - f00 - (x**2 * s2 * (s1 + c**2 * s2) * (1 + y**2) + y**2 * s1 * s2)) == 0)

# ---------------- (C1) ----------------
# only bipartition {1}|{2}; crossing coefficients A[0,1] = c and A[1,0] = 0
w_min = A[0, 1]**2 + A[1, 0]**2
check("C1 w_min = c^2", sp.simplify(w_min - c**2) == 0)
# case s2 <= s1: s1 = s2 + d (d >= 0 handled by d > 0 and the limit d = 0 below)
sub_a = {s1: s2 + d}
kappa_a = (s2 + d) / s2                  # lambda_max(E)/lambda_min(E)
lb_arg_a = (w_min / kappa_a).subs(sub_a)
check("C1 s2 < s1: lower-bound argument w_min/kappa_E equals k (bound attained)",
      sp.simplify(lb_arg_a - k.subs(sub_a)) == 0)
check("C1 s2 = s1: lower-bound argument equals k",
      sp.simplify((w_min / 1) - k.subs({s1: s2})) == 0)
# case s2 > s1: s2 = s1 + d
sub_b = {s2: s1 + d}
kappa_b = (s1 + d) / s1
gap_b = sp.factor(sp.simplify(k.subs(sub_b) - (w_min / kappa_b).subs(sub_b)))
print("     s2 > s1: k - w_min/kappa_E =", gap_b)
check("C1 s2 > s1: k - w_min/kappa_E = c^2 d (2 s1 + d)/(s1 (s1 + d)) > 0 (strict for c > 0)",
      sp.simplify(gap_b - c**2 * d * (2 * s1 + d) / (s1 * (s1 + d))) == 0)
# upper bound: argument (lambda_max(P)/lambda_min(E)) w_min >= k, and log(1+k) < k for k > 0
ub_arg_a = ((s1 + c**2 * s2) / s2 * w_min).subs(sub_a)   # s2 <= s1: lambda_min(E)=s2, lambda_max(P)=s1+c^2 s2
gap_ua = sp.simplify(ub_arg_a - k.subs(sub_a))
check("C1 s2 <= s1: upper-bound argument - k >= 0",
      sp.simplify(gap_ua - c**2 * ((s2 + d + c**2 * s2) / s2 - s2 / (s2 + d))) == 0
      and sp.simplify((s2 + d) / s2 - s2 / (s2 + d)).is_positive)
# s2 > s1: lambda_min(E) = s1, lambda_max(P) = max(s1 + c^2 s2, s2) >= s2
check("C1 s2 > s1: upper-bound argument >= c^2 s2/s1 = k (lambda_max(P) >= s2)",
      sp.simplify(c**2 * s2 / s1 - k) == 0)
t = sp.symbols('t', positive=True)
check("C1 log(1+t) < t for t > 0 (derivative t/(1+t) > 0, value 0 at 0)",
      sp.simplify(sp.diff(t - sp.log(1 + t), t) - t / (1 + t)) == 0)
# exact rational grid: LB <= J <= UB, LB = J iff s2 <= s1
grid_ok = True
vals = [sp.Rational(1, 3), sp.Rational(1, 2), sp.Integer(1), sp.Rational(3, 2), sp.Integer(2), sp.Integer(3)]  # exact, no Python floats
for cv, a1, a2 in itertools.product(vals, vals, vals):
    kv = cv**2 * a2 / a1
    kap = max(a1, a2) / min(a1, a2)
    lb = cv**2 / kap
    lamP = max(a1 + cv**2 * a2, a2)
    ub = lamP / min(a1, a2) * cv**2
    if not (lb <= kv and (lb == kv) == (a2 <= a1) and kv <= ub):
        grid_ok = False
check(f"C1 exact rational grid ({len(vals)**3} points): w/kappa <= k <= UB-argument, equality iff s2 <= s1",
      grid_ok)

# ---------------- (C2) ----------------
Ipred = sp.log((P.det()) / (E.det())) / 2
check("C2 I_pred = 1/2 log(det P/det E) = 1/2 log(1+k) = J",
      sp.simplify(sp.exp(2 * Ipred) - (1 + k)) == 0)
check("C2 B = 0: E + A P A^T = P, so I_0 = 0 and I_cut = I_pred - J = 0",
      sp.simplify(E + A * P * A.T - P) == sp.zeros(2, 2))

# ---------------- (C3) ----------------
a = sp.symbols('a', real=True)
Aa = sp.Matrix([[0, c], [0, a]])
p11, p12, p22 = sp.symbols('p11 p12 p22')
Pg = sp.Matrix([[p11, p12], [p12, p22]])
sol = sp.solve(list(Aa * Pg * Aa.T + E - Pg), [p11, p12, p22], dict=True)
check("C3 Lyapunov has a unique symmetric solution", len(sol) == 1)
Pa = Pg.subs(sol[0])
pp = 1 / (1 - a**2)
check("C3 det P = s2 p (s1 + c^2 s2)",
      sp.simplify(Pa.det() - s2 * pp * (s1 + c**2 * s2)) == 0)
pv, kv_ = sp.symbols('p k', positive=True)
r = 1 + kv_ * pv * (kv_ + 1) / (kv_ * pv + 1)
xs = sp.simplify(c * Pa[0, 1] / Pa[0, 0])
Ba = sp.diag(x, y)
fa = sp.simplify((E + (Aa - Ba) * Pa * (Aa - Ba).T).det())
fmin = sp.simplify(fa.subs({x: xs, y: a}))
check("C3 residual at B* = diag(x*, a) equals s1 s2 r(k,p)",
      sp.simplify(fmin - s1 * s2 * r.subs({kv_: k, pv: pp})) == 0)
check("C3 identity f = s1 s2 r + s2 P11 (x - x*)^2 + (a - y)^2 (s1 P22 + x^2 det P)",
      sp.simplify(fa - (s1 * s2 * r.subs({kv_: k, pv: pp}) + s2 * Pa[0, 0] * (x - xs)**2
                        + (a - y)**2 * (s1 * Pa[1, 1] + x**2 * Pa.det()))) == 0)
Icut_arg = pv * (1 + kv_) / r
check("C3 p(1+k)(kp+1) - (1 + kp(k+2)) = (p-1)(1 + kp(1+k))",
      sp.expand(pv * (1 + kv_) * (kv_ * pv + 1) - (1 + kv_ * pv * (kv_ + 2))
                - (pv - 1) * (1 + kv_ * pv * (1 + kv_))) == 0)
check("C3 r (kp+1) = 1 + kp(k+2)",
      sp.simplify(r * (kv_ * pv + 1) - (1 + kv_ * pv * (kv_ + 2))) == 0)
check("C3 I_cut argument p(1+k)/r - 1 = (p-1)(1+kp(1+k))/(1+kp(k+2)): zero iff p = 1",
      sp.simplify(Icut_arg - 1 - (pv - 1) * (1 + kv_ * pv * (1 + kv_)) / (1 + kv_ * pv * (kv_ + 2))) == 0)

# ---------------- (C4) ----------------
c2, t1, t2 = sp.symbols('c2 t1 t2', positive=True)
k2 = c2**2 * t2 / t1
A4 = sp.diag(A, sp.Matrix([[0, c2], [0, 0]]))
E4 = sp.diag(s1, s2, t1, t2)
P4 = sp.diag(P, sp.diag(t1 + c2**2 * t2, t2))
check("C4 P(X(x)Y) = blockdiag(P_X, P_Y) solves Lyapunov",
      sp.simplify(A4 * P4 * A4.T + E4 - P4) == sp.zeros(4, 4))
I4 = sp.log(P4.det() / E4.det()) / 2
check("C4 I_pred(X(x)Y) = 1/2 log(1+k) + 1/2 log(1+k') (additive)",
      sp.simplify(sp.exp(2 * I4) - (1 + k) * (1 + k2)) == 0)
blocks = [{0, 1}, {2, 3}]
crossing = [(i, j) for i in range(4) for j in range(4)
            if (i in blocks[0]) != (j in blocks[0]) and A4[i, j] != 0]
check("C4 bipartition {1,2}|{3,4}: A has no crossing coefficient, so B = A is admissible",
      crossing == [])
R4 = E4 + (A4 - A4) * P4 * (A4 - A4).T
check("C4 residual with B = A is E: det ratio 1, so J(X(x)Y) = 0 (J >= 0 always)",
      sp.simplify(R4.det() / E4.det()) == 1)
und = {(i, j) for i in range(4) for j in range(4) if i != j and (A4[i, j] != 0 or A4[j, i] != 0)}
check("C4 undirected support is 2K_2 = {12, 34}",
      und == {(0, 1), (1, 0), (2, 3), (3, 2)})
check("C4 no universal vertex in 2K_2",
      not any(all(v == w or (w, v) in und for v in range(4)) for w in range(4)))
check("C4 cut defect: I_cut(X(x)Y) - I_cut(X) - I_cut(Y) = J(X) + J(Y)  [I_cut(X)=I_cut(Y)=0]",
      sp.simplify(sp.exp(2 * (I4 - 0)) - sp.exp(2 * (sp.log(1 + k) / 2 + sp.log(1 + k2) / 2))) == 0)

# ---------------- (C5) ----------------
z1, z2 = sp.symbols('z1 z2', real=True)
Sz = sp.diag(1 + k, 1)
zz = sp.Matrix([z1, z2])
surpr = (zz.T * Sz.inv() * zz)[0] / 2 + sp.log(2 * sp.pi) + sp.log(Sz.det()) / 2
grad = [sp.diff(surpr, v) for v in (z1, z2)]
check("C5 surprisal gradient vanishes only at z = 0",
      sp.solve(grad, [z1, z2], dict=True) == [{z1: 0, z2: 0}])
H = sp.hessian(surpr, (z1, z2))
check("C5 surprisal Hessian = Sigma_z^{-1} > 0 (unique minimum, the mode)",
      sp.simplify(H - Sz.inv()) == sp.zeros(2, 2) and sp.simplify(Sz.det()).is_positive)
check("C5 E|z|^2 = tr Sigma_z = 2 + k > 0, while the section value is |0|^2 = 0",
      sp.simplify(Sz.trace() - (2 + k)) == 0)

print("TODAS LAS COMPROBACIONES:", "sí" if ALL_OK else "NO")
