# -*- coding: utf-8 -*-
"""
Familia gaussiana restringida F0 (Seccion 5 del articulo), puntos (1) y (2), que corresponden a los
puntos (G1) y (G2) de la Seccion 5.  Comprobacion exacta con SymPy.

Familia F0: X_{t+1} = A X_t + eps_{t+1},  A = [[0, c], [0, 0]],
            E = Cov(eps) = diag(s1, s2),  c >= 0,  s1, s2 > 0.
Funcional residual J (Seccion 3 del articulo, Lema 'Gaussian integration and connectivity'):
  J = min_B 1/2 log[ det(E + (A-B) P (A-B)^T) / det E ],
  B desconectada para la biparticion {1}|{2}, es decir B = diag(x, y).
log es el logaritmo natural (nats).  J es un funcional auxiliar de la ley del
proceso; NO se identifica con Phi_Q (Seccion 5 del articulo).

Todo es simbolico/exacto; no hay optimizacion numerica.  Ejecutar con
  python3 -I v12_familia_escala.py
"""
import sympy as sp

N_OK = 0


def check(name, cond):
    global N_OK
    cond = bool(cond)
    print(("OK   " if cond else "FAIL ") + name)
    assert cond, name
    N_OK += 1


def zero(expr):
    return sp.simplify(sp.expand(expr)) == 0


def zeromat(Mx):
    return all(zero(e) for e in Mx)


print("SymPy", sp.__version__)

c = sp.Symbol('c', nonnegative=True)
s1, s2 = sp.symbols('s1 s2', positive=True)
x, y = sp.symbols('x y', real=True)

A = sp.Matrix([[0, c], [0, 0]])
E = sp.diag(s1, s2)
p = s1 + c**2 * s2           # p = s1 + c^2 s2, la entrada P11 de la covarianza estacionaria
k = c**2 * s2 / s1           # k = c^2 s2 / s1

print("\n== (1a) Covarianza estacionaria ==")
p11, p12, p22 = sp.symbols('p11 p12 p22')
Pg = sp.Matrix([[p11, p12], [p12, p22]])
sol = sp.solve(list(A * Pg * A.T + E - Pg), [p11, p12, p22], dict=True)
check("ecuacion de Lyapunov P = A P A^T + E: solucion simetrica unica", len(sol) == 1)
P = Pg.subs(sol[0])
check("P = diag(s1 + c^2 s2, s2)", zeromat(P - sp.diag(p, s2)))
check("A nilpotente: A^2 = 0, luego P = E + A E A^T (serie finita)",
      A**2 == sp.zeros(2) and zeromat(E + A * E * A.T - P))
check("P definida positiva (s1 + c^2 s2 > 0, s2 > 0)", sp.ask(sp.Q.positive(p)) and sp.ask(sp.Q.positive(s2)))

print("\n== (1b) Determinante residual para B = diag(x, y) ==")
B = sp.diag(x, y)
Mres = A - B
f = sp.expand((E + Mres * P * Mres.T).det())
target = sp.expand(s2 * p + s2 * p * x**2 + s1 * s2 * y**2 + s2 * p * x**2 * y**2)
print("det =", sp.factor(f))
check("det(E+(A-B)P(A-B)^T) = s2 p + s2 p x^2 + s1 s2 y^2 + s2 p x^2 y^2", zero(f - target))
# La misma identidad escrita como s2 p + s2 [x^2 p (1 + y^2) + y^2 s1] (punto (G1) de la Seccion 5):
a_, d_ = x, y
f_M = s2 * (s1 + c**2 * s2) + s2 * (a_**2 * (s1 + c**2 * s2) * (1 + d_**2) + d_**2 * s1)
check("coincide con s2 p + s2 [x^2 p (1+y^2) + y^2 s1] (forma del punto (G1))", zero(f - f_M))

print("\n== (1c) Minimo global y unico en x = y = 0 ==")
f0 = f.subs({x: 0, y: 0})
dec = x**2 * (s2 * p * (1 + y**2)) + y**2 * (s1 * s2)
check("f(x,y) - f(0,0) = x^2 * s2 p (1+y^2) + y^2 * s1 s2  (identidad)", zero(f - f0 - dec))
check("coeficientes s2 p (1+y^2) > 0 y s1 s2 > 0 para todo y real",
      sp.ask(sp.Q.positive(s2 * p * (1 + y**2))) and sp.ask(sp.Q.positive(s1 * s2)))
print("  => f(x,y) >= f(0,0) con igualdad si y solo si x = 0 e y = 0;"
      " log es estrictamente creciente, asi que el minimizador de J es el mismo.")
# Advertencia: la unicidad global NO procede de convexidad.
H = sp.hessian(f, (x, y))
detH = sp.expand(H.det())
val = detH.subs({c: 1, s1: 1, s2: 1, x: 1, y: 1})
check("el objetivo no es convexo conjuntamente: det Hess(f)(1,1) = %s < 0 con c=s1=s2=1" % val, val < 0)
g = sp.log(f / E.det()) / 2
Hg = sp.hessian(g, (x, y)).subs({c: 1, s1: 1, s2: 1, x: 1, y: 1})
valg = sp.nsimplify(sp.simplify(Hg.det()))
check("tampoco el objetivo logaritmico: det Hess(J-objetivo)(1,1) = %s < 0" % valg, valg < 0)

print("\n== (1d) Valor de J ==")
ratio = sp.simplify(f0 / E.det())
check("min det / det E = p / s1 = 1 + k, con k = c^2 s2 / s1", zero(ratio - (1 + k)))
J = sp.log(1 + k) / 2
print("  J = 1/2 log(1 + k),  k = c^2 s2 / s1")

print("\n== (1e) Extra: conductor blanco con coeficiente interno del receptor a (vease el punto (G7)) ==")
a = sp.Symbol('a', real=True)
Aa = sp.Matrix([[a, c], [0, 0]])
sola = sp.solve(list(Aa * Pg * Aa.T + E - Pg), [p11, p12, p22], dict=True)
check("Lyapunov con receptor a: solucion unica", len(sola) == 1)
Pa = Pg.subs(sola[0])
check("Pa = diag((s1 + c^2 s2)/(1 - a^2), s2)", zeromat(Pa - sp.diag((s1 + c**2 * s2) / (1 - a**2), s2)))
fa = sp.expand((E + (Aa - B) * Pa * (Aa - B).T).det())
deca = s2 * ((a - x)**2 * Pa[0, 0] * (1 + y**2) + y**2 * s1)
check("fa(x,y) - s2(s1 + c^2 s2) = s2[(a-x)^2 Pa11 (1+y^2) + y^2 s1]", zero(fa - s2 * p - deca))
print("  Con |a| < 1, Pa11 > 0: minimo unico en x = a, y = 0;"
      " J = 1/2 log(1+k), independiente de a.")

print("\n== (1f) Valores numericos del punto (G1) de la Seccion 5 ==")
for s2v, Jexp in [(1, sp.log(2) / 2), (3, sp.log(2))]:
    Jv = sp.log(1 + sp.Integer(1)**2 * s2v / 1) / 2
    check("(G1): c = s1 = 1, s2 = %d -> J = %s" % (s2v, Jexp), zero(sp.expand_log(Jv - Jexp)))
cv, s1v, s2v = sp.Rational(13, 10), sp.Rational(7, 10), sp.Rational(19, 10)
kv = cv**2 * s2v / s1v
Jnats = sp.log(1 + kv) / 2
nats = sp.N(Jnats, 20)
bits = sp.N(Jnats / sp.log(2), 20)
print("  (c,s1,s2) = (1.3, 0.7, 1.9): k = %s, 1+k = %s" % (kv, 1 + kv))
print("  J = %s nats = %s bits" % (nats, bits))
check("(G1): J = 0.86023 nats (5 decimales)", abs(nats - sp.Float('0.86023')) < sp.Float('5e-6'))
check("(G1): J = 1.24106 bits (5 decimales)", abs(bits - sp.Float('1.24106')) < sp.Float('5e-6'))

print("\n== (2) Invariancia de k por reescalado X1' = alpha X1, X2' = beta X2 (alpha, beta > 0) ==")
al, be = sp.symbols('alpha beta', positive=True)
D = sp.diag(al, be)
A2 = D * A * D.inv()
E2 = D * E * D
P2 = D * P * D
check("A' = D A D^-1 = [[0, alpha c / beta], [0, 0]]", zeromat(A2 - sp.Matrix([[0, al * c / be], [0, 0]])))
check("E' = D E D = diag(alpha^2 s1, beta^2 s2)", zeromat(E2 - sp.diag(al**2 * s1, be**2 * s2)))
check("P' = D P D resuelve la ecuacion de Lyapunov de (A', E')", zeromat(A2 * P2 * A2.T + E2 - P2))
c2, s1_2, s2_2 = A2[0, 1], E2[0, 0], E2[1, 1]
k2 = c2**2 * s2_2 / s1_2
check("k' = c'^2 s2' / s1' = k", zero(k2 - k))
Ncov, Ncov2 = c**2 * s2, c2**2 * s2_2
check("N = c^2 s2 es covariante: N' = alpha^2 N (no invariante)", zero(Ncov2 - al**2 * Ncov))
check("para todo B diagonal: D (A - B) D^-1 = A' - B", zeromat(D * (A - B) * D.inv() - (A2 - B)))
f2 = (E2 + (A2 - B) * P2 * (A2 - B).T).det()
check("cociente det(E'+(A'-B)P'(A'-B)^T)/det E' = cociente original, para todo (x, y)",
      zero(f2 / E2.det() - f / E.det()))
print("  => J es invariante, y tambien el objetivo entero (no solo su minimo).")

print("\n== (2b) Cambios de signo ==")
als, bes = sp.symbols('alpha_s beta_s', real=True, nonzero=True)
Ds = sp.diag(als, bes)
A3, E3 = Ds * A * Ds.inv(), Ds * E * Ds
k3 = A3[0, 1]**2 * E3[1, 1] / E3[0, 0]
check("con alpha, beta reales no nulos k' = k igualmente (cuadrados)", zero(k3 - k))
print("  c' = alpha c / beta; si c > 0, c' >= 0 exige alpha beta > 0 (la familia pide c >= 0):"
      " solo el cambio global de signo (alpha, beta < 0) permanece en la familia;"
      " si c = 0, cualquier combinacion de signos.")

print("\n== (2c) Normalizacion Z_i = X_i / sqrt(s_i) ==")
Dn = sp.diag(1 / sp.sqrt(s1), 1 / sp.sqrt(s2))
AZ, EZ, PZ = Dn * A * Dn.inv(), Dn * E * Dn, Dn * P * Dn
check("ruido normalizado: Cov(eta) = I", zeromat(EZ - sp.eye(2)))
check("acoplamiento normalizado: A_Z = [[0, sqrt(k)], [0, 0]] (c >= 0)",
      zeromat(AZ - sp.Matrix([[0, sp.sqrt(k)], [0, 0]])))
check("Cov(Z) estacionaria = diag(1 + k, 1) (solo depende de k)", zeromat(PZ - sp.diag(1 + k, 1)))

print("\n== Biyeccion k <-> J ==")
Jk = sp.Symbol('J', nonnegative=True)
kk = sp.Symbol('k', nonnegative=True)
check("dJ/dk = 1/(2(1+k)) > 0: J estrictamente creciente en k >= 0",
      zero(sp.diff(sp.log(1 + kk) / 2, kk) - 1 / (2 * (1 + kk))))
inv = sp.solve(sp.Eq(sp.log(1 + kk) / 2, Jk), kk)
check("inversa unica k = exp(2J) - 1", len(inv) == 1 and zero(inv[0] - (sp.exp(2 * Jk) - 1)))

print("\nTotal de comprobaciones superadas: %d" % N_OK)
