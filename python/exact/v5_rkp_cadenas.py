# -*- coding: utf-8 -*-
"""
Familia gaussiana restringida F0 (Seccion 5 del articulo), punto (5), que corresponde al punto (G7) de la
Seccion 5: familia con conductor con memoria y resultado condicional de constancia.  Comprobacion exacta
con SymPy; ejecutar con python3 -I.

Familia con conductor autorregresivo y coeficiente del receptor nulo:
  A = [[0, c], [0, a]],  |a| < 1,  E = diag(s1, s2),  k = c^2 s2 / s1 > 0,
  p = 1/(1 - a^2) >= 1.
Notacion: aqui a es el coeficiente propio del conductor, que la Seccion 5 del articulo llama a_22;
alpha, en (5h), es el coeficiente propio del receptor, que el articulo llama a.
G = min_{x,y} 1/2 log det(E + (A-B) P (A-B)^T)/det E, B = diag(x, y), retardo 1, nats;
G es el funcional J del articulo (Seccion 3) en esta familia.
Lo que se comprueba (punto (G7) de la Seccion 5): G = 1/2 log r(k, p), r = 1 + k p (k+1)/(k p + 1);
dr/dp > 0; rango [1+k, 2+k); p* = k'/(k(k+1-k')) >= 1 con r(k, p*) = 1 + k' = r(k', 1);
cadenas de pasos < 1.  IPS_K: u depende solo de k (la premisa IPS_K de la Seccion 5).
Nada de esto identifica G con Phi_Q ni atribuye unidad a estados sinteticos.
"""
import math
import sympy as sp

N_OK = 0


def check(name, cond):
    global N_OK
    cond = bool(cond)
    print(("OK   " if cond else "FAIL ") + name)
    assert cond, name
    N_OK += 1


def zero(e):
    return sp.simplify(sp.cancel(sp.together(sp.expand(e)))) == 0


def zeromat(Mx):
    return all(zero(e) for e in Mx)


def lyap(A, E):
    p11, p12, p22 = sp.symbols('p11 p12 p22')
    Pg = sp.Matrix([[p11, p12], [p12, p22]])
    sol = sp.solve(list(A * Pg * A.T + E - Pg), [p11, p12, p22], dict=True)
    assert len(sol) == 1
    return Pg.subs(sol[0]).applyfunc(sp.simplify)


print("SymPy", sp.__version__)
c = sp.Symbol('c', real=True)
s1, s2 = sp.symbols('s1 s2', positive=True)
a = sp.Symbol('a', real=True)
x, y = sp.symbols('x y', real=True)
A = sp.Matrix([[0, c], [0, a]])
E = sp.diag(s1, s2)
B = sp.diag(x, y)
p_a = 1 / (1 - a**2)
k_c = c**2 * s2 / s1

print("\n== (5a) Covarianza estacionaria con conductor AR ==")
P = lyap(A, E)
check("P22 = s2 p, P12 = c a s2 p, P11 = s1 + c^2 s2 p, p = 1/(1-a^2)",
      zeromat(P - sp.Matrix([[s1 + c**2 * s2 * p_a, c * a * s2 * p_a], [c * a * s2 * p_a, s2 * p_a]])))
detP = sp.simplify(P.det())
check("det P = s2 p (s1 + c^2 s2)", zero(detP - s2 * p_a * (s1 + c**2 * s2)))

print("\n== (5b) Minimo exacto y unico: G = 1/2 log r(k, p) ==")
f = sp.expand((E + (A - B) * P * (A - B).T).det())
K, Pp, Kp = sp.symbols('k p kprime', positive=True)
r = 1 + K * Pp * (K + 1) / (K * Pp + 1)
r_sub = r.subs({K: k_c, Pp: p_a})
xstar = c * P[0, 1] / P[0, 0]
dec = s2 * P[0, 0] * (x - xstar)**2 + (a - y)**2 * (s1 * P[1, 1] + x**2 * detP)
check("f(x,y) = s1 s2 r(k,p) + s2 P11 (x - x*)^2 + (a - y)^2 (s1 P22 + x^2 det P)  (identidad)",
      zero(f - s1 * s2 * r_sub - dec))
print("  s2 P11 > 0 y s1 P22 + x^2 det P > 0: minimo unico en x = x* = c P12/P11, y = a;"
      " min/det E = r(k, p), luego G = 1/2 log r(k, p).")

print("\n== (5c) Propiedades de r(k, p) ==")
check("dr/dp = k(k+1)/(kp+1)^2 > 0", zero(sp.diff(r, Pp) - K * (K + 1) / (K * Pp + 1)**2))
check("r(k, 1) = 1 + k", zero(r.subs(Pp, 1) - (1 + K)))
check("lim_{p->inf} r(k, p) = 2 + k", zero(sp.limit(r, Pp, sp.oo) - (2 + K)))
check("2 + k - r = (k+1)/(kp+1) > 0 (el supremo no se alcanza)", zero(2 + K - r - (K + 1) / (K * Pp + 1)))
check("r - (1+k) = k (p-1)/(kp+1) >= 0 para p >= 1", zero(r - (1 + K) - K * (Pp - 1) / (K * Pp + 1)))
print("  r(k, .) continua y estrictamente creciente en [1, inf): rango exacto [1+k, 2+k).")

print("\n== (5d) p* y el enlace r(k, p*) = 1 + k' = r(k', 1) ==")
pstar = Kp / (K * (K + 1 - Kp))
check("r(k, p*) = 1 + k'", zero(r.subs(Pp, pstar) - (1 + Kp)))
check("r(k', 1) = 1 + k'", zero(r.subs({K: Kp, Pp: 1}) - (1 + Kp)))
check("p* - 1 = (k+1)(k'-k)/(k(k+1-k')): p* >= 1 sii k' >= k (con k' < k+1)",
      zero(pstar - 1 - (K + 1) * (Kp - K) / (K * (K + 1 - Kp))))
print("  p* finito exige k' < k + 1; a* = sqrt(1 - 1/p*) en [0, 1) realiza p* en la familia.")

print("\n== (5e) Un enlace concreto de las cadenas de (G7) (calculo matricial exacto, no solo forma cerrada) ==")
one = sp.Integer(1)


def G_exact(cv, s1v, s2v, av):
    Am = sp.Matrix([[0, cv], [0, av]])
    Em = sp.diag(s1v, s2v)
    Pm = lyap(Am, Em)
    fm = sp.expand((Em + (Am - B) * Pm * (Am - B).T).det())
    xs = cv * Pm[0, 1] / Pm[0, 0]
    fmin = fm.subs({x: xs, y: av})
    decm = s2v * Pm[0, 0] * (x - xs)**2 + (av - y)**2 * (s1v * Pm[1, 1] + x**2 * Pm.det())
    assert zero(fm - fmin - decm)
    return sp.nsimplify(fmin / Em.det())


for name, (cv, s1v, s2v, av) in {"C": (one, one, one, 0), "A": (one, one, one, sp.Rational(1, 2)),
                                  "B": (one, one, sp.Rational(8, 7), 0)}.items():
    kv = cv**2 * s2v / s1v
    pv = 1 / (1 - sp.Integer(av)**2) if av == 0 else 1 / (1 - av**2)
    rv = G_exact(cv, s1v, s2v, av)
    print("  %s: k = %s, p = %s, cociente = %s, r(k,p) = %s" % (name, kv, pv, rv, r.subs({K: kv, Pp: pv})))
    check("  %s: cociente matricial exacto = r(k, p)" % name, zero(rv - r.subs({K: kv, Pp: pv})))
print("  C y A comparten k = 1 (enlace IPS_K); A y B comparten r = 15/7 (enlace S).")


def chain(k0, k1):
    n = int(math.floor(k1 - k0)) + 1
    ks = [k0 + sp.Rational(i, n) * (k1 - k0) for i in range(n + 1)]
    links = []
    for ki, kj in zip(ks[:-1], ks[1:]):
        ps = kj / (ki * (ki + 1 - kj))
        links.append((ki, kj, ps))
    return ks, links


print("\n== (5f) Cadenas exactas de pasos < 1 ==")
for k0, k1 in [(sp.Rational(1, 10), sp.Rational(7, 2)), (one, sp.Rational(8, 7)),
               (sp.Integer(2), sp.Rational(13, 2)), (sp.Rational(1, 1000), sp.Integer(10))]:
    ks, links = chain(k0, k1)
    ok = all((kj - ki) < 1 and ps >= 1 and zero(r.subs({K: ki, Pp: ps}) - r.subs({K: kj, Pp: 1}))
             for ki, kj, ps in links)
    check("  cadena %s -> %s en %d pasos: todo p* >= 1 y r(k_i, p*) = r(k_{i+1}, 1) exacto"
          % (k0, k1, len(links)), ok)
    # control finito de la logica: union-find con aristas IPS_K (igual k) y S (igual r)
    nodes = [(ki, one) for ki in ks] + [(ki, ps) for ki, kj, ps in links]
    parent = list(range(len(nodes)))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i
    for i in range(len(nodes)):
        for j in range(i + 1, len(nodes)):
            same_k = nodes[i][0] == nodes[j][0]
            same_r = zero(r.subs({K: nodes[i][0], Pp: nodes[i][1]}) - r.subs({K: nodes[j][0], Pp: nodes[j][1]}))
            if same_k or same_r:
                parent[find(i)] = find(j)
    check("    control finito: IPS_K + S unen los %d nodos en una sola clase" % len(nodes),
          len({find(i) for i in range(len(nodes))}) == 1)
print("  Para 0 < k < K, n = floor(K-k)+1 y k_i = k + i(K-k)/n dan pasos (K-k)/n < 1;"
      " IPS_K (u = H(k)) y S (igual r => igual u) dan H(k_i) = H(k_{i+1}), luego H(k) = H(K).")

print("\n== (5g) Lectura alternativa IPS_K~, con la varianza estacionaria del conductor: k~ = c^2 P22/s1 = k p (punto (G7)) ==")
Kt, Ktp = sp.symbols('kt ktprime', positive=True)
rt = 1 + Kt * (Kt / Pp + 1) / (Kt + 1)
check("r(k, p) con k = k~/p es 1 + k~ (k~/p + 1)/(k~ + 1)", zero(r.subs(K, Kt / Pp) - rt))
check("dr/dp a k~ fijo = -k~^2/(p^2 (k~+1)) < 0", zero(sp.diff(rt, Pp) + Kt**2 / (Pp**2 * (Kt + 1))))
check("rango a k~ fijo: (1 + k~/(k~+1), 1 + k~]", zero(rt.subs(Pp, 1) - (1 + Kt))
      and zero(sp.limit(rt, Pp, sp.oo) - (1 + Kt / (Kt + 1))))
check("k~ = 1: rango (3/2, 2]; r(p = 2) = 7/4 es interior, no un extremo",
      rt.subs({Kt: 1, Pp: 1}) == 2 and sp.limit(rt.subs(Kt, 1), Pp, sp.oo) == sp.Rational(3, 2)
      and rt.subs({Kt: 1, Pp: 2}) == sp.Rational(7, 4))
pprime = Ktp**2 / (Kt * Ktp + Kt - Ktp)
check("p' = k~'^2/(k~ k~' + k~ - k~') da r(k~', p') = 1 + k~ (enlace en la lectura k~)",
      zero(rt.subs({Kt: Ktp, Pp: pprime}) - (1 + Kt)))
check("p' - 1 = (k~'-k~)(k~'+1)/(k~ k~' + k~ - k~')",
      zero(pprime - 1 - (Ktp - Kt) * (Ktp + 1) / (Kt * Ktp + Kt - Ktp)))
check("para 0 < k~ < 1: k~/(1-k~) >= k~(1+k~)", zero(Kt / (1 - Kt) - Kt * (1 + Kt) - Kt**3 / (1 - Kt)))

print("\n== (5h) Extra: receptor con coeficiente interno alpha (conductor y receptor con memoria; final del punto (G7)) ==")
al = sp.Symbol('alpha', real=True)
Aal = sp.Matrix([[al, c], [0, a]])
Pal = lyap(Aal, E)
detPal = sp.simplify(Pal.det())
fal = sp.expand((E + (Aal - B) * Pal * (Aal - B).T).det())
xs_al = al + c * Pal[0, 1] / Pal[0, 0]
gmin = s2 * (s1 + c**2 * detPal / Pal[0, 0])
dec_al = s2 * Pal[0, 0] * (x - xs_al)**2 + (a - y)**2 * (s1 * Pal[1, 1] + (al - x)**2 * detPal)
check("f = s2 (s1 + c^2 detP/P11) + s2 P11 (x - x*)^2 + (a-y)^2 (s1 P22 + (alpha-x)^2 det P)",
      zero(fal - gmin - dec_al))
print("  => G = 1/2 log(1 + c^2 Var(X2 | X1)/s1), Var(X2|X1) = det P/P11 (minimo unico en x = x*, y = a).")
check("a = 0: P12 = 0 y G = 1/2 log(1 + k) para todo alpha", zero(lyap(Aal.subs(a, 0), E)[0, 1]))
G_of = lambda alv, av: sp.simplify((gmin / (s1 * s2)).subs({al: alv, a: av, c: 1, s1: 1, s2: 1}))
g1, g2 = G_of(0, sp.Rational(1, 2)), G_of(sp.Rational(1, 2), sp.Rational(1, 2))
print("  c = s1 = s2 = 1, a = 1/2: cociente %s (alpha = 0) frente a %s (alpha = 1/2); k = 1 en ambos" % (g1, g2))
check("con a != 0, G depende de alpha mientras k no: IPS_K 'elimina' alpha por premisa", g1 != g2)

print("\nTotal de comprobaciones superadas: %d" % N_OK)
