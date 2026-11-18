# -*- coding: utf-8 -*-
"""
Familia gaussiana restringida F0 (Seccion 5 del articulo), punto (3), que corresponde a los puntos
(G3)-(G5) de la Seccion 5.  Modelos apuntados, isomorfismo, fibras de J y contramodelo.
Comprobacion exacta con SymPy; ejecutar con python3 -I.

DEFINICIONES (familia F0 del punto (1)):
  F0 = { theta = (c, s1, s2) : c >= 0, s1 > 0, s2 > 0 },
  A_theta = [[0, c], [0, 0]],  E_theta = diag(s1, s2),
  L_theta = ley estacionaria del proceso X_{t+1} = A_theta X_t + eps_{t+1};
  su marginal de un instante es N(0, P_theta), P_theta = diag(s1 + c^2 s2, s2),
  definida positiva, luego de soporte R^2.
  Modelo apuntado de estado: par (theta, x) con theta en F0 y x en R^2
    (x pertenece siempre al soporte de la marginal).
  Modelo apuntado de historia de longitud T: (theta, x_{0:T}) con x_t en R^2
    (soporte pleno de la ley de ventana: punto (4)).
  Isomorfismo positivo: (theta, x) ~+ (theta', x') si existen alpha, beta > 0
    con c' = alpha c / beta, s1' = alpha^2 s1, s2' = beta^2 s2 y
    x' = (alpha x1, beta x2) (para historias: x'_t = D x_t para todo t).
    Es el cambio lineal X' = D X, D = diag(alpha, beta): D A D^-1 = A',
    D E D = E', y lleva el punto (o la historia) al punto (o historia).
  Isomorfismo con signos: lo mismo con alpha, beta reales no nulos, siempre que
    theta' quede en F0 (c' >= 0): si c > 0 exige alpha beta > 0; si c = 0, no
    restringe signos.  Diagonal porque debe preservar la biparticion {1}|{2}.
  Invariantes: k(theta) = c^2 s2 / s1 y z(theta, x) = (x1/sqrt(s1), x2/sqrt(s2)).

Las asignaciones u de este guion son funciones formales sobre modelos
sinteticos.  No se atribuye unidad fenomenica a ningun estado sintetico ni se
identifica J con Phi_Q.
"""
import itertools
import sympy as sp

N_OK = 0


def check(name, cond):
    global N_OK
    cond = bool(cond)
    print(("OK   " if cond else "FAIL ") + name)
    assert cond, name
    N_OK += 1


def zero(e):
    return sp.simplify(sp.expand(e)) == 0


def act(al, be, th, xs):
    """Accion de D = diag(al, be) sobre un modelo apuntado (theta, historia)."""
    c, s1, s2 = th
    return (al * c / be, al**2 * s1, be**2 * s2), tuple((al * xt[0], be * xt[1]) for xt in xs)


def kinv(th):
    c, s1, s2 = th
    return c**2 * s2 / s1


def zinv(th, xs):
    c, s1, s2 = th
    return tuple((xt[0] / sp.sqrt(s1), xt[1] / sp.sqrt(s2)) for xt in xs)


def Jof(th):
    return sp.log(1 + kinv(th)) / 2


def u_F(th, xs):
    """Contramodelo formal: F(k, z_{0:T}) = media de |z_t|^2."""
    zs = zinv(th, xs)
    return sp.Rational(1, len(zs)) * sum(zt[0]**2 + zt[1]**2 for zt in zs)


print("SymPy", sp.__version__)
c = sp.Symbol('c', nonnegative=True)
s1, s2 = sp.symbols('s1 s2', positive=True)
al, be = sp.symbols('alpha beta', positive=True)
x1, x2 = sp.symbols('x1 x2', real=True)
th = (c, s1, s2)
X = ((x1, x2),)

print("\n== (3a) Invariancia de (k, z) por isomorfismos positivos ==")
th2, X2 = act(al, be, th, X)
check("k(D.theta) = k(theta)", zero(kinv(th2) - kinv(th)))
z, z2 = zinv(th, X)[0], zinv(th2, X2)[0]
check("z(D.theta, D x) = z(theta, x)", zero(z2[0] - z[0]) and zero(z2[1] - z[1]))

print("\n== (3b) Completitud: igual (k, z) => isomorfos (positivo) ==")
s1p, s2p = sp.symbols("s1' s2'", positive=True)
z1, z2s = sp.symbols('z1 z2', real=True)
thA = (c, s1, s2)
XA = ((sp.sqrt(s1) * z1, sp.sqrt(s2) * z2s),)
cB = c * sp.sqrt(s2 * s1p / (s1 * s2p))      # unico c' >= 0 con k' = k
thB = (cB, s1p, s2p)
XB = ((sp.sqrt(s1p) * z1, sp.sqrt(s2p) * z2s),)
check("los dos modelos tienen igual k", zero(kinv(thB) - kinv(thA)))
check("los dos modelos tienen igual z", all(zero(a - b) for a, b in zip(zinv(thA, XA)[0], zinv(thB, XB)[0])))
alS, beS = sp.sqrt(s1p / s1), sp.sqrt(s2p / s2)
thC, XC = act(alS, beS, thA, XA)
check("D = diag(sqrt(s1'/s1), sqrt(s2'/s2)) lleva (theta, x) a (theta', x')",
      all(zero(a - b) for a, b in zip(thC, thB)) and all(zero(a - b) for a, b in zip(XC[0], XB[0])))
sol = sp.solve([al**2 * s1 - s1, be**2 * s2 - s2], [al, be], dict=True)
check("accion libre: el estabilizador de theta es trivial (alpha = beta = 1)",
      len(sol) == 1 and sol[0][al] == 1 and sol[0][be] == 1)
print("  => en la fibra {k = k0} las clases positivas estan en biyeccion con z en R^2.")

print("\n== (3c) Cambios de signo admisibles ==")
cpos = sp.Symbol('c', positive=True)
thp = (cpos, s1, s2)
thm, Xm = act(-al, -be, thp, X)
check("c > 0, D = diag(-alpha, -beta): c' = alpha c / beta >= 0 (sigue en F0)", zero(thm[0] - al * cpos / be))
zp, zm = zinv(thp, X)[0], zinv(thm, Xm)[0]
check("c > 0, cambio global de signo: z -> -z", zero(zm[0] + zp[0]) and zero(zm[1] + zp[1]))
th0 = (sp.Integer(0), s1, s2)
for sa, sb in [(1, -1), (-1, 1), (-1, -1)]:
    thq, Xq = act(sa * al, sb * be, th0, X)
    zq = zinv(thq, Xq)[0]
    z0 = zinv(th0, X)[0]
    check("c = 0, signos (%+d, %+d): c' = 0 y z -> (%+d z1, %+d z2)" % (sa, sb, sa, sb),
          thq[0] == 0 and zero(zq[0] - sa * z0[0]) and zero(zq[1] - sb * z0[1]))
nz = lambda zz: zz[0]**2 + zz[1]**2
check("|z|^2 invariante tambien por los cambios de signo admisibles", zero(nz(zm) - nz(zp)))

print("\n== (3d) Cada fibra {J = J0} contiene un continuo de clases no isomorfas ==")
k0 = sp.Symbol('k0', nonnegative=True)
r = sp.Symbol('r', nonnegative=True)
thk0 = (sp.sqrt(k0), sp.Integer(1), sp.Integer(1))
Xr = ((r, sp.Integer(0)),)
check("theta0 = (sqrt(k0), 1, 1) esta en la fibra: k = k0", zero(kinv(thk0) - k0))
check("|z(theta0, (r, 0))| = r para todo r >= 0", zero(sp.sqrt(nz(zinv(thk0, Xr)[0])) - r))
print("  |z| es invariante (con o sin signos): r != r' => clases distintas.  Como J0 -> k0 = e^(2 J0) - 1"
      " es biyectiva, toda fibra {J = J0}, J0 >= 0, contiene las clases [theta0, (r, 0)], r >= 0:"
      " un continuo; y a lo sumo un continuo, pues las clases se inyectan en [0, inf) x R^2.")

print("\n== (3e) Historias: invariante z_{0:T} ==")
T = 2
xs = tuple((sp.Symbol('x1_%d' % t, real=True), sp.Symbol('x2_%d' % t, real=True)) for t in range(T + 1))
thH, xsH = act(al, be, th, xs)
check("z_{0:%d} invariante por isomorfismos positivos" % T,
      all(zero(a[0] - b[0]) and zero(a[1] - b[1]) for a, b in zip(zinv(th, xs), zinv(thH, xsH))))
print("  La completitud se prueba igual, componente a componente (mismo D para todo t);"
      " las clases de historias en la fibra estan en biyeccion con z_{0:T} en R^(2(T+1)).")

print("\n== (3f) Contramodelo: u = F(k, z) = |z|^2 (estado) y media de |z_t|^2 (historia) ==")
check("u_F invariante por isomorfismos positivos (estado)", zero(u_F(th2, X2) - u_F(th, X)))
check("u_F invariante por el cambio global de signo (c > 0)", zero(u_F(thm, Xm) - u_F(thp, X)))
check("u_F invariante por isomorfismos positivos (historia T = 2)", zero(u_F(thH, xsH) - u_F(th, xs)))
one = sp.Integer(1)
th0n = (one, one, one)                                # k = 1
th1n = (sp.Integer(2), one, sp.Rational(1, 4))        # k = 4 * (1/4) / 1 = 1
check("theta0 = (1,1,1) y theta1 = (2,1,1/4) tienen k = 1", kinv(th0n) == 1 and kinv(th1n) == 1)
check("J(theta0) = J(theta1) = log(2)/2", zero(Jof(th0n) - sp.log(2) / 2) and zero(Jof(th1n) - sp.log(2) / 2))
ua = u_F(th0n, ((0, 0),))
ub = u_F(th0n, ((1, 0),))
uc = u_F(th1n, ((0, sp.Rational(1, 2)),))
print("  u_F(theta0, (0,0)) = %s ; u_F(theta0, (1,0)) = %s ; u_F(theta1, (0,1/2)) = %s" % (ua, ub, uc))
check("misma ley y mismo J, distinto u_F: viola 'igual J => igual u'", ua == 0 and ub == 1)
check("leyes distintas en la misma fibra de J, distinto u_F", ua != uc)
check("(theta1, (0, 0)) es isomorfo a (theta0, (0, 0)) y u_F coincide",
      act(one, sp.Rational(1, 2), th0n, ((0, 0),)) == (th1n, ((0, 0),))
      and u_F(th1n, ((0, 0),)) == ua)
uh0 = u_F(th0n, ((0, 0), (0, 0)))
uh1 = u_F(th0n, ((1, 0), (0, 0)))
check("historias T = 1 bajo theta0: u_F = %s frente a %s" % (uh0, uh1), uh0 == 0 and uh1 == sp.Rational(1, 2))

print("\n== (3g) La violacion no es un artefacto de conjuntos nulos ==")
kk = sp.Symbol('k', nonnegative=True)
Pz = sp.diag(1 + kk, 1)        # Cov(z) bajo L_theta (comprobado en v12): solo depende de k
Ez2 = Pz.trace()
check("E_theta |z|^2 = tr Cov(z) = 2 + k", zero(Ez2 - (2 + kk)))
print("  Bajo toda ley de la fibra, z ~ N(0, diag(1+k, 1)); |z|^2 = (1+k) W1 + W2 con W1, W2 chi^2_1"
      " independientes tiene ley continua: dos extracciones independientes dan u_F distinto c.s.")
EF2 = sp.log(1 + kk) / 2 + Ez2 - (2 + kk)      # linealidad de la esperanza
check("variante F2 = J(k) + |z|^2 - (2+k): E_theta F2 = J(k)", zero(EF2 - sp.log(1 + kk) / 2))
print("  Variante: F2(k, z) = J(k) + |z|^2 - (2 + k) tiene media J bajo L_theta y viola igualmente S_J"
      " punto a punto: coincidir con J en media (nivel de ley) no da igualdad por episodio.")

print("\n== (3h) Nivel de ley: k es invariante completo de las leyes ==")
thL = (c, s1, s2)
thLp = (cB, s1p, s2p)
thLc, _ = act(alS, beS, thL, ())
check("igual k => existe D que lleva theta a theta' (leyes isomorfas)", all(zero(a - b) for a, b in zip(thLc, thLp)))
print("  => a nivel de ley la fibra {J = J0} es una sola clase: toda asignacion de nivel de ley"
      " invariante es h(k) = h(e^(2J) - 1) y S_J se cumple trivialmente en F0.  A nivel apuntado no.")

print("\n== (3i) Control finito: invariancia frente a IPS_K y S_J (valores en {0,1}) ==")
models = [
    ("m1", th0n, ((0, 0),)),
    ("m2", th0n, ((1, 0),)),
    ("m3", (sp.sqrt(3), one, one), ((0, 0),)),     # k = 3
    ("m4", (sp.sqrt(3), one, one), ((1, 0),)),     # k = 3
    ("m5", th1n, ((0, 0),)),                       # isomorfo a m1
]
iso_pairs = [(0, 4)]   # unico par isomorfo (comprobado arriba); m1..m4 tienen (k, |z|) distintos
inv_vals = [(kinv(m[1]), sp.simplify(nz(zinv(m[1], m[2])[0]))) for m in models]
check("invariantes (k, |z|^2): %s" % inv_vals,
      len(set(inv_vals)) == 4 and inv_vals[0] == inv_vals[4])
n_inv = n_ips = n_s = n_both = n_inv_not_s = 0
for vals in itertools.product([0, 1], repeat=len(models)):
    inv_ok = all(vals[i] == vals[j] for i, j in iso_pairs)
    ips_ok = all(vals[i] == vals[j] for i in range(5) for j in range(5) if kinv(models[i][1]) == kinv(models[j][1]))
    s_ok = all(vals[i] == vals[j] for i in range(5) for j in range(5) if zero(Jof(models[i][1]) - Jof(models[j][1])))
    n_inv += inv_ok
    n_ips += ips_ok
    n_s += s_ok
    n_both += (ips_ok == s_ok)
    n_inv_not_s += (inv_ok and not s_ok)
print("  asignaciones: 32; invariantes: %d; IPS_K: %d; S_J: %d; invariantes que violan S_J: %d"
      % (n_inv, n_ips, n_s, n_inv_not_s))
check("en F0, IPS_K (u depende solo de k) y S_J coinciden en las 32 asignaciones", n_both == 32)
check("la invariancia sola deja 12 asignaciones que violan S_J", n_inv == 16 and n_s == 4 and n_inv_not_s == 12)

print("\nTotal de comprobaciones superadas: %d" % N_OK)
