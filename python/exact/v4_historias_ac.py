# -*- coding: utf-8 -*-
"""
Familia gaussiana restringida F0 (Seccion 5 del articulo), punto (4), que corresponde al punto (G6) de la
Seccion 5 (proposicion de no identificabilidad con ventanas finitas).  Leyes estacionarias de historias finitas
(x_0, ..., x_T) en la familia F0 (A = [[0,c],[0,0]], E = diag(s1,s2), c >= 0,
s1, s2 > 0).  Comprobacion exacta con SymPy; ejecutar con python3 -I.

TEOREMA (escrito; el guion comprueba sus pasos algebraicos para T = 0..5).
 (i) La ley de ventana mu_theta^T es N(0, Sigma_T(theta)) en R^(2(T+1)) con
     Sigma_T = L_T Diag(P, E, ..., E) L_T^T, donde L_T es triangular inferior
     por bloques con bloques diagonales identidad: x_t = A^t x_0 +
     sum_{j=1..t} A^(t-j) eps_j.  Como P > 0 y E > 0 y det L_T = 1,
     Sigma_T > 0 y det Sigma_T = det P (det E)^T > 0, para todo T >= 0.
     (El argumento es general en T; el guion lo verifica para T = 0..5.)
 (ii) Toda ley gaussiana con covarianza definida positiva tiene densidad
     estrictamente positiva respecto de Lebesgue, luego es equivalente a
     Lebesgue.  Por tanto mu_theta^T y mu_theta'^T son mutuamente
     absolutamente continuas para cualesquiera theta, theta' en F0, en
     particular con k != k' (J != J', pues J = 1/2 log(1+k) es inyectiva).
 (iii) No existe f medible (Borel o Lebesgue) en R^(2(T+1)) con
     f = J(theta) mu_theta-c.s. y f = J(theta') mu_theta'-c.s. si J != J':
     N = {f != J(theta)} es mu_theta-nulo, luego Lebesgue-nulo, luego
     mu_theta'-nulo; entonces mu_theta'(f = J(theta)) = 1 y
     mu_theta'(f = J(theta')) = 1 con sucesos disjuntos: contradiccion.
     Version cuantitativa: para toda f medible,
     mu(f = J) + mu'(f = J') <= 1 + TV(mu, mu') < 2.
 Alcance: es un resultado de ventana finita.  Para historias infinitas la
 ley fuerte de los grandes numeros recupera k casi seguro (ver nota final);
 eso no se ejecuta aqui.
"""
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


def zeromat(Mx):
    return all(zero(e) for e in Mx)


def window_cov(A, P, T):
    """Sigma_T a partir de las autocovarianzas Gamma(h) = Cov(X_{t+h}, X_t) = A^h P."""
    n = A.shape[0]
    S = sp.zeros(n * (T + 1))
    for i in range(T + 1):
        for j in range(T + 1):
            blk = A**(i - j) * P if i >= j else (A**(j - i) * P).T
            S[n * i:n * i + n, n * j:n * j + n] = blk
    return S


def factor_L(A, T):
    n = A.shape[0]
    L = sp.zeros(n * (T + 1))
    for t in range(T + 1):
        L[n * t:n * t + n, 0:n] = A**t
        for j in range(1, t + 1):
            L[n * t:n * t + n, n * j:n * j + n] = A**(t - j)
    return L


def kl_gauss0(S1, S2):
    """KL(N(0,S1) || N(0,S2)) en nats, exacto."""
    n = S1.shape[0]
    return sp.Rational(1, 2) * ((S2.inv() * S1).trace() - n + sp.log(S2.det() / S1.det()))


print("SymPy", sp.__version__)
c = sp.Symbol('c', nonnegative=True)
s1, s2 = sp.symbols('s1 s2', positive=True)
A = sp.Matrix([[0, c], [0, 0]])
E = sp.diag(s1, s2)
P = sp.diag(s1 + c**2 * s2, s2)

print("\n== (4a) Autocovarianzas: Gamma(0) = P, Gamma(1) = A P, Gamma(h) = 0 para h >= 2 ==")
check("A^2 = 0, luego Gamma(h) = A^h P = 0 para h >= 2 (proceso 1-dependiente)", A**2 == sp.zeros(2))
print("  Gamma(1) = A P =", (A * P).tolist())

print("\n== (4b) Factorizacion Sigma_T = L D L^T y determinante, T = 0..5 ==")
for T in range(0, 6):
    S = window_cov(A, P, T)
    L = factor_L(A, T)
    D = sp.diag(*([P] + [E] * T))
    check("T=%d: Sigma_T = L_T Diag(P, E, ..., E) L_T^T" % T, zeromat(L * D * L.T - S))
    check("T=%d: det L_T = 1" % T, sp.simplify(L.det()) == 1)
    dS = sp.factor(S.det())
    check("T=%d: det Sigma_T = (s1 + c^2 s2) s2 (s1 s2)^%d = %s > 0" % (T, T, dS),
          zero(S.det() - (s1 + c**2 * s2) * s2 * (s1 * s2)**T) and sp.ask(sp.Q.positive(dS)))
print("  => Sigma_T definida positiva (x^T Sigma x = |D^(1/2) L^T x|^2 > 0 si x != 0), tambien con c = 0.")

print("\n== (4c) Ilustracion exacta: el par del punto (G6) (c = s1 = 1; s2 = 1 frente a 3) ==")
one = sp.Integer(1)
th_a = dict(c=one, s1=one, s2=one)                  # k = 1, J = log(2)/2
th_b = dict(c=one, s1=one, s2=sp.Integer(3))        # k = 3, J = log 2


def mats(th):
    Am = sp.Matrix([[0, th['c']], [0, 0]])
    Em = sp.diag(th['s1'], th['s2'])
    Pm = sp.diag(th['s1'] + th['c']**2 * th['s2'], th['s2'])
    return Am, Em, Pm


def kl_window(tha, thb, T):
    Aa, Ea, Pa = mats(tha)
    Ab, Eb, Pb = mats(thb)
    return kl_gauss0(window_cov(Aa, Pa, T), window_cov(Ab, Pb, T))


def kl_rate(tha, thb):
    """Regla de la cadena markoviana: KL por paso de la transicion, promediada bajo la ley estacionaria de tha."""
    Aa, Ea, Pa = mats(tha)
    Ab, Eb, Pb = mats(thb)
    dA = Aa - Ab
    return sp.Rational(1, 2) * ((Eb.inv() * Ea).trace() - 2 + sp.log(Eb.det() / Ea.det())
                                + (dA.T * Eb.inv() * dA * Pa).trace())


for (na, tha), (nb, thb) in [(("k=1", th_a), ("k=3", th_b)),
                             (("k=1", th_a), ("k=4", dict(c=sp.Integer(2), s1=one, s2=one)))]:
    Aa, Ea, Pa = mats(tha)
    Ab, Eb, Pb = mats(thb)
    kl0 = kl_gauss0(Pa, Pb)
    rate = kl_rate(tha, thb)
    print("  par %s / %s: KL_0 = %s ; tasa por paso = %s" % (na, nb, sp.simplify(kl0), sp.simplify(rate)))
    for T in range(0, 6):
        klT = kl_window(tha, thb, T)
        check("  %s/%s, T=%d: KL_T = KL_0 + T * tasa = %s (finita)" % (na, nb, T, sp.N(klT, 8)),
              zero(sp.expand_log(klT - (kl0 + T * rate), force=True)))
        tv_pinsker = sp.sqrt(klT / 2)
        if T in (0, 2, 5):
            print("      cota de Pinsker TV <= sqrt(KL/2) = %s%s" % (
                sp.N(tv_pinsker, 6), "" if tv_pinsker < 1 else "  (no informativa; TV < 1 sigue valiendo por (ii))"))
    check("  %s/%s: tasa por paso > 0, luego KL_T -> infinito con T" % (na, nb), sp.N(rate) > 0)

print("\n== Nota (no ejecutada): historias infinitas ==")
print("  Con A^2 = 0: X_{2,t} = eps_{2,t} i.i.d. N(0, s2) y X_{1,t} X_{2,t-1} = (c eps_{2,t-1} + eps_{1,t}) eps_{2,t-1}"
      " son i.i.d. en t; por la ley fuerte de los grandes numeros, c^, s2^ y s1^ (momentos muestrales)"
      " convergen c.s., luego k^ -> k c.s. bajo toda ley de F0.  Las leyes de historias infinitas con k != k'"
      " son mutuamente singulares: el resultado (iii) es especifico de ventanas finitas.")

print("\nTotal de comprobaciones superadas: %d" % N_OK)
