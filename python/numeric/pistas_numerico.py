"""Numerical checks (illustrations, not certificates) for routes 1-2.
Linear-Gaussian open system X_{t+1}=A X_t+eps, Cov(eps)=E, rho(A)<1, P = A P A^T + E.
I_pred = 1/2 log det P - 1/2 log det E  (= I(X_t;X_{t+1}), additive under tensor product)
J_P   = min_{B in disc(P)} 1/2 log det(E+(A-B)P(A-B)^T)/det E,  J = min_P J_P
I_cut = I_pred - J (predictive information of the best disconnected predictor)
Proved on paper (Cheeger-type sandwich), with w_min = min_P ||A_cross(P)||_F^2:
   1/2 log(1 + w_min/kappa_E) <= J <= 1/2 (lmax(P)/lmin(E)) w_min.
Hub of strength c (|A_vw|,|A_wv| >= c for all v != w)  =>  J >= 1/2 log(1+2c^2/kappa_E).
The inner minimisation uses BFGS with random restarts; reported J is the best found.
Band (exact enumeration): labeled graphs on n units that are connected and have no
universal vertex; expected 0, 0, 15, 472 for n = 2, 3, 4, 5."""
import itertools, numpy as np
from scipy.optimize import minimize
from scipy.linalg import solve_discrete_lyapunov
rng=np.random.default_rng(20261118)

def bipartitions(n):
    seen=set()
    for r in range(1,n//2+1):
        for M in itertools.combinations(range(n),r):
            Mc=tuple(sorted(set(range(n))-set(M))); key=min(M,Mc)
            if key in seen: continue
            seen.add(key); yield set(M)

def analyse(A,E,restarts=6):
    n=A.shape[0]; P=solve_discrete_lyapunov(A,E)
    ld=lambda X: np.linalg.slogdet(X)[1]
    Ipred=0.5*(ld(P)-ld(E)); best=np.inf; wmin=np.inf
    for M in bipartitions(n):
        mask=np.array([[(i in M)==(j in M) for j in range(n)] for i in range(n)])
        idx=np.argwhere(mask); cross=np.where(mask,0.0,A); wmin=min(wmin,float((cross**2).sum()))
        def f(v):
            B=np.zeros((n,n)); B[idx[:,0],idx[:,1]]=v
            return 0.5*(ld(E+(A-B)@P@(A-B).T)-ld(E))
        starts=[A[idx[:,0],idx[:,1]]]+[A[idx[:,0],idx[:,1]]+rng.normal(0,0.5,len(idx)) for _ in range(restarts)]
        for v0 in starts:
            r=minimize(f,v0,method='BFGS',options={'gtol':1e-12,'maxiter':20000})
            best=min(best,r.fun)
    eE=np.linalg.eigvalsh(E); kE=eE[-1]/eE[0]
    lo=0.5*np.log1p(wmin/kE); hi=0.5*np.linalg.eigvalsh(P)[-1]/eE[0]*wmin
    return dict(J=best,Ipred=Ipred,Icut=Ipred-best,wmin=wmin,kE=kE,lo=lo,hi=hi,rho=max(abs(np.linalg.eigvals(A))))

def mk(n,edges,c=0.3,a=0.2):
    A=np.eye(n)*a
    for i,j in edges: A[i,j]=c; A[j,i]=c
    return A

ok=True
print("== Cuatro sistemas (c=0.3, a=0.2, E=I)")
ex={'ring':[(0,1),(1,2),(2,3),(3,0)],'star':[(0,1),(0,2),(0,3)],'path':[(0,1),(1,2),(2,3)],'split':[(0,1),(2,3)]}
for k,e in ex.items():
    r=analyse(mk(4,e),np.eye(4))
    cond=r['lo']-1e-9<=r['J']<=r['hi']+1e-9; ok&=cond
    print(f"{k:6s} J={r['J']:.6f} cota_inf={r['lo']:.6f} cota_sup={r['hi']:.6f} I_pred={r['Ipred']:.6f} I_cut={r['Icut']:.6f} sandwich={'sí' if cond else 'NO'}")
print("== Centro de fuerza c (estrella de 4, E=I): J >= 1/2 log(1+2c^2)")
for c in [0.1,0.2,0.3,0.4]:
    r=analyse(mk(4,ex['star'],c=c),np.eye(4)); bound=0.5*np.log1p(2*c*c); cond=r['J']>=bound-1e-9; ok&=cond
    print(f"c={c}: J={r['J']:.6f} >= {bound:.6f}: {'sí' if cond else 'NO'}")
print("== Sistemas aleatorios (n=4, E aleatoria definida positiva)")
for t in range(12):
    n=4; Ar=rng.normal(0,0.35,(n,n))*(rng.random((n,n))<0.5); np.fill_diagonal(Ar,rng.normal(0,0.3,n))
    rho=max(abs(np.linalg.eigvals(Ar)))
    if rho>=0.95: Ar*=0.9/rho
    G=rng.normal(0,1,(n,n)); E=G@G.T+0.5*np.eye(n)
    r=analyse(Ar,E,restarts=4); cond=r['lo']-1e-9<=r['J']<=r['hi']+1e-9; ok&=cond
    print(f"aleatorio {t:2d}: wmin={r['wmin']:.4f} J={r['J']:.6f} [{r['lo']:.6f}, {r['hi']:.6f}] {'sí' if cond else 'NO'}")
print("== Producto tensorial: J(X⊗Y)=0 e I_pred aditiva")
A1=mk(2,[(0,1)],c=0.4); A2=mk(3,[(0,1),(1,2)],c=0.3)
A12=np.block([[A1,np.zeros((2,3))],[np.zeros((3,2)),A2]])
r1=analyse(A1,np.eye(2)); r2=analyse(A2,np.eye(3)); r12=analyse(A12,np.eye(5),restarts=1)
print(f"J(X)={r1['J']:.6f} J(Y)={r2['J']:.6f} J(X⊗Y)={r12['J']:.2e}; I_pred(X)+I_pred(Y)={r1['Ipred']+r2['Ipred']:.12f} I_pred(X⊗Y)={r12['Ipred']:.12f}")
ok&=abs(r12['J'])<1e-9 and abs(r1['Ipred']+r2['Ipred']-r12['Ipred'])<1e-10
print("== Banda: grafos etiquetados conexos sin vértice universal (enumeración exacta)")
def band_count(n):
    pares=list(itertools.combinations(range(n),2)); total=0
    for mask in range(1<<len(pares)):
        adj=[set() for _ in range(n)]
        for b,(i,j) in enumerate(pares):
            if mask>>b&1: adj[i].add(j); adj[j].add(i)
        seen={0}; pila=[0]
        while pila:
            v=pila.pop()
            for w in adj[v]:
                if w not in seen: seen.add(w); pila.append(w)
        conexo=len(seen)==n
        universal=any(len(adj[v])==n-1 for v in range(n))
        total+=conexo and not universal
    return total
for n,esperado in ((2,0),(3,0),(4,15),(5,472)):
    m=band_count(n); cond=m==esperado; ok&=cond
    print(f"n={n}: {m} grafos en la banda (esperado {esperado}): {'sí' if cond else 'NO'}")
print("TODAS LAS COMPROBACIONES:", "sí" if ok else "NO")
