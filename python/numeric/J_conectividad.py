"""Numerical illustration (not a certificate) of: for X_{t+1}=A X_t+eps, Cov(eps)=E>0,
J(A,E) = min over bipartitions of min over block-disconnected B of
1/2 log det(E+(A-B)P(A-B)^T)/det E  is > 0 iff the undirected off-diagonal support of A
is connected. The analytic proof is in the paper (Section 3, Lemma 'Gaussian integration
and connectivity'); this script only evaluates the
four example systems with a local optimizer (no global-optimality claim)."""
import itertools, numpy as np
from scipy.optimize import minimize
from scipy.linalg import solve_discrete_lyapunov

def systems(c=0.3, a=0.2):
    n=4; out={}
    def mk(edges):
        A=np.eye(n)*a
        for i,j in edges: A[i,j]=c; A[j,i]=c
        return A
    out['ring']=mk([(0,1),(1,2),(2,3),(3,0)])
    out['star']=mk([(0,1),(0,2),(0,3)])
    out['path']=mk([(0,1),(1,2),(2,3)])
    out['split']=mk([(0,1),(2,3)])
    return out

def bipartitions(n):
    seen=set()
    for r in range(1,n//2+1):
        for M in itertools.combinations(range(n),r):
            Mc=tuple(sorted(set(range(n))-set(M)))
            key=min(M,Mc)
            if key in seen: continue
            seen.add(key); yield set(M)

def J(A,E):
    n=A.shape[0]
    P=solve_discrete_lyapunov(A,E)
    best=(np.inf,None)
    for M in bipartitions(n):
        mask=np.array([[ (i in M)==(j in M) for j in range(n)] for i in range(n)])
        idx=np.argwhere(mask)
        def f(v):
            B=np.zeros((n,n)); B[idx[:,0],idx[:,1]]=v
            R=E+(A-B)@P@(A-B).T
            s,ld=np.linalg.slogdet(R); s2,ld2=np.linalg.slogdet(E)
            return 0.5*(ld-ld2)
        v0=A[idx[:,0],idx[:,1]].copy()
        r=minimize(f,v0,method='BFGS',options={'gtol':1e-12,'maxiter':10000})
        if r.fun<best[0]: best=(r.fun,sorted(M))
    return best,max(abs(np.linalg.eigvals(A)))

E=np.eye(4)
ok=True
for name,A in systems().items():
    (val,part),rho=J(A,E)
    print(f"{name:6s} rho(A)={rho:.3f}  J≈{val:.6e}  partición mínima={part}")
    # Lemma J (proved on paper): J > 0 iff the undirected support is connected.
    conexo = name != 'split'
    cond = (val > 1e-6) if conexo else (abs(val) < 1e-9)
    ok &= cond and rho < 1
    print(f"[{'ok' if cond else 'FALLO'}] {name}: {'J > 0 (soporte conexo)' if conexo else 'J = 0 (soporte disconexo)'}")
print("TODAS LAS COMPROBACIONES:", "sí" if ok else "NO")
raise SystemExit(0 if ok else 1)
