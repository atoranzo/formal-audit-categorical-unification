"""Within-system intervention in the band: scale all couplings by c (support unchanged,
so the system stays connected without a broadcast vertex). Numerical check (local
optimizer with restarts; not a certificate) of whether J increases with c for P4, C4."""
import itertools, numpy as np
from scipy.optimize import minimize
from scipy.linalg import solve_discrete_lyapunov
rng=np.random.default_rng(7)
def bip(n):
    seen=set()
    for r in range(1,n//2+1):
        for M in itertools.combinations(range(n),r):
            Mc=tuple(sorted(set(range(n))-set(M))); k=min(M,Mc)
            if k in seen: continue
            seen.add(k); yield set(M)
def J(A,E,restarts=5):
    n=A.shape[0]; P=solve_discrete_lyapunov(A,E); ld=lambda X: np.linalg.slogdet(X)[1]; best=np.inf
    for M in bip(n):
        mask=np.array([[(i in M)==(j in M) for j in range(n)] for i in range(n)]); idx=np.argwhere(mask)
        f=lambda v: 0.5*(ld(E+(A-np.where(mask,0,0)-_B(v,idx,n))@P@(A-_B(v,idx,n)).T)-ld(E))
        for v0 in [A[idx[:,0],idx[:,1]]]+[A[idx[:,0],idx[:,1]]+rng.normal(0,0.3,len(idx)) for _ in range(restarts)]:
            r=minimize(lambda v: 0.5*(ld(E+(A-_B(v,idx,n))@P@(A-_B(v,idx,n)).T)-ld(E)),v0,method='BFGS',options={'gtol':1e-12})
            best=min(best,r.fun)
    return best
def _B(v,idx,n):
    B=np.zeros((n,n)); B[idx[:,0],idx[:,1]]=v; return B
def mk(edges,c,a=0.2,n=4):
    A=np.eye(n)*a
    for i,j in edges: A[i,j]=c; A[j,i]=c
    return A
E=np.eye(4); ok=True
for name,edges in [('P4',[(0,1),(1,2),(2,3)]),('C4',[(0,1),(1,2),(2,3),(3,0)])]:
    vals=[]
    for c in [0.05,0.10,0.15,0.20,0.25,0.30,0.35]:
        A=mk(edges,c); rho=max(abs(np.linalg.eigvals(A)))
        vals.append(J(A,E)); print(f"{name} c={c:.2f} rho={rho:.3f} J={vals[-1]:.6f}")
    mono=all(x<y for x,y in zip(vals,vals[1:])); ok&=mono
    print(f"{name}: J estrictamente creciente en c en la malla: {'sí' if mono else 'NO'}")
print("RESULTADO:", "sí" if ok else "NO")
