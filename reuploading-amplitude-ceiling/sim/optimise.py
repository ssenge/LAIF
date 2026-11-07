"""Local optimisation of |c_{mL-d}| over unitaries on m encoded qubits plus ancillas between uploads.

Usage: python optimise.py m ancillas d L seed. Prints the best value of three restarts of L-BFGS-B
(numerical gradients); the readout is optimal for each circuit (trace-norm formula).
"""
import numpy as np, sys
from scipy.optimize import minimize
from scipy.linalg import expm
m,a,d,L=map(int,sys.argv[1:5]); seed=int(sys.argv[5])
n=m+a; D=2**n; K=m*L-d
rng=np.random.default_rng(seed)
Y=np.array([[0,-1j],[1j,0]])
def ry_layer(x):
    g=np.cos(x/2)*np.eye(2)-1j*np.sin(x/2)*Y
    u=np.array([[1.]])
    for q in range(n): u=np.kron(u,g if q<m else np.eye(2))
    return u
N=2*m*L+3; xs=2*np.pi*np.arange(N)/N
R=[ry_layer(x) for x in xs]
def unitary(p):
    H=p[:D*D].reshape(D,D); H=(H+H.T)/2+1j*(p[D*D:].reshape(D,D)-p[D*D:].reshape(D,D).T)/2
    return expm(1j*H)
def value(p):
    Vs=[unitary(p[k*2*D*D:(k+1)*2*D*D]) for k in range(L-1)]
    M=np.zeros((D,D),complex)
    for i,x in enumerate(xs):
        psi=np.zeros(D,complex); psi[0]=1
        psi=R[i]@psi
        for V in Vs: psi=R[i]@(V@psi)
        M+=np.outer(psi,psi.conj())*np.exp(1j*K*x)/N
    best=0
    for phi in np.linspace(0,np.pi,25):
        best=max(best,np.abs(np.linalg.eigvalsh((np.exp(1j*phi)*M+np.exp(-1j*phi)*M.conj().T)/2)).sum())
    return best
P=(L-1)*2*D*D
res=[]
for r in range(3):
    p0=rng.normal(size=P)*2
    o=minimize(lambda p:-value(p),p0,method='L-BFGS-B',options={'maxiter':300})
    res.append(-o.fun)
print(f"m={m} anc={a} d={d} L={L} seed={seed}: best {max(res):.5f}",flush=True)
