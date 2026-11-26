"""Checks for Theorem 8 (conjugation bound).
(1) The program state of L = |0><psi_u|, psi_u = c|0> + s ubar, is |0> (x) (c|0> + s u), and the WML step agrees with lind(L).
(2) The coherence q = <ubar| e^{t Lind}(|0><0|) |0> is real with q <= q0 < 0 and |q| >= c s beta_t, beta_t = e^{-t/2}(1-e^{-t/2}),
    for d = 3, 5, 8 and t from 0.01 to 12; ||W|| = 1, Tr W sigma = -2q, Tr Pi sigma = 0.
(3) The dual certificate 1 (x) X_op >= Omega with Tr X_op = n s^2/(lam (d-2)), built from exact Haar moments
    E[v^(x)k vbar^(x)k] = P_Sym/D_k, for (d, n) = (3, 1..4), (4, 1..3), (5, 1..2), (6, 2)."""
import os, sys, itertools, math
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS", "RAYON_NUM_THREADS"):
    os.environ[_v] = "1"
import numpy as np
from scipy.linalg import expm
from wml import lind, step, brute_step
import opt
rng=np.random.default_rng(1)
def rand_u(d):
    u=np.zeros(d,complex); u[1:]=rng.normal(size=d-1)+1j*rng.normal(size=d-1); return u/np.linalg.norm(u)
# Step 1: program convention, complex u
for d in (3,4):
  for th in (0.3,1.0):
    u=rand_u(d); c,s=np.cos(th),np.sin(th); e0=np.eye(d)[0]
    psi=c*e0+s*u.conj(); L=np.outer(e0,psi.conj())
    P=opt.program(L); phi=c*e0+s*u
    want=np.kron(e0,phi); assert np.allclose(P,np.outer(want,want.conj())), "convention"
    # and NOT ubar (unless trivial)
    bad=np.kron(e0,c*e0+s*u.conj()); print("d",d,"th",th,"|<prog|0,phi_ubar>|^2 =",abs(bad.conj()@P@bad))
    # WML physical step realizes target from this program (brute vs closed form)
    D=0.01; assert np.allclose(brute_step(L,D),step(L,D),atol=1e-10)
    Ls=lind(L); assert np.abs(step(L,D)-np.eye(d*d)-D*Ls).max()<50*D*D
print("step1 ok: program = |0>|c0+s u>, WML step consistent with lind(L) to 1st order")
# Step 2: coherence
worst=1e9
for d in (3,5,8):
  for t in (0.01,0.3,1,2,2*np.log(2),3,6,12):
    for th in np.linspace(0.02,np.pi/2-0.02,9):
      u=rand_u(d); c,s=np.cos(th),np.sin(th); e0=np.eye(d)[0]; ub=u.conj()
      psi=c*e0+s*ub; L=np.outer(e0,psi.conj())
      sig=(expm(t*lind(L))@np.outer(e0,e0).reshape(-1,order="F")).reshape(d,d,order="F")
      q=ub.conj()@sig@e0; beta=np.exp(-t/2)*(1-np.exp(-t/2)); a=1-np.exp(-t/2); q0=-c*s*a*(1-a*c*c)
      assert abs(q.imag)<1e-10 and q.real<=q0+1e-12 and -q.real>=c*s*beta-1e-12
      W=-(np.outer(e0,ub.conj())+np.outer(ub,e0)); Pi=np.eye(d)-np.outer(e0,e0)-np.outer(ub,ub.conj())
      assert abs(np.abs(np.linalg.eigvalsh(W)).max()-1)<1e-12
      assert abs(np.trace(W@sig).real+2*q.real)<1e-12 and abs(np.trace(Pi@sig))<1e-12
      # renewal formula check by quadrature
      worst=min(worst,-q.real/(c*s*beta))
print("step2 ok, min |q|/(cs beta) =",worst)


import numpy as np
def cert(d, n):
    m=d-1; N=d**(n+1)
    print("d=%d n=%d dim=%d dense MB=%.1f"%(d,n,N,N*N*8/1e6),flush=True)
    assert N*N*8<0.5e9
    e0=np.eye(d)[0]; P0=np.eye(d); P0[0,0]=0
    def psym(k):  # projector on Sym^k of (0perp)^{(x)k}, as tensor with k ket + k bra legs
        if k==0: return np.ones(())
        D=d**k; M=np.zeros((D,D))
        for perm in itertools.permutations(range(k)):
            T=np.eye(D).reshape((d,)*k+(D,)); M+=np.transpose(T,list(perm)+[k]).reshape(D,D)
        M/=math.factorial(k); Pk=np.ones((1,1))
        for _ in range(k): Pk=np.kron(Pk,P0)
        return (Pk@M@Pk).reshape((d,)*(2*k))
    PS={k:psym(k) for k in range(n+2)}
    Dk=lambda k: math.comb(k+m-1,k)
    def moment(ket,bra):
        """E[|f><g|] with ket, bra lists of 'V' or '0' (length L1, L2); returns matrix d^L1 x d^L2"""
        kv=[i for i,x in enumerate(ket) if x=='V']; bv=[i for i,x in enumerate(bra) if x=='V']
        L1,L2=len(ket),len(bra)
        if len(kv)!=len(bv): return None
        k=len(kv); T=PS[k]/Dk(k)
        for i in range(L1-k): T=np.multiply.outer(T,e0)
        for i in range(L2-k): T=np.multiply.outer(T,e0)
        # current leg order: kv-ket legs, bv-bra legs, zeros-ket, zeros-bra
        k0=[i for i in range(L1) if i not in kv]; b0=[i for i in range(L2) if i not in bv]
        src=[('k',i) for i in kv]+[('b',i) for i in bv]+[('k',i) for i in k0]+[('b',i) for i in b0]
        dst=[('k',i) for i in range(L1)]+[('b',i) for i in range(L2)]
        T=np.transpose(T,[src.index(x) for x in dst]); return T.reshape(d**L1,d**L2)
    def Omega(th,lam):
        c,s=np.cos(th),np.sin(th); Om=np.zeros((N,N))
        subsets=list(itertools.product([0,1],repeat=n))
        w=lambda S: c**(n-sum(S))*s**sum(S)
        for S in subsets:
            for S2 in subsets:
                kin=['V' if x else '0' for x in S]; bin_=['V' if x else '0' for x in S2]; ww=w(S)*w(S2)
                # -|0><V| (x) ...
                M=moment(['0']+kin,['V']+bin_)
                if M is not None: Om-=ww*M
                M=moment(['V']+kin,['0']+bin_)
                if M is not None: Om-=ww*M
                # -lam (P0 - |V><V|)
                M=moment(kin,bin_)
                if M is not None: Om-=lam*ww*np.kron(P0,M)
                M=moment(['V']+kin,['V']+bin_)
                if M is not None: Om+=lam*ww*M
        return Om
    def sector_proj(k):  # projector on span of |k;v>: Sym^n states with k excitations in 0perp
        Din=d**n; Pk=np.zeros((Din,Din))
        for S in itertools.product([0,1],repeat=n):
            if sum(S)!=k: continue
            for S2 in itertools.product([0,1],repeat=n):
                if sum(S2)!=k: continue
                Pk+=moment(['V' if x else '0' for x in S],['V' if x else '0' for x in S2])
        return Pk*Dk(k)/math.comb(n,k)
    Pks={k:sector_proj(k) for k in range(n+1)}
    for k,Pk in Pks.items(): assert np.abs(Pk@Pk-Pk).max()<1e-10 and abs(np.trace(Pk)-Dk(k))<1e-9
    worst=1e9
    for th in (0.05,0.4,np.pi/4,1.2,1.5):
      for lam in (0.05,0.7,5.,80.):
        c,s=np.cos(th),np.sin(th); b=[math.comb(n,k)*c**(2*(n-k))*s**(2*k) for k in range(n+1)]
        assert abs(sum(k*b[k] for k in range(n+1))-n*s*s)<1e-12
        X=np.zeros((d**n,d**n)); tr=0
        for k in range(1,n+1):
            g=math.sqrt(b[k]*b[k-1])/Dk(k); h=b[k-1]*(d-2)/(Dk(k-1)*(k+d-2)); x=g*g/(lam*h); X+=x*Pks[k]; tr+=x*Dk(k)
        assert abs(tr-n*s*s/(lam*(d-2)))<1e-10
        Om=Omega(th,lam); assert np.abs(Om-Om.T).max()<1e-12
        ev=np.linalg.eigvalsh(np.kron(np.eye(d),X)-Om); worst=min(worst,ev.min()/max(1,np.abs(ev).max()))
        # tightness: smallest uniform scaling a with a*X still feasible (bisection)
        lo,hi=0.,1.
        for _ in range(30):
            mid=(lo+hi)/2
            if np.linalg.eigvalsh(np.kron(np.eye(d),mid*X)-Om).min()>-1e-11: hi=mid
            else: lo=mid
        print("th=%.2f lam=%5.2f  Tr X=%.5f  min eig=%.2e  min feasible scale of X=%.4f"%(th,lam,tr,ev.min(),hi),flush=True)
    print("worst normalized min eig",worst); assert worst>-1e-10; print("ok")


for d, n in ((3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (5, 1), (5, 2), (6, 2)):
    cert(d, n)
print("all ok")
