"""Theorem 6 checks. (1) Operator identities: the first theta-derivative of pi_v^n at theta = 0 is e^{i phi}|tau><ell^n| + h.c.,
the phi-averaged second derivative is 2|tau><tau| - 2n pi_ell^n, and pi_v^n has trigonometric degree exactly 2n in theta.
(2) The test vectors: f = -C0^+ C1 e = sum_m |m, tauhat, m>/(2d sqrt n), f+C0f = 1/(4n), e+C1f = -1/(4n), f+C1f < 0.
(3) On the collective WML channel (n steps of time t/n) the 2x2 bound |e+Cf|^2/f+Cf captures almost all of the leak."""
import os, sys
for v in ("OMP_NUM_THREADS","OPENBLAS_NUM_THREADS","MKL_NUM_THREADS","VECLIB_MAXIMUM_THREADS","RAYON_NUM_THREADS"): os.environ[v]="1"
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import itertools, numpy as np
from scipy.linalg import expm
from wml import lind
from functools import reduce
kr = lambda *a: reduce(np.kron, a)

def vec(d, th, ph, i=1):
    v = np.zeros(d*d, complex); v[0] = np.cos(th); v[i] = np.exp(1j*ph)*np.sin(th); return v
def pin(v, n):
    w = reduce(np.kron, [v]*n); return np.outer(w, w.conj())
def tau(d, n, i=1):
    l = np.zeros(d*d); l[0] = 1; q = np.zeros(d*d); q[i] = 1
    return sum(reduce(np.kron, [q if j == c else l for j in range(n)]) for c in range(n)), reduce(np.kron, [l]*n)

# 1. derivative identities (operator level)
for d, n in ((2,2),(2,3),(3,2),(3,3)):
    t_, l_ = tau(d, n); h = 1e-4
    for ph in (0.0, np.pi/2, 0.7):
        D1 = (pin(vec(d,h,ph),n) - pin(vec(d,-h,ph),n))/(2*h)
        ex = np.exp(1j*ph)*np.outer(t_, l_); ex = ex + ex.conj().T
        assert np.abs(D1-ex).max() < 1e-6
    K = 2*n+1; phs = 2*np.pi*np.arange(K)/K
    avg = lambda th: sum(pin(vec(d,th,p),n) for p in phs)/K
    h = 1e-3; D2 = (avg(h) - 2*avg(0) + avg(-h))/h**2
    assert np.abs(D2 - (2*np.outer(t_,t_) - 2*n*np.outer(l_,l_))).max() < 1e-4
    # trig degree: Fourier coefficients of pi_v^n in theta vanish beyond 2n
    M = 8*n+8; ths = 2*np.pi*np.arange(M)/M
    F = np.fft.fft(np.array([pin(vec(d,t,0.3),n) for t in ths]), axis=0)/M
    fr = np.fft.fftfreq(M, 1/M)
    assert np.abs(F[np.abs(fr) > 2*n]).max() < 1e-12 and np.abs(F[np.abs(fr) == 2*n]).max() > 1e-6
    print("identities ok d=%d n=%d (first deriv, phi-avg second deriv, trig degree exactly 2n)" % (d, n))

# 2./3. Choi matrices: C0, C1 (Gsym), WML n-step collective channel
def g_tensor(d):   # g[s,p,o,s',p',o'] = <o|G1(|s><s'| (x) |p><p'|)|o'>
    P = d*d; g = np.zeros((d,P,d,d,P,d), complex)
    U = lambda k: np.eye(P)[k].reshape(d,d)
    for s in range(d):
        for s2 in range(d):
            rho = np.zeros((d,d)); rho[s,s2] = 1
            for p in range(P):
                for p2 in range(P):
                    Lp, Lq = U(p), U(p2)
                    g[s,p,:,s2,p2,:] = Lp@rho@Lq.T - 0.5*(Lq.T@Lp@rho + rho@Lq.T@Lp)
    return g
def wml_K(d, t):   # K[s,p,o,s',p',o']
    G = np.eye(d).reshape(-1); SW = np.zeros((d*d,d*d))
    for i in range(d):
        for j in range(d): SW[i*d+j, j*d+i] = 1
    M = np.kron(np.eye(d), np.outer(G,G)) @ np.kron(SW, np.eye(d))/np.sqrt(d)
    U = expm(t*lind(M)); Dm = d**3; K = np.zeros((d,d*d,d,d,d*d,d), complex)
    for a in range(Dm):
        for b in range(Dm):
            X = np.zeros((Dm,Dm)); X[a,b] = 1
            Y = (U@X.reshape(-1,order="F")).reshape(Dm,Dm,order="F").reshape(d,d*d,d,d*d)
            K[a//(d*d), a%(d*d), :, b//(d*d), b%(d*d), :] = np.einsum("ajbj->ab", Y)
    return K
def chain(Ks, d):  # sequential steps -> matrix on (s,p1..pn,o)
    n = len(Ks); P = d*d
    T = Ks[0]      # axes s,p1,o,s',p1',o'
    for j in range(1, n):
        # T: (s, p.., u, s', p'.., u'), K: (u,p,o,u',p',o')
        k = j
        Tr = T.reshape(d, P**k, d, d, P**k, d)
        T = np.einsum("apubqv,ucovdw->apcobqdw", Tr, Ks[j]).reshape(d, P**(k+1), d, d, P**(k+1), d)
    N = d*P**n*d
    return T.reshape(N, N)
def gsym(d, n):
    g = g_tensor(d); P = d*d; I = np.eye(P); tot = 0
    for c in range(n):
        # g on copy c, identity (trace) on others
        A = g.reshape(d,P,d,d,P,d)
        left, right = P**c, P**(n-1-c)
        T = np.einsum("xy,spotqu,zw->sxpzotyqwu", np.eye(left), A, np.eye(right))
        tot = tot + T.reshape(d*P**n*d, d*P**n*d)
    return tot/n
for d, n in ((2,1),(2,2),(3,1),(3,2),(2,3)):
    P = d*d; N = d*P**n*d
    Gam = np.eye(d).reshape(-1)
    C0 = np.einsum("so,tu,pq->spotqu", np.eye(d), np.eye(d), np.eye(P**n)).reshape(N,N)
    C1 = gsym(d, n)
    assert np.abs(C1 - C1.conj().T).max() < 1e-12
    t_, l_ = tau(d, n); th = t_/np.sqrt(n)
    ket = lambda s, p, o: kr(np.eye(d)[s], p, np.eye(d)[o])
    e = ket(0, l_, 1)
    f = -np.linalg.pinv(C0) @ C1 @ e
    beta = 1/(2*d*np.sqrt(n))
    assert np.abs(f - beta*sum(ket(m, th, m) for m in range(d))).max() < 1e-12
    assert abs(e@C0@e) < 1e-14 and abs(e@C1@e) < 1e-14
    assert abs(f@C0@f - 1/(4*n)) < 1e-12 and abs(e@C1@f + 1/(4*n)) < 1e-12
    fc1f = (f@C1@f).real; assert abs(fc1f + (d-1+1/n)/(4*d*d*n)) < 1e-12
    print("d=%d n=%d: f = beta sum_m|m,tauhat,m>, beta=1/(2d sqrt n); f+C0f=1/(4n); e+C1f=-1/(4n); f+C1f=-(d-1+1/n)/(4d^2 n)=%.5f" % (d, n, fc1f))
    for t in (0.2, 0.05, 0.0125):
        C = chain([wml_K(d, t/n)]*n, d)
        assert np.linalg.eigvalsh((C+C.conj().T)/2).min() > -1e-10
        CB = C - C0 - t*C1
        E, X, Fv = (e@C@e).real, e@C@f, (f@C@f).real
        tot = sum((ket(0,l_,i)@C@ket(0,l_,i)).real for i in range(1, d))
        print("   t=%.4f  n*leak_i/t^2=%.4f  n*totleak/((d-1)t^2/4)=%.4f | e+C_B f/(t^2/n)=%+.4f  f+C_B f/(t^2/n)=%+.4f | 2x2 bound/leak=%.4f"
              % (t, n*E/t**2, n*tot/((d-1)*t*t/4), (e@CB@f).real/(t*t/n), (f@CB@f).real/(t*t/n), abs(X)**2/Fv/E))
        assert E*Fv >= abs(X)**2 - 1e-14
