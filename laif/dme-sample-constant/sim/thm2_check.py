"""Checks for Theorem 2 (every protocol with n copies needs t^2 (1 - O(t))/eps copies).
(a) The e^{-i phi} Fourier coefficient of d/dtheta U_v at theta = 0 (v = cos th |0> + e^{i phi} sin th |1>) is
    Y(rho) = a |0><1| rho W^+ + conj(a) W rho |0><1|, a = e^{-it} - 1, W = e^{-it |0><0|}, and
    Q(Y) = sum_m <0|Y(|1><m|)|m> = -(d-2)(1 - cos t) - i d sin t.
(b) Q(X) = <0 0|(X (x) id)(|1 0><Omega|)|Omega>, hence |Q(X)| <= d ||X||_diamond.
(c) The chain of the proof on two channels with n copies (d = 2, t = 0.05): n DME steps, and the optimal covariant
    channel of opt_dme.py. Both are covariant, so eps is the error at sigma = |0><0|. Checked: e+Ce <= eps,
    0 < f+Cf <= 1/n, n |e+Cf| >= sin t - 4(n+1) eps - delta_n, n eps >= (sin t - 4(n+1) eps - delta_n)^2.
(d) Constants: delta_n <= 12 t^3 for n >= 1 and t <= 1/10, and x >= (sin t - 8x - 12 t^3)^2 with x < t^2 forces
    x >= t^2 (1 - 19 t) (exact root of the quadratic on a grid)."""
import os, sys
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"): os.environ[_v] = "1"
import math, itertools
import numpy as np, cvxpy as cp
from scipy.linalg import expm
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import opt_dme as od

def Q(X, d):
    return sum((X(np.outer(np.eye(d)[1], np.eye(d)[m])))[0, m] for m in range(d))

# (a)
for d in (2, 3, 5):
    for t in (0.05, 0.3, 1.0):
        def U(th, ph):
            v = np.zeros(d, complex); v[0] = np.cos(th); v[1] = np.exp(1j * ph) * np.sin(th)
            W = expm(-1j * t * np.outer(v, v.conj())); return lambda r: W @ r @ W.conj().T
        h = 1e-6; phis = 2 * np.pi * np.arange(8) / 8
        def Ycoef(r):
            return sum(np.exp(1j * ph) * (U(h, ph)(r) - U(-h, ph)(r)) / (2 * h) for ph in phis) / len(phis)
        a = np.exp(-1j * t) - 1; W = np.eye(d, dtype=complex); W[0, 0] = np.exp(-1j * t); E01 = np.outer(np.eye(d)[0], np.eye(d)[1])
        Y = lambda r: a * E01 @ r @ W.conj().T + np.conj(a) * W @ r @ E01
        rng = np.random.default_rng(d)
        for _ in range(3):
            r = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
            assert np.abs(Ycoef(r) - Y(r)).max() < 1e-6
        assert abs(Q(Y, d) - (-(d - 2) * (1 - np.cos(t)) - 1j * d * np.sin(t))) < 1e-12
        assert abs(Q(Y, d)) >= d * np.sin(t) - 1e-12
print("(a) Fourier coefficient Y and Q(Y) = -(d-2)(1-cos t) - i d sin t, |Q(Y)| >= d sin t", flush=True)

# (b)
rng = np.random.default_rng(7)
for d in (2, 3, 4):
    A, B = [rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)) for _ in range(2)]
    X = lambda r: A @ r @ B
    Om = np.eye(d).reshape(-1); k10 = np.kron(np.eye(d)[1], np.eye(d)[0]); Z = np.outer(k10, Om)
    Z4 = Z.reshape(d, d, d, d); XZ = np.zeros((d * d, d * d), complex)
    for a_ in range(d):
        for b_ in range(d):
            XZ += np.kron(X(Z4[:, a_, :, b_]), np.outer(np.eye(d)[a_], np.eye(d)[b_]))
    assert abs(np.kron(np.eye(d)[0], np.eye(d)[0]) @ XZ @ Om - Q(X, d)) < 1e-10
print("(b) Q(X) = <00|(X (x) id)(|10><Omega|)|Omega>", flush=True)

# (c)
def full_choi(f, d, n):
    Din = d ** (n + 1); C = np.zeros((Din * d, Din * d), complex)
    for a_ in range(Din):
        for b_ in range(Din):
            X = np.zeros((Din, Din)); X[a_, b_] = 1; C[a_ * d:(a_ + 1) * d, b_ * d:(b_ + 1) * d] = f(X)
    return C

def dme_channel(d, n, t):
    D = t / n; S = np.zeros((d * d, d * d))
    for i in range(d):
        for j in range(d): S[i * d + j, j * d + i] = 1
    Us = expm(-1j * D * S)
    def f(X):
        R = X.reshape(d, d ** n, d, d ** n)
        out = np.zeros((d, d), complex)
        # expand X in the product basis of the copies and apply one step per copy
        for p in itertools.product(range(d), repeat=n):
            for q in itertools.product(range(d), repeat=n):
                ip = sum(b * d ** (n - 1 - k) for k, b in enumerate(p)); iq = sum(b * d ** (n - 1 - k) for k, b in enumerate(q))
                r = R[:, ip, :, iq]
                if not r.any(): continue
                for k in range(n):
                    Xk = np.zeros((d, d)); Xk[p[k], q[k]] = 1
                    M = (Us @ np.kron(r, Xk) @ Us.conj().T).reshape(d, d, d, d)
                    r = np.trace(M, axis1=1, axis2=3)
                out += r
        return out
    return full_choi(f, d, n)

def opt_channel(d, n, t):
    B = od.basis(n, d); Din = d ** (n + 1)
    c = cp.Variable(len(B)); C = sum(c[k] * B[k] for k in range(len(B)))
    cons = [C >> 0, cp.partial_trace(C, [Din, d], axis=1) == np.eye(Din)]
    dc, s = od.dia(sum(c[k] * od.reduce(B[k], n, d) for k in range(len(B))) - od.target(d, t), d)
    cp.Problem(cp.Minimize(s), cons + dc).solve(solver="SCS", eps=1e-10, max_iters=400000)
    Cv = sum(c.value[k] * B[k] for k in range(len(B))); w, V = np.linalg.eigh((Cv + Cv.conj().T) / 2)
    return (V * np.clip(w, 0, None)) @ V.conj().T          # project to PSD (SCS tolerance)

def half_diamond(J, d):
    cons, s = od.dia(J, d); cp.Problem(cp.Minimize(s), cons).solve(solver="SCS", eps=1e-10); return s.value

d, t = 2, 0.05
for n in (1, 2):
    delta = sum((2 * t) ** k / math.factorial(k - 1) for k in range(n + 2, 60)) + (2 * n + 2) * sum((2 * t) ** k / math.factorial(k) for k in range(n + 2, 60))
    for name, C in (("DME", dme_channel(d, n, t)), ("optimal", opt_channel(d, n, t))):
        Din = d ** (n + 1); TP = od.ptrace(C, [Din, d], 1)
        assert np.abs(TP - np.eye(Din)).max() < 1e-6 and np.linalg.eigvalsh(C).min() > -1e-9
        eps = half_diamond(od.reduce(C, n, d) - od.target(d, t), d)
        e = np.zeros(Din * d); e[(1 * d ** n) * d] = 1
        f = np.zeros(Din * d, complex)
        for m in range(d):
            for j in range(n):
                idx = [0] * n; idx[j] = 1; p = sum(b * d ** (n - 1 - q) for q, b in enumerate(idx))
                f[(m * d ** n + p) * d + m] = -1j / (d * n)
        eCe = (e @ C @ e).real; eCf = e @ C @ f; fCf = (f.conj() @ C @ f).real
        br = np.sin(t) - 4 * (n + 1) * eps - delta
        assert eCe <= eps + 1e-7 and 0 < fCf <= 1 / n + 1e-7 and n * abs(eCf) >= br - 1e-7 and n * eps >= br ** 2 - 1e-7
        print("    %s n=%d: n eps/t^2 = %.4f, n e+Ce/t^2 = %.4f, n f+Cf = %.4f, n|e+Cf|/t = %.4f, bound (br/t)^2 = %.4f"
              % (name, n, n * eps / t ** 2, n * eCe / t ** 2, n * fCf, n * abs(eCf) / t, (br / t) ** 2), flush=True)
print("(c) proof chain holds on DME and on the optimal channel, d = 2, n = 1, 2")

# (d)
def delta_n(n, t):
    return sum((2 * t) ** k / math.factorial(k - 1) for k in range(n + 2, 80)) + (2 * n + 2) * sum((2 * t) ** k / math.factorial(k) for k in range(n + 2, 80))
for t in np.linspace(1e-3, 0.1, 200):
    for n in range(1, 60):
        assert delta_n(n, t) <= 12 * t ** 3
    # smallest x in [0, t^2) with sqrt(x) >= sin t - 8x - 12 t^3: root of sqrt(x) + 8x = b, b = sin t - 12 t^3 > 0
    b = np.sin(t) - 12 * t ** 3; assert b > 0
    r = ((-1 + np.sqrt(1 + 32 * b)) / 16) ** 2
    assert r >= t * t * (1 - 19 * t), (t, r / t ** 2)
print("(d) delta_n <= 12 t^3 and n eps >= t^2 (1 - 19 t) for t <= 1/10")
print("ok")
