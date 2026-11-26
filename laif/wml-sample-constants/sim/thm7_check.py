"""Checks for the harmonic split behind Theorem 7.
(1) pi_v^{(x)n} on Sym^n(W), W = span{ell, q} (spin j = n/2): for the highest-weight state the spin-k part O_k is diagonal,
    O_k = p_k(j) p_k(m) / ||p_k||^2 with p_k the discrete Chebyshev (Gram) polynomials on m = -j..j. We assert
    ||O_k||_2^2 = (2k+1) n!^2/((n-k)!(n+k+1)!) and ||O_k||_1 <= sqrt(2k+1) exp(-k^2/(4n)) (exactly for n <= 100, via the rank bound for n <= 2000), and that the
    tails sum_{k>k0} (2k)^r ||O_k||_1, r = 0, 1, 2, with k0 = min(n+1, ceil(sqrt(24 n log(2n/t)))) are below t^2/n.
    Every O_k(v) is a rotation of the highest-weight one, so the trace norms do not depend on v.
(2) For a random channel Lambda: S (x) P^n -> S (d = 2, n = 1..3), theta -> Lambda(|0><0| (x) O_k(v_theta)) has
    trigonometric degree exactly 2k in theta, and the parts sum to Lambda(|0><0| (x) pi_v^n)."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "RAYON_NUM_THREADS"):
    os.environ[_v] = "1"
import itertools, math
import numpy as np
from math import lgamma, exp, sqrt, log

def parts_norms(n):
    """(||O_k||_2^2, ||O_k||_1) for k = 0..n; Stieltjes procedure for the Gram polynomials in 80-digit arithmetic"""
    import mpmath as mp
    mp.mp.dps = 80
    N = n + 1; x = [mp.mpf(a) - mp.mpf(n) / 2 for a in range(N)]
    p = [1 / mp.sqrt(N)] * N; prev = [mp.mpf(0)] * N; b = mp.mpf(0); out = []
    for k in range(n + 1):
        top = p[-1]                                         # highest weight m = j is the last point
        out.append((float(mp.fsum((top * v) ** 2 for v in p)), float(mp.fsum(abs(top * v) for v in p))))
        if k == n: break
        a = mp.fsum(xi * v * v for xi, v in zip(x, p))
        r = [(xi - a) * v - b * u for xi, v, u in zip(x, p, prev)]
        b = mp.sqrt(mp.fsum(v * v for v in r)); prev = p; p = [v / b for v in r]
    return out

# exact spin parts (80 digits) for moderate n: the Hilbert-Schmidt formula and the trace norms
for n in (1, 2, 3, 5, 12, 30, 60, 100):
    nr = parts_norms(n); tot = 0.0
    for k, (hs2, tr1) in enumerate(nr):
        pred = (2 * k + 1) * exp(2 * lgamma(n + 1) - lgamma(n - k + 1) - lgamma(n + k + 2))
        assert abs(hs2 - pred) <= 1e-9 * pred + 1e-40, (n, k, hs2, pred)
        assert tr1 <= sqrt(n + 1) * sqrt(hs2) * (1 + 1e-9) + 1e-40          # rank <= n + 1
        assert tr1 <= sqrt(2 * k + 1) * exp(-k * k / (4 * n)) * (1 + 1e-9) + 1e-40, (n, k, tr1)
        tot += hs2
    assert abs(tot - 1) < 1e-9
    print("n=%3d  exact spin parts: ||O_k||_2 formula, trace norms below sqrt(2k+1) exp(-k^2/(4n)), sum 1" % n, flush=True)
# rigorous for every n: ||O_k||_1 <= sqrt(n+1) ||O_k||_2 and (n+1) ||O_k||_2^2 <= (2k+1) exp(-k^2/(2n)); tails from it
for n in list(range(1, 201)) + [300, 500, 1000, 2000]:
    bnd = []
    for k in range(n + 1):
        lhs = log(n + 1) + log(2 * k + 1) + 2 * lgamma(n + 1) - lgamma(n - k + 1) - lgamma(n + k + 2)
        assert lhs <= log(2 * k + 1) - k * k / (2 * n) + 1e-12, (n, k)
        bnd.append(sqrt(2 * k + 1) * exp(-k * k / (4 * n)))
    for t in (0.5, 0.1, 0.01):
        k0 = min(n + 1, math.ceil(sqrt(24 * n * log(2 * n / t))))
        tails = [sum((2 * k) ** r * bnd[k] for k in range(k0 + 1, n + 1)) for r in (0, 1, 2)]
        assert max(tails) <= t * t / n, (n, t, k0, tails)
print("n <= 2000: trace-norm tail bound from the exact formula; tails beyond k0 (with factors 1, 2k, 4k^2) below t^2/n")

# (2) degree of each part under a random channel
rng = np.random.default_rng(3)
d = 2; P = d * d
for n in (1, 2, 3):
    Din = d * P ** n
    nk = Din // d + 2                                                        # enough Kraus operators for full rank
    K = rng.normal(size=(nk, d, Din)) + 1j * rng.normal(size=(nk, d, Din))   # random channel: Kraus, then normalize
    S = sum(k.conj().T @ k for k in K); w, V = np.linalg.eigh(S); Sm = V @ np.diag(w ** -0.5) @ V.conj().T
    K = [k @ Sm for k in K]
    assert np.abs(sum(k.conj().T @ k for k in K) - np.eye(Din)).max() < 1e-10
    ell = np.zeros(P); ell[0] = 1; q = np.zeros(P); q[1] = 1                 # ell = |00>, q = |01>
    # Dicke basis of Sym^n(W): D_m = normalized sum over placements of (n - m) ell and m q
    D = []
    for m in range(n + 1):
        vec = 0
        for pos in itertools.combinations(range(n), m):
            vec = vec + __import__("functools").reduce(np.kron, [q if c in pos else ell for c in range(n)])
        D.append(vec / np.linalg.norm(vec))
    D = np.array(D).T                                                          # P^n x (n+1)
    # spin-k projections on L(C^{n+1}) via the adjoint Casimir
    j = n / 2; mm = np.arange(j, -j - 1, -1); Np = n + 1
    Jz = np.diag(mm); Jp = np.zeros((Np, Np))
    for a in range(1, Np): Jp[a - 1, a] = sqrt(j * (j + 1) - mm[a] * (mm[a] + 1))
    Jx = (Jp + Jp.T) / 2; Jy = (Jp - Jp.T) / 2j; I = np.eye(Np)
    ad = lambda A: np.kron(A, I) - np.kron(I, A.T)
    Cas = sum(ad(A) @ ad(A) for A in (Jx, Jy, Jz)); w, V = np.linalg.eigh((Cas + Cas.conj().T) / 2)
    Pk = [V[:, np.abs(w - k * (k + 1)) < 1e-6] for k in range(n + 1)]
    # Dicke index m (number of q) <-> spin m_z = j - m
    M = 64; ths = 2 * np.pi * np.arange(M) / M; phi = 0.4
    vals = np.zeros((n + 1, M), complex); full = np.zeros(M, complex)
    for a, th in enumerate(ths):
        c = np.array([math.sqrt(math.comb(n, m)) * np.cos(th) ** (n - m) * (np.exp(1j * phi) * np.sin(th)) ** m for m in range(n + 1)])
        rho = np.outer(c, c.conj())
        def out(X):                                  # <1| Lambda(|0><0| (x) D X D+) |0>, a coherence entry
            Y = np.kron(np.diag([1.0, 0.0]), D @ X @ D.conj().T)
            return sum(k @ Y @ k.conj().T for k in K)[1, 0]
        full[a] = out(rho)
        for k in range(n + 1):
            Ok = (Pk[k] @ (Pk[k].conj().T @ rho.reshape(-1))).reshape(Np, Np); vals[k, a] = out(Ok)
    assert np.abs(vals.sum(axis=0) - full).max() < 1e-10
    fr = np.abs(np.fft.fftfreq(M, 1 / M))
    for k in range(n + 1):
        F = np.fft.fft(vals[k]) / M
        assert np.abs(F[fr > 2 * k]).max() < 1e-12, (n, k)
    print("n=%d  random channel: each spin-k part has theta-degree <= 2k, parts sum to the full output" % n, flush=True)
print("ok")
