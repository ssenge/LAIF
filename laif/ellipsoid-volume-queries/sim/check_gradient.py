"""Statevector check of Theorem 1 for origin-centred ellipsoids K = {x : x^T A x <= 1}, B(0,r) in K in B(0,R).

f~(y) = 1/t~^2 with t~ the midpoint after s + 1 bisection steps on [0, H], H = 2^ceil(log2(R/|y|)), using exact
membership. g~(j) = (f~(u + j) - f~(u - j))/4 approximates (A u) . j on j in {0..N-1}^d. The phase
e^{2 pi i g~(j)/(4 Lam)} and a Fourier transform on each coordinate estimate w = A u/(4 Lam) in [-1/4, 1/4]^d.
"""
import math
import numpy as np

rng = np.random.default_rng(1)
r, R = 0.5, 3.0
Lam = 1 / r**2

def rand_A(d):
    Q, _ = np.linalg.qr(rng.normal(size=(d, d)))
    lam = np.exp(rng.uniform(math.log(1 / R**2), math.log(1 / r**2), size=d))
    return (Q * lam) @ Q.T

def f_tilde(A, Y, s):
    ny = np.linalg.norm(Y, axis=1); z = ny == 0; ny[z] = 1
    q = np.einsum("ij,jk,ik->i", Y, A, Y)
    lo = np.zeros_like(ny); hi = 2.0 ** np.ceil(np.log2(R / ny))
    for _ in range(s + 1):                      # one membership query at mid * y per step
        mid = (lo + hi) / 2; inside = mid**2 * q <= 1
        lo = np.where(inside, mid, lo); hi = np.where(inside, hi, mid)
    f = 1 / ((lo + hi) / 2) ** 2; f[z] = 0
    rel = np.abs(f - q)[~z] / q[~z]
    assert np.all(rel <= 3 * 2.0**-s * R / r), rel.max()
    return f

def column(A, i, N, s):
    d = len(A); grid = np.indices((N,) * d).reshape(d, -1).T.astype(float); u = np.eye(d)[i]
    g = (f_tilde(A, u + grid, s) - f_tilde(A, u - grid, s)) / 4
    g0 = grid @ (A @ u)
    eta = np.max(np.abs(2 * math.pi * (g - g0) / (4 * Lam)))
    dist = lambda gv: np.abs(np.fft.fftn((np.exp(2j * math.pi * gv / (4 * Lam)) / math.sqrt(N**d)).reshape((N,) * d), norm="ortho")) ** 2
    return dist(g), dist(g0), eta, A @ u / (4 * Lam)

ks_of = lambda N: np.where(np.arange(N) >= N // 2, np.arange(N) - N, np.arange(N))
for d, N in [(2, 64), (3, 16), (4, 8)]:
    s = math.ceil(math.log2(200 * N * N * d * R / r))   # the value of s in the theorem
    worst_eta, worst_ok = 0.0, 1.0
    for _ in range(3):
        A = rand_A(d)
        for i in range(d):
            P, P0, eta, w = column(A, i, N, s)
            assert eta < 0.05 and 0.5 * np.abs(P - P0).sum() <= eta + 1e-9
            for k in range(d):
                marg = P.sum(axis=tuple(a for a in range(d) if a != k))
                ok = marg[np.abs(ks_of(N) - N * w[k]) <= 1].sum()
                assert ok >= 8 / math.pi**2 - eta - 1e-9, ok
                worst_ok = min(worst_ok, ok)
            worst_eta = max(worst_eta, eta)
    print(f"d = {d}, N = {N}, s = {s}: phase error {worst_eta:.4f}, per-coordinate success >= {worst_ok:.4f}")

# end to end in d = 3: medians of 9 runs per column, symmetrize, determinant error
d, N = 3, 64
s = math.ceil(math.log2(200 * N * N * d * R / r)); worst, worst_ld, n_small = 0.0, 0.0, 0
for _ in range(4):
    A = rand_A(d); B = np.zeros((d, d))
    for i in range(d):
        P, _, _, _ = column(A, i, N, s)
        flat = P.ravel() / P.sum(); idx = rng.choice(len(flat), size=9, p=flat)
        ks = ks_of(N)[np.array(np.unravel_index(idx, (N,) * d)).T]
        B[:, i] = np.median(ks, axis=0) * 4 * Lam / N
    Ah = (B + B.T) / 2; err = np.max(np.abs(Ah - A))
    assert err <= 4 * Lam / N + 1e-12
    X = np.linalg.solve(np.linalg.cholesky(A), np.linalg.solve(np.linalg.cholesky(A), (Ah - A).T).T)
    nx = np.linalg.norm(X, 2); ld = abs(np.linalg.slogdet(Ah)[1] - np.linalg.slogdet(A)[1])
    if nx <= 0.25:                               # the regime that the theorem's N guarantees
        assert ld <= 2 * d * nx + 1e-12
        n_small += 1; worst_ld = max(worst_ld, ld / (2 * d * nx) if nx > 0 else 0)
    worst = max(worst, err)
print(f"end to end, d = 3, N = 64: max entry error {worst:.4f} <= 4 Lam/N = {4 * Lam / N:.4f}; |log det error| <= 2 d ||X|| in the {n_small} of 4 cases with ||X|| <= 1/4")

# constants of the proof
for dd in [2, 10, 100, 1000]:
    m = math.ceil(8 * math.log(10 * dd**2)); assert math.exp(-2 * m * (1 / 4) ** 2) <= 1 / (10 * dd**2)
mu = np.linspace(-0.25, 0.25, 100001); assert np.all(np.abs(np.log1p(mu)) <= 2 * np.abs(mu) + 1e-15)
eps = np.linspace(1e-6, 1, 1000); assert np.all(np.exp(eps / 4) - 1 <= eps)
assert 2 * math.pi * 0.03 / 4 + 2 * math.pi * 2**-10 < 0.055 and 8 / math.pi**2 - 0.055 > 0.75
print("median, logarithm, volume and phase constants checked")
