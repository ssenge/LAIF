"""Statevector check of the gradient step for origin-centred ellipsoids K = {x : x^T A x <= 1}.

f~(y) = 1/t~^2, where t~ is found by bisection on the ray {t y} with exact membership queries.
g~(j) = (f~(u + j) - f~(u - j))/4 approximates the linear function (A u) . j on j in {0..N-1}^d.
The phase e^{2 pi i g~(j)/(4 Lam)} followed by an inverse Fourier transform on each coordinate
estimates w_k = (A u)_k/(4 Lam) in [-1/4, 1/4] to resolution 1/N. Asserts: the bisection error bound,
per-coordinate success (within one grid step) at least 0.7, the distance to the ideal output, and an
end-to-end learning of A by coordinatewise medians with the determinant error it implies.
"""
import math
import numpy as np

rng = np.random.default_rng(5)
r, R = 0.5, 3.0
Lam = 1 / r**2

def rand_A(d):
    Q, _ = np.linalg.qr(rng.normal(size=(d, d)))
    lam = np.exp(rng.uniform(math.log(1 / R**2), math.log(1 / r**2), size=d))
    return (Q * lam) @ Q.T

def f_tilde(A, y, steps):
    ny = np.linalg.norm(y)
    if ny == 0:
        return 0.0, 0
    lo, hi = r / ny, R / ny                      # t*lo inside K, t*hi outside or on the boundary
    for _ in range(steps):
        mid = (lo + hi) / 2
        if mid**2 * (y @ A @ y) <= 1: lo = mid   # one membership query at the point mid*y
        else: hi = mid
    t = (lo + hi) / 2
    return 1 / t**2, steps

def output_dist(A, u, N, steps):
    d = len(u); grid = np.indices((N,) * d).reshape(d, -1).T
    g = np.array([(f_tilde(A, u + j, steps)[0] - f_tilde(A, u - j, steps)[0]) / 4 for j in grid])
    g0 = grid @ (A @ u)
    eta = np.max(np.abs(2 * math.pi * (g - g0) / (4 * Lam)))
    def dist(gv):
        psi = np.exp(2j * math.pi * gv / (4 * Lam)).reshape((N,) * d) / math.sqrt(N**d)
        amp = np.fft.fftn(psi, norm="ortho")   # sum_j e^{2 pi i (w - k/N) j} / sqrt(N^d): peaks at k = w N
        return np.abs(amp) ** 2
    return dist(g), dist(g0), eta

for d, N, steps in [(2, 64, 40), (3, 32, 40)]:
    for trial in range(5):
        A = rand_A(d)
        for i in range(d):
            u = np.eye(d)[i]
            P, P0, eta = output_dist(A, u, N, steps)
            assert eta < 0.05, eta
            tv = 0.5 * np.abs(P - P0).sum()
            assert tv <= eta + 1e-9, (tv, eta)
            w = (A @ u) / (4 * Lam)
            for k in range(d):
                marg = P.sum(axis=tuple(a for a in range(d) if a != k))
                c = int(round(w[k] * N)) % N
                ok = sum(marg[(c + s) % N] for s in (-1, 0, 1))
                assert ok >= 0.7, (d, k, ok)
print("phase error, distance to the ideal output and per-coordinate success >= 0.7 checked for d = 2, 3")

# end to end: medians over 9 runs per column, symmetrize, determinant ratio
d, N, steps = 3, 32, 40
worst = 0.0
for trial in range(4):
    A = rand_A(d); Ah = np.zeros((d, d))
    for i in range(d):
        P, _, _ = output_dist(A, np.eye(d)[i], N, steps)
        flat = P.ravel() / P.sum(); idx = rng.choice(len(flat), size=9, p=flat)
        js = np.array(np.unravel_index(idx, (N,) * d)).T
        js = np.where(js >= N // 2, js - N, js)          # values in [-N/2, N/2)
        Ah[:, i] = np.median(js, axis=0) / N * 4 * Lam
    Ah = (Ah + Ah.T) / 2
    err = np.max(np.abs(Ah - A))
    assert err <= 4 * Lam / N + 1e-12, err
    worst = max(worst, err)
print(f"end to end, d = 3, N = 32: max entry error {worst:.4f} <= 4 Lam/N = {4 * Lam / N:.4f}")
