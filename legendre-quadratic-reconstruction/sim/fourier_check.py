"""Exact check of the Fourier coefficients of chi(f), f(x) = (x + s)^T A (x + s) - D over F_p^n, n even:
    sum_x chi(f(x)) e(k.x/p) = G^n chi(-D det A) sum_{y in F_p, y^2 = D k^T A^{-1} k} e((y - k.s)/p)
for every k, with G the Gauss sum and random symmetric invertible A, s and D != 0."""
import numpy as np
rng = np.random.default_rng(3)
def chi_tab(p):
    c = np.full(p, -1); c[(np.arange(1, p)**2) % p] = 1; c[0] = 0; return c
def inv_mod(M, p):
    n = len(M); A = np.concatenate([M % p, np.eye(n, dtype=np.int64)], 1)
    for i in range(n):
        r = next(r for r in range(i, n) if A[r, i] % p); A[[i, r]] = A[[r, i]]
        A[i] = A[i] * pow(int(A[i, i]), -1, p) % p
        for r in range(n):
            if r != i: A[r] = (A[r] - A[r, i] * A[i]) % p
    return A[:, n:]
def check(p, n):
    chi = chi_tab(p)
    while True:
        A = rng.integers(0, p, (n, n)); A = (A + A.T) % p
        if round(np.linalg.det(A)) % p: break
    s = rng.integers(0, p, n); D = int(rng.integers(1, p))
    Ai = inv_mod(A, p); detA = int(round(np.linalg.det(A))) % p
    g = np.indices((p,) * n).reshape(n, -1).T
    y = (g + s) % p
    f = (np.einsum('ki,ij,kj->k', y, A, y) - D) % p
    F = np.fft.ifftn(chi[f].reshape((p,) * n)) * p**n          # sum_x chi(f(x)) e(k.x/p)
    G = sum(chi[t] * np.exp(2j*np.pi*t/p) for t in range(p))
    sq = {}
    for v in range(p): sq.setdefault(v*v % p, []).append(v)
    worst = 0
    for k in g:
        qk = int(k @ Ai @ k) % p; ks = int(k @ s) % p
        pred = G**n * chi[(-D * detA) % p] * sum(np.exp(2j*np.pi*(v - ks)/p) for v in sq.get(D*qk % p, []))
        worst = max(worst, abs(F[tuple(k)] - pred))
    return worst
print("p, n, largest deviation over all k")
for p, n in [(7, 2), (11, 2), (13, 2), (31, 2), (5, 4), (7, 4)]:
    e = check(p, n)
    assert e < 1e-9
    print(p, n, f"{e:.1e}")
