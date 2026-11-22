"""Numerical rank test: a fixed observable of degree m - 1 reach P_{(m-1)L}? (2608.01365, Lemma 6, gives d = min(n, m-2)).
Curve z(theta) = eps (a cos theta + b sin theta) in R^{m-1}, theta = L x (simplex coords y_j = 1/m + z_j).
G of degree m-1 with G(z(theta)) constant (null space of linear constraints); multipliers M_j = dG/dz_j on the curve.
Image of the derivative: span{M_j(Lx) p(x) : p in P_L}; full rank 2(m-1)L + 1 means P_{(m-1)L} is in H_g."""
import itertools, numpy as np
rng = np.random.default_rng(1)

def exps(k, deg):
    return [e for e in itertools.product(range(deg + 1), repeat=k) if sum(e) <= deg]

def run(m, L, curve):
    k, deg = m - 1, m - 1
    E = exps(k, deg)
    th = np.linspace(0, 2 * np.pi, 8 * deg + 9, endpoint=False)
    Z = curve(th)                                    # (len th, k)
    mon = lambda Z: np.stack([np.prod(Z ** np.array(e), axis=1) for e in E], 1)
    A = mon(Z); A = A[1:] - A[0]                     # constancy constraints
    _, sv, Vt = np.linalg.svd(A); null = Vt[(sv > 1e-10).sum():]
    c = rng.standard_normal(len(null)) @ null
    N = 2 * (m - 1) * L + 1
    x = np.linspace(0, 2 * np.pi, 4 * N + 7, endpoint=False)
    Zx = curve(L * x)
    cols = []
    for j in range(k):                              # dG/dz_j
        dm = np.stack([e[j] * np.prod(Zx ** np.array([ei - (i == j) if i == j else ei for i, ei in enumerate(e)]), axis=1) if e[j] else 0 * x for e in E], 1)
        Mj = dm @ c
        for w in range(L + 1):
            cols.append(Mj * np.cos(w * x))
            if w: cols.append(Mj * np.sin(w * x))
    B = np.stack(cols, 1)
    s = np.linalg.svd(B, compute_uv=False)
    return (s > 1e-8 * s[0]).sum(), N

for m in range(3, 8):
    a, b = rng.standard_normal(m - 1), rng.standard_normal(m - 1)
    ell = lambda t: 0.05 * (np.outer(np.cos(t), a) + np.outer(np.sin(t), b))
    # richer degree-1 curve in theta is the same; also try curves with harmonics of x below L (not used here)
    for L in [1, 2, 3, 5]:
        r, N = run(m, L, ell); assert r == N, (m, L, r, N)
        print(f"m = {m}, L = {L}: rank {r}, target dim P_(m-1)L = {N}, their d = m-2 gives {2*(m-2)*L+1}")
print("all checks passed")
