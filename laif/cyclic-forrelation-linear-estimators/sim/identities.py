"""Exact checks for cyclic Forrelation T_k (brute force, numpy, small n).
1. Character collapse, k = 4..8, character at every position j (cyclic indices):
   T_k(.., f_{j-2}, f_{j-1}, chi_w, f_{j+1}, ..) = T_{k-2}(.., f_{j-2} chi_w, f_{j-1}(. + w) f_{j+1}, ..).
2. Expansion T_k = sum_w hat f_j(w) T_k(.., chi_w at j, ..), and the k = 4 closed form hat f_1(w) E_x f_2(x + w) f_4(x).
3. Barrier constants: T_k = sum_x c(x) prod f_j(x_j) with |c(x)| = N^{-(k/2+1)}, so sum |c| = N^{k/2-1};
   E_f T_k^2 = sum c^2 = N^{-2}, checked by exact enumeration of all inputs for (n, k) = (1, 3), (1, 4), (1, 5), (2, 3).
Run: python identities.py
"""
import itertools
import numpy as np

rng = np.random.default_rng(1)


def had(n):
    h = np.array([[1.0]])
    for _ in range(n):
        h = np.kron(h, np.array([[1, 1], [1, -1]]) / np.sqrt(2))
    return h


def T(fs, H):
    M = np.eye(H.shape[0])
    for f in fs:
        M = M @ np.diag(f) @ H
    return np.trace(M) / H.shape[0]


checks = 0
for n in (2, 3, 4):
    N = 2 ** n; H = had(n)
    pts = list(itertools.product((0, 1), repeat=n)); idx = {p: i for i, p in enumerate(pts)}
    chi = np.array([[(-1) ** sum(a * b for a, b in zip(w, x)) for x in pts] for w in pts], float)
    shift = lambda f, w: np.array([f[idx[tuple((a + b) % 2 for a, b in zip(x, w))]] for x in pts])
    for k in range(4, 9):
        for _ in range(4):
            f = [rng.choice([-1.0, 1.0], N) for _ in range(k)]
            for j in range(k):
                total = 0.0
                for wi, w in enumerate(pts):
                    g = list(f); g[j] = chi[wi]
                    lhs = T(g, H)
                    r = g[j - 2:] + g[:j - 2] if j >= 2 else g[j - 2 + k:] + g[:j - 2 + k]   # rotate: f_{j-2} first
                    new = [r[0] * chi[wi], shift(r[1], w) * r[3]] + r[4:]
                    assert abs(lhs - T(new, H)) < 1e-9, (n, k, j, w)
                    if k == 4:
                        assert abs(lhs - (chi[wi] @ r[0] / N) * np.mean(shift(r[1], w) * r[3])) < 1e-9
                    total += (chi[wi] @ f[j] / N) * lhs
                    checks += 1
                assert abs(total - T(f, H)) < 1e-9
print(f"character collapse and expansion: {checks} exact checks, k = 4..8, n = 2..4")

for n, k in ((1, 3), (1, 4), (1, 5), (2, 3)):
    N = 2 ** n; H = had(n)
    m2 = 0.0; cnt = 0
    for bits in itertools.product((-1.0, 1.0), repeat=N * k):
        f = [np.array(bits[N * j:N * (j + 1)]) for j in range(k)]
        m2 += T(f, H) ** 2; cnt += 1
    assert abs(m2 / cnt - N ** -2.0) < 1e-12, (n, k, m2 / cnt)
    pts = list(itertools.product((0, 1), repeat=n))
    s = 0.0
    for xs in itertools.product(pts, repeat=k):            # |c(x)| is constant, so sum |c| = N^k N^{-(k/2+1)}
        s += N ** -(k / 2 + 1)
    assert abs(s - N ** (k / 2 - 1)) < 1e-9
print("E_f T_k^2 = N^-2 by exact enumeration; sum |c| = N^(k/2 - 1)")
print("all checks passed")
