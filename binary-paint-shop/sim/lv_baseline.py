"""Independent Monte Carlo of the Local Vector algorithm of 2609.39042 (Algorithm 1) on d-regular graphs
of girth >= 2m + 2 (radius m for tau > 0; radius m - 1 and girth 2m for tau = 0): vectors from the minimum eigenvector of A_m (eq. 21), scores X_w(a) = v_w . r_a,
M_w(a) = max_{b != a} X_w(b) - max_b X_w(b), S_v(a) = X_v(a) + tau/sqrt(d) sum_{w in N(v)} M_w(a).
Only the edge u, v and their other neighbours enter, so we sample their joint Gaussian scores.

usage: lv_baseline.py k d m [samples]     (table row p of 2609.39042 is m = p+1)
"""
import sys
import numpy as np
from scipy.optimize import minimize_scalar


def alphas(d, m):
    a, b = 1 / np.sqrt(d), np.sqrt(d - 1) / d
    A = np.zeros((m, m))
    for i in range(m - 1):
        A[i, i + 1] = A[i + 1, i] = a if i == 0 else b
    w, V = np.linalg.eigh(A)
    beta = V[:, 0]
    al = np.array([beta[0]] + [beta[l] / np.sqrt(d * (d - 1.0) ** (l - 1)) for l in range(1, m)])
    return w[0], al


def overlaps(d, m, al, Lmax=3):
    """rho_L = v_i . v_j for dist(i, j) = L, by explicit sums on the d-regular tree."""
    # count tree vertices x at distance s from i and t from j, dist(i, j) = L
    rho = []
    for L in range(Lmax + 1):
        tot = 0.0
        # walk from i towards j for r steps (0 <= r <= L), then branch off away from the path for h steps
        for r in range(L + 1):
            for h in range(m):
                if h == 0:
                    cnt = 1
                elif r in (0, L):
                    cnt = (d - (1 if L > 0 else 0)) * (d - 1) ** (h - 1) if L > 0 else d * (d - 1) ** (h - 1)
                else:
                    cnt = (d - 2) * (d - 1) ** (h - 1)
                s, t = r + h, L - r + h
                if s < m and t < m:
                    tot += cnt * al[s] * al[t]
        rho.append(tot)
    return np.array(rho)


def sample_scores(k, d, m, n, rng):
    lam, al = alphas(d, m)
    rho = overlaps(d, m, al)
    # vertices: 0 = u, 1 = v, 2..d = other nbrs of u, d+1..2d-1 = other nbrs of v
    N = 2 * d
    dist = np.zeros((N, N), int)
    U = [0] + list(range(2, d + 1)); Vs = [1] + list(range(d + 1, 2 * d))
    for i in range(N):
        for j in range(N):
            if i == j: continue
            side = lambda x: 0 if x == 0 or 2 <= x <= d else 1
            if {i, j} == {0, 1}: dist[i, j] = 1
            elif i in (0, 1) or j in (0, 1):
                c, o = (j, i) if i in (0, 1) else (i, j)
                dist[i, j] = 1 if side(c) == side(o) else 2
            else:
                dist[i, j] = 2 if side(i) == side(j) else 3
    C = rho[dist]
    assert abs(rho[0] - 1) < 1e-9 and abs(rho[1] - lam) < 1e-9, (rho, lam)
    Lc = np.linalg.cholesky(C + 1e-13 * np.eye(N))
    X = np.einsum("ij,sjk->sik", Lc, rng.standard_normal((n, N, k)))   # (n, vertex, label)
    return X


def cut_prob(X, k, d, tau):
    top = X.max(axis=2, keepdims=True)
    srt = np.sort(X, axis=2)
    second = srt[:, :, -2:-1]
    M = np.where(X == top, second - top, 0.0)          # max_{b != a} X(b) - max_b X(b)
    nu = [1] + list(range(2, d + 1))                     # N(v)... careful: N(u) = {v} + others of u
    Nu = [1] + list(range(2, d + 1)); Nv = [0] + list(range(d + 1, 2 * d))
    Su = X[:, 0] + tau / np.sqrt(d) * M[:, Nu].sum(axis=1)
    Sv = X[:, 1] + tau / np.sqrt(d) * M[:, Nv].sum(axis=1)
    cu, cv = Su.argmax(axis=1), Sv.argmax(axis=1)
    hit = (cu != cv).astype(float)
    return hit.mean(), hit.std() / np.sqrt(len(hit))


if __name__ == "__main__":
    k, d, m = map(int, sys.argv[1:4])
    n = int(float(sys.argv[4])) if len(sys.argv) > 4 else 2_000_000
    rng = np.random.default_rng(12345)
    X = np.concatenate([sample_scores(k, d, m, n // 10, rng) for _ in range(10)])
    tpm = cut_prob(X, k, d, 0.0)
    r = minimize_scalar(lambda t: -cut_prob(X, k, d, t)[0], bounds=(0, 20), method="bounded",
                        options={"xatol": 1e-4})
    best = cut_prob(X, k, d, r.x)
    # fresh samples at the chosen tau, to remove optimization bias
    X2 = np.concatenate([sample_scores(k, d, m, n // 10, rng) for _ in range(10)])
    fresh = cut_prob(X2, k, d, r.x)
    print(f"k={k} d={d} m={m} (row p={m-1} of [1], girth {2*m+2}): TPM {tpm[0]:.5f}  LV tau={r.x:.3f} "
          f"{best[0]:.5f}  fresh {fresh[0]:.5f} +- {fresh[1]:.5f}")
