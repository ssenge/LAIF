"""Search for n pure states with small pairwise overlaps that are not k-learnable.

Alternates two SDPs: for a Gram matrix G, the best witness X (k-locally PSD, trace 1) minimizing Tr(XG);
for a witness X, the Gram matrix G (PSD, unit diagonal, Tr(XG) <= -delta) minimizing max_{i != j} |G_ij|.
The value of t never increases. Saves G_{n}{k}_{seed}.npy and X_{n}{k}_{seed}.npy.
Usage: python search.py n k seeds delta
"""
import itertools, sys, warnings
import cvxpy as cp
import numpy as np

warnings.filterwarnings("ignore")
n, k, seeds, delta = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
subs = list(itertools.combinations(range(n), k))


def witness(G):
    X = cp.Variable((n, n), hermitian=True)
    p = cp.Problem(cp.Minimize(cp.real(cp.trace(X @ G))), [cp.trace(X) == 1] + [X[np.ix_(s, s)] >> 0 for s in subs])
    p.solve(solver="CLARABEL")
    return X.value, p.value


def gram(X):
    G = cp.Variable((n, n), hermitian=True); t = cp.Variable()
    cons = [G >> 0, cp.real(cp.diag(G)) == 1, cp.real(cp.trace(X @ G)) <= -delta]
    cons += [cp.abs(G[i, j]) <= t for i in range(n) for j in range(i + 1, n)]
    p = cp.Problem(cp.Minimize(t), cons); p.solve(solver="CLARABEL")
    return G.value, p.value


W = np.sqrt((k - 1) / ((n - 1) * (n - k + 1)))
print(f"n={n} k={k}: sufficient threshold (4) = {W:.6f}, (6) = {(k - 1) / (n - 1):.6f}")
rng = np.random.default_rng(0)
for sd in range(seeds):
    V = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n)); V[:, 0] += 8   # clustered start, not k-learnable
    V /= np.linalg.norm(V, axis=1, keepdims=True); G = V.conj() @ V.T
    X, m = witness(G)
    if m >= -1e-9: continue
    t_old = 9
    for it in range(60):
        G, t = gram(X)
        X, m = witness(G)
        if t_old - t < 1e-7: break
        t_old = t
    assert m < 0
    A = np.abs(G[~np.eye(n, dtype=bool)])
    print(f"seed {sd}: max overlap {A.max():.7f} (min {A.min():.7f}), max - (4) = {A.max() - W:.2e}, rank {np.sum(np.linalg.eigvalsh(G) > 1e-6)}")
    np.save(f"G_{n}{k}_{sd}.npy", G); np.save(f"X_{n}{k}_{sd}.npy", X)
