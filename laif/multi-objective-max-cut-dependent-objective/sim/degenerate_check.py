"""Instances with w3 = -0.5 w1 - 5 w2 on every edge, built as in App. C.5.1 of arXiv:2608.25098 (all objectives maximized):
brute force over all cuts (vertex 0 fixed) shows that every distinct outcome vector is Pareto-optimal.
Random instances with n = 12 to 16, then random graphs with edge probability 0.5 and complete graphs with n = 20."""
import itertools, numpy as np, moocore

def weights(rng, m):
    c1 = rng.integers(0, 46, m); c2 = np.where(c1 <= 22, rng.integers(45 - c1, 46), rng.integers(0, 46 - c1))
    w1, w2 = c1 + 5.0, c2 + 5.0
    return np.column_stack([w1, w2, -0.5 * w1 - 5 * w2])

def outcomes(n, E, W, chunk=1 << 16):
    U, V = np.array(E).T; out = []
    for st in range(0, 1 << (n - 1), chunk):
        x = np.arange(st, min(st + chunk, 1 << (n - 1)))
        X = np.hstack([np.zeros((len(x), 1), np.int8), ((x[:, None] >> np.arange(n - 1)) & 1).astype(np.int8)])
        out.append(np.unique((X[:, U] != X[:, V]).astype(float) @ W, axis=0))
    return np.unique(np.vstack(out), axis=0)

rng = np.random.default_rng(5)
cases = [(int(rng.integers(12, 17)), 0.5) for _ in range(10)] + [(20, 0.5), (20, 1.0)]
for n, p in cases:
    E = [(u, v) for u in range(n) for v in range(u + 1, n) if p == 1.0 or rng.random() < p]
    F = outcomes(n, E, weights(rng, len(E)))
    nd = moocore.is_nondominated(F, maximise=True, keep_weakly=False)
    assert nd.all(), (n, (~nd).sum())
    print(f"n={n} {'complete' if p == 1.0 else 'p=0.5'} edges={len(E)} cuts={1 << (n - 1)} distinct outcome vectors={len(F)}, all Pareto-optimal")
