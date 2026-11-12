"""QAOA p = 1 on LocalMaxCut, 3-regular graph of girth > 7: exact value on the 22-qubit radius-3 tree around v.
Phase operator exp(-i gamma C) with C = sum of the vertex terms (indicator: at least 2 of 3 neighbours on the other
side) of all vertices at depth <= 2; terms of deeper vertices commute with the observable. Mixer exp(-i beta sum X)."""
import sys, numpy as np
par = [-1, 0, 0, 0] + [1 + i // 2 for i in range(6)] + [4 + i // 2 for i in range(12)]
N = 22
nb = [[] for _ in range(N)]
for c in range(1, N): nb[c].append(par[c]); nb[par[c]].append(c)
idx = np.arange(2 ** N, dtype=np.int64)
bit = [((idx >> (N - 1 - j)) & 1).astype(np.int8) for j in range(N)]       # qubit j is axis j after reshape
def satw(w):
    return ((sum((bit[w] ^ bit[u]) for u in nb[w])) >= 2).astype(np.float64)
S = [satw(w) for w in range(10)]
C = np.sum(S, 0); obs = S[0]
def F(g, b):
    psi = np.exp(-1j * g * C) / 2 ** (N / 2)
    c, s = np.cos(b), -1j * np.sin(b)
    psi = psi.reshape([2] * N)
    for j in range(N):
        a0 = np.take(psi, 0, j); a1 = np.take(psi, 1, j)
        psi = np.stack([c * a0 + s * a1, s * a0 + c * a1], j)
    return float(np.dot(np.abs(psi.reshape(-1)) ** 2, obs))
assert abs(F(0.0, 0.3) - 0.5) < 1e-12               # gamma = 0: uniform random cut, P(at least 2 of 3) = 1/2
if __name__ == "__main__":
    from scipy.optimize import minimize
    best = (0, None)
    for g0 in np.linspace(0.1, 6.2, int(sys.argv[1]) if len(sys.argv) > 1 else 12):   # C has integer spectrum: period 2 pi
        for b0 in (0.3, 1.2, 2.0, 2.8):
            r = minimize(lambda x: -F(*x), [g0, b0], method="Nelder-Mead", options=dict(xatol=1e-7, fatol=1e-10))
            if -r.fun > best[0]: best = (-r.fun, r.x); print(round(-r.fun, 6), r.x, flush=True)
    print("best", best)
