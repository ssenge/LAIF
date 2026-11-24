"""State-vector check of Lemma 1: with X on W and Z elsewhere on a graph state, a clean v satisfies
s_v = sum_{N(v)} t on every shot, and every other (v, Gamma) parity is a fair coin."""
import itertools, numpy as np
rng = np.random.default_rng(1)
n = 10
L, R = range(5), range(5, 10)
E = set()
for _ in range(3):                      # union of 3 random bijections (multi-edges merged)
    p = rng.permutation(5)
    for a in L: E.add((a, 5 + p[a]))
x = np.arange(2 ** n)
bits = (x[:, None] >> np.arange(n)) & 1
phase = np.zeros(2 ** n, dtype=int)
for a, b in E: phase ^= bits[:, a] & bits[:, b]
psi = (-1.0) ** phase / 2 ** (n / 2)
adj = {v: set() for v in range(n)}
for a, b in E: adj[a].add(b); adj[b].add(a)
H = np.array([[1, 1], [1, -1]]) / np.sqrt(2)
for trial in range(6):
    W = [v for v in range(n) if rng.random() < 0.4]
    st = psi.reshape([2] * n)               # axis i <-> qubit n-1-i
    for v in W: st = np.moveaxis(np.tensordot(H, st, axes=([1], [n - 1 - v])), 0, n - 1 - v)
    pr = np.abs(st.reshape(-1)) ** 2
    samp = rng.choice(2 ** n, size=4000, p=pr)
    sb = (samp[:, None] >> np.arange(n)) & 1
    U = [u for u in range(n) if u not in W]
    for v in W:
        clean = not (adj[v] & set(W))
        for r in range(0, 4):
            for G in itertools.combinations(U, r):
                f = (sb[:, v] + sb[:, list(G)].sum(1)) % 2 if G else sb[:, v] % 2
                rate = f.mean()
                truth = clean and set(G) == adj[v]
                assert (rate == 0) if truth else (0.4 < rate < 0.6), (W, v, G, rate, clean)
    print("W", W, "ok")
