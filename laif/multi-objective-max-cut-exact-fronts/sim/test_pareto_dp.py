"""Exact DP against brute force on random small graphs (asserts)."""
import itertools, sys
import numpy as np, networkx as nx
sys.path.insert(0, ".")
from pareto_dp import pareto, nondom

def brute(n, E, W):
    vals = []
    for bits in itertools.product((0, 1), repeat=n - 1):
        b = (0,) + bits
        vals.append(sum((W[k] for k, (u, v) in enumerate(E) if b[u] != b[v]), np.zeros(W.shape[1])))
    return nondom(np.array(vals))

rng = np.random.default_rng(7); cases = 0
for trial in range(60):
    n = int(rng.integers(4, 13)); m = int(rng.integers(2, 5))
    G = nx.gnm_random_graph(n, int(rng.integers(n - 1, 2 * n)), seed=int(rng.integers(1e9)))
    E = sorted(tuple(sorted(e)) for e in G.edges())
    if not E: continue
    if trial % 3 == 0: W = rng.integers(-2, 3, size=(len(E), m)).astype(float)   # ties and zeros
    else: W = rng.normal(size=(len(E), m))
    ref = brute(n, E, W); _, got = pareto(list(range(n)), E, W)
    assert len(ref) == len(got) and np.allclose(ref[np.lexsort(ref.T)], got[np.lexsort(got.T)]), (trial, len(ref), len(got))
    cases += 1
print("ok", cases, "random cases")
