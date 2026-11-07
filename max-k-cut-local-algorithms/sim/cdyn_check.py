"""Independent check of cdyn_tree.py: run the graph dynamics of cdyn.py on an explicit radius-p tree around an edge."""
import sys, json
import numpy as np, jax, jax.numpy as jnp
from cdyn import dyn_graph
k, d, p, n = 3, 4, 3, 20000
params = [r for r in map(json.loads, open("cdyn_params_3_4.jsonl")) if r["p"] == p][0]["params"]
edges = [(0, 1)]; front = [0, 1]; N = 2
for _ in range(p):
    nf = []
    for x in front:
        for _ in range(d - 1):
            edges.append((x, N)); nf.append(N); N += 1
    front = nf
E = np.array(edges)
# n independent copies as one disjoint graph
EE = jnp.asarray((E[None, :, :] + N * np.arange(n)[:, None, None]).reshape(-1, 2))
rng = np.random.default_rng(3); hits = 0
for rep in range(10):
    seeds = jnp.asarray(rng.integers(k, size=N * n))
    psi = dyn_graph(jnp.asarray(params), seeds, EE, N * n, k, p)
    lab = np.asarray(jnp.argmax(jnp.abs(psi), axis=1)).reshape(n, N)
    hits += int((lab[:, 0] != lab[:, 1]).sum())
print("explicit tree", hits / (10 * n))
