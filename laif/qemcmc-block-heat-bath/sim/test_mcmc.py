"""Checks: the block heat bath draws the block exactly from pi_K conditioned on the outside and the block weight
(chi-square against enumeration on a random block of the N = 144 graph), and Kawasaki moves keep the weight."""
import itertools, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, networkx as nx
from mcmc import couplings, block_plan, block_heat_bath
from blocks import g144

n, E, blocks = g144(); ptr, idx, val, Ea, w = couplings(n, E, 7); Gq = {tuple(e): q for e, q in zip(E, w)}
G = nx.Graph(E); rng = np.random.default_rng(3); beta = 0.9
B = sorted(nx.bfs_tree(G, 40, depth_limit=3).nodes())[:12]                  # a connected 12-vertex block
order, W, pm, cp, vn, wo = block_plan(B, ptr, idx, val)
inB = set(B); done = set(); F = []; Gb = G.subgraph(B)
for t, v in enumerate(order):
    for p, u in enumerate(F): cp[t, p] = Gq.get(tuple(sorted((u, v))), 0.0)
    done.add(v); F = [u for u in F + [v] if any(z not in done for z in Gb[u])]
x = np.zeros(n, np.int64); x[rng.choice(n, 72, replace=False)] = 1; k = int(x[order].sum())
def energy(y): return sum(q * y[u] * y[v] for (u, v), q in Gq.items())
states = [s for s in itertools.product((0, 1), repeat=len(B)) if sum(s) == k]
p = []
for s in states:
    y = x.copy(); y[order] = s; p.append(np.exp(-beta * energy(y)))
p = np.array(p) / sum(p); key = {s: i for i, s in enumerate(states)}
inblk = np.zeros(n, np.bool_); inblk[order] = True; A = np.zeros((len(B) + 1, 1 << W, len(B) + 1))
np.random.seed(11); cnt = np.zeros(len(states)); M = 200000
for _ in range(M):
    y = x.copy(); block_heat_bath(y, order, W, pm, cp, vn, wo, ptr, idx, val, inblk, beta, A)
    assert y.sum() == x.sum() and (y[~inblk] == x[~inblk]).all()
    cnt[key[tuple(y[order])]] += 1
big = p * M > 20
chi2 = (((cnt - p * M) ** 2) / (p * M))[big].sum(); dof = big.sum() - 1
print(f"block of {len(B)}, weight {k}, {len(states)} states, frontier {W}: chi2 = {chi2:.1f} on {dof} dof, tail mass {cnt[~big].sum() / M:.4f} vs {p[~big].sum():.4f}")
assert chi2 < dof + 5 * np.sqrt(2 * dof)
print("ok")
