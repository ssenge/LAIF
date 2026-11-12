"""The c = 1/4 rule on random 3-regular multigraphs (configuration model, n vertices): satisfied fraction. Short
cycles are O(1) in number, so the fraction should match the tree value up to O(1/sqrt n) noise."""
import sys, numpy as np
from lmc_eval import T
n = int(sys.argv[1]); rng = np.random.default_rng(int(sys.argv[2]))
stubs = rng.permutation(np.repeat(np.arange(n), 3)).reshape(-1, 2)
nb = [[] for _ in range(n)]
order = np.argsort(np.concatenate([stubs[:, 0], stubs[:, 1]]), kind="stable")
other = np.concatenate([stubs[:, 1], stubs[:, 0]])[order]
NB = other.reshape(n, 3)                                # neighbour list (with multiplicity) of each vertex
g = rng.standard_normal(n)
z = g > T(g[NB], 0.25)
sat = (z[NB] != z[:, None]).sum(1) >= 2
print(n, round(sat.mean(), 5))
