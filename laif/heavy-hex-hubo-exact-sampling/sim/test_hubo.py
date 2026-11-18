"""Checks of the exact eliminator against enumeration on connected 16-vertex pieces of the Heron graph:
ln Z at several beta, the ground energy, and a chi-square test of 200 000 exact samples."""
import os, sys, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, networkx as nx
from scipy.stats import chi2
from hubo import heron156, instance, energy, Eliminator

G = heron156()
for seed, start in ((1, 0), (2, 45), (3, 120)):
    nodes = list(nx.bfs_tree(G, start))[:16]
    H = nx.convert_node_labels_to_integers(G.subgraph(nodes).copy()); n, terms = instance(seed, H)
    Z = 1 - 2 * np.array(list(itertools.product((0, 1), repeat=n))); E = energy(terms, Z)
    El = Eliminator(n, terms)
    for beta in (0.5, 2.0, 10.0):
        lz = np.logaddexp.reduce(-beta * E); assert abs(El.log_z(beta) - lz) < 1e-9 * max(1, abs(lz)), (beta, lz)
    e0, z0 = El.ground(); assert abs(e0 - E.min()) < 1e-9 and abs(energy(terms, z0)[0] - e0) < 1e-9
    beta = 2.0; S = El.sample(beta, 200_000, np.random.default_rng(seed))
    code = ((1 - S) // 2) @ (1 << np.arange(n)[::-1]); cnt = np.bincount(code, minlength=2 ** n)
    p = np.exp(-beta * E - np.logaddexp.reduce(-beta * E)); exp_ = 200_000 * p
    big = exp_ >= 5; stat = ((cnt[big] - exp_[big]) ** 2 / exp_[big]).sum(); dof = big.sum() - 1
    pv = chi2.sf(stat, dof); print(f"piece {seed}: lnZ and ground ok, chi2 {stat:.0f} on {dof} dof, p = {pv:.3f}")
    assert pv > 1e-3
print("all checks passed")
