"""Statevector check of the frozen-qubit ceiling: warm-started QAOA (initial product state with angles theta_i, mixer
sum sin(theta_i) X_i + cos(theta_i) Z_i, cost = cut) never changes a qubit with theta_i in {0, pi}, and its expected cut is
at most the maximum cut with those spins fixed. Random 3-regular graphs on 12 vertices, random angles and depths 1..6."""
import itertools
import numpy as np, networkx as nx
from scipy.linalg import expm
rng = np.random.default_rng(0); n = 12; X = np.array([[0, 1], [1, 0]]); Z = np.diag([1., -1.])
bits = np.array(list(itertools.product((0, 1), repeat=n)))                  # bit q of basis state b, qubit 0 most significant
for trial in range(20):
    G = nx.random_regular_graph(3, n, seed=trial); cutv = sum(bits[:, i] != bits[:, j] for i, j in G.edges()).astype(float)
    th = rng.uniform(0, np.pi, n); fr = rng.choice(n, 5, replace=False); th[fr] = rng.choice([0, np.pi], 5)
    psi = np.array([1.])
    for q in range(n): psi = np.kron(psi, [np.cos(th[q] / 2), np.sin(th[q] / 2)])
    p = 1 + trial % 6; psi = psi.astype(complex)
    for _ in range(p):
        g, b = rng.uniform(0, np.pi, 2); psi = np.exp(-1j * g * cutv) * psi
        for q in range(n):
            u = expm(-1j * b * (np.sin(th[q]) * X + np.cos(th[q]) * Z)); psi = np.moveaxis(np.tensordot(u, psi.reshape([2] * n), axes=([1], [q])), 0, q).reshape(-1)
    prob = np.abs(psi) ** 2; assert abs(prob.sum() - 1) < 1e-9
    fixed = {q: int(th[q] > 1) for q in fr}
    for q, v in fixed.items(): assert prob[bits[:, q] != v].sum() < 1e-12      # frozen qubit never flips
    ok = np.all([bits[:, q] == v for q, v in fixed.items()], axis=0)
    ceil = cutv[ok].max(); ev = prob @ cutv; assert ev <= ceil + 1e-9
    print(f"trial {trial}: p={p}, expected cut {ev:.4f} <= ceiling {ceil:.0f} (unrestricted max {cutv.max():.0f})")
print("all checks passed")
