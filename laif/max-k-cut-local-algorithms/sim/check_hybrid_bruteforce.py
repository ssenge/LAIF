"""Independent check of hybrid.joint / cut_after_rule by a full state vector on the radius-2 tree of an
edge, k = 3, d = 3, QAOA depth 1 (14 qutrits), for random angles and random rules."""
import itertools
import numpy as np
import jax.numpy as jnp
from treeqaoa import unpack
from hybrid import joint, cut_after_rule, rule_states, new_label_dist

k, d, q = 3, 3, 1
# tree: 0 = u, 1 = v; children of u: 2, 3; of v: 4, 5; grandchildren 6..13
par = {2: 0, 3: 0, 4: 1, 5: 1}
nxt = 6
for c in (2, 3, 4, 5):
    for _ in range(d - 1):
        par[nxt] = c; nxt += 1
n = nxt
edges = [(0, 1)] + [(p_, c) for c, p_ in par.items()]
lab = np.indices([k] * n).reshape(n, -1)
HC = sum((lab[a] == lab[b]) for a, b in edges).astype(float)

rng = np.random.default_rng(5)
for trial in range(3):
    gamma, beta = rng.uniform(0, 2, 2)
    F = np.exp(2j * np.pi * np.outer(range(k), range(k)) / k) / np.sqrt(k)
    U = F @ np.diag(np.exp(-1j * np.r_[beta, 0, 0])) @ F.conj().T
    psi = np.full(k ** n, k ** (-n / 2), complex) * np.exp(-1j * gamma * HC)
    psi = psi.reshape([k] * n)
    for qd in range(n):
        psi = np.moveaxis(np.tensordot(U, psi, axes=([1], [qd])), 0, qd)
    prob = (np.abs(psi) ** 2).sum(axis=tuple(range(6, n)))       # labels of 0..5
    states = rule_states(k, d)
    rule = {s: int(rng.integers(0, k)) for s in states}
    same = 0.0
    for lbl in itertools.product(range(k), repeat=6):
        pr = prob[lbl]
        x, y = lbl[0], lbl[1]
        cu = np.bincount([lbl[2], lbl[3], y], minlength=k)
        cv = np.bincount([lbl[4], lbl[5], x], minlength=k)
        same += pr * new_label_dist(x, list(cu), rule, k) @ new_label_dist(y, list(cv), rule, k)
    brute = 1 - same
    f, phis, _ = unpack(jnp.array([gamma, beta]), k, q, "grover", "potts", "plus")
    J, comps = joint(f, phis, d)
    tree = cut_after_rule(J, comps, rule, k)
    print(f"trial {trial}: brute {brute:.12f}  tree {tree:.12f}")
    assert abs(brute - tree) < 1e-10
print("hybrid contraction agrees with the state vector")
