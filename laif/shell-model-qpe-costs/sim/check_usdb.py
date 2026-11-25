"""Check the M-scheme build against known USDB ground-state energies and the per-block 1-norms of 2607.21563 Table III."""
import sys, numpy as np, scipy.sparse.linalg as sla
from shell import build, basis, hamiltonian
path = sys.argv[1]
for name, A, Z, N in (("20Ne", 20, 2, 2), ("24Mg", 24, 4, 4)):
    states, orbs, t, W = build(path, A)
    B = basis(states, orbs, Z, N, 0)
    H = hamiltonian(states, t, W, B)
    assert abs(H - H.T).max() < 1e-10
    e = sla.eigsh(H, k=3, which="SA")[0]
    print(name, "dim", len(B), "lowest", np.round(np.sort(e), 4))
    if name == "24Mg":
        Mp = {}
        for (p, q, r, s), v in W.items():
            if (p, q) <= (r, s):
                M = (states[p][1] + states[q][1]) // 2
                Mp.setdefault(abs(M), [0, 0]); Mp[abs(M)][0] += abs(v); Mp[abs(M)][1] += 1
        for M in sorted(Mp): print("M=+-%d  1-norm %.2f  nnz %d (per sign)" % (M, Mp[M][0] / (1 if M == 0 else 2), Mp[M][1] / (1 if M == 0 else 2)))
        print("one-body 1-norm", round(sum(abs(t)), 2))
