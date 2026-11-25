"""Ground energies of T + V_M (one-body term plus the two-body terms of a single pair-M block), the operators that
approach (ii) of 2607.21563 passes to phase estimation, against the ground energy of the full H. 24Mg, USDB."""
import sys, numpy as np, scipy.sparse.linalg as sla
from shell import build, basis, hamiltonian
states, orbs, t, W = build(sys.argv[1], 24)
B = basis(states, orbs, 4, 4, 0)
E0 = sla.eigsh(hamiltonian(states, t, W, B), k=1, which="SA")[0][0]
print("full H: E0 = %.4f" % E0)
assert abs(E0 + 87.1044) < 1e-3
blocks = sorted({(states[p][1] + states[q][1]) // 2 for (p, q, r, s) in W})
low = []
for M in blocks:
    WM = {k: v for k, v in W.items() if (states[k[0]][1] + states[k[1]][1]) // 2 == M}
    e = sla.eigsh(hamiltonian(states, t, WM, B), k=1, which="SA")[0][0]
    low.append(e); print("T + V_M, M=%+d: lowest %.4f" % (M, e))
print("min over blocks %.4f vs E0 %.4f" % (min(low), E0))
assert min(low) - E0 > 1.0      # the block minimum misses E0 by far more than eps = 0.01 MeV
