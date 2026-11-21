"""Checks: flip_energy against recomputation; optimum energies E_OPT against exhaustive search for N <= 20."""
import os, sys, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from numba import njit
from mts import energy, corr, flip_energy, E_OPT

rng = np.random.default_rng(0)
for _ in range(200):
    N = int(rng.integers(5, 40)); s = rng.choice([-1, 1], N).astype(np.int64); C = np.zeros(N, np.int64); corr(s, C)
    j = int(rng.integers(N)); t = s.copy(); t[j] = -t[j]; assert flip_energy(s, C, j) == energy(t)

@njit(cache=True)
def exhaustive(N):
    best = 1 << 60; s = np.empty(N, np.int64)
    for x in range(1 << (N - 1)):                       # s[0] = +1 by the global flip symmetry
        for i in range(N): s[i] = 1 - 2 * ((x >> i) & 1) if i < N - 1 else 1
        e = energy(s)
        if e < best: best = e
    return best

for N in range(10, 21):
    e = exhaustive(N); print(N, e, flush=True)
    if N in E_OPT: assert e == E_OPT[N]
print("checks passed")
