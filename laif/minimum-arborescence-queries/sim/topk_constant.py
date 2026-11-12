"""Measured applications / sqrt(d*N) for the top-k subroutine by itself, under exact Grover statistics.
Random f, A = sqrt(N) types. Tests whether the constant of Durr et al., Theorem 6 stays bounded as N grows.
Limits: random inputs, N up to 2^16, a few runs per cell."""
import math
import numpy as np
from arb import top_k_bbht, Stats

rng = np.random.default_rng(5)
Ns = [2 ** k for k in (8, 10, 12, 14, 16)]
print("d\\N   " + " ".join(f"{N:>7}" for N in Ns))
for d in (1, 2, 4, 16, 64):
    row = []
    for N in Ns:
        A = math.isqrt(N)
        if d > A / 2:
            row.append("      -")
            continue
        vals = []
        for s in range(30 if N < 2 ** 14 else 8):
            st = Stats()
            top_k_bbht(rng.integers(0, 10 ** 9, (A, N // A), dtype=np.int64), None, d, rng, st)
            vals.append(st.applications / math.sqrt(d * N))
        row.append(f"{np.mean(vals):7.2f}")
    print(f"{d:5} " + " ".join(row), flush=True)
