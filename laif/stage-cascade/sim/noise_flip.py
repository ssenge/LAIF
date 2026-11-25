"""Noise reverses the cascade sign at a stable equilibrium (annual two-stage model of noise_sign.py).
Effect of an adult cull hA = 0.02 on the long-run mean of the saplings, E[S], for weather noise sigma,
with common random numbers over 4 seeds of 80,000 years each."""
import numpy as np
from noise_sign import mean_S

p = [2.519, 3.4317, 0.5948, 0.6724, 0.9599, 1.1827, 0.4183, 0.0]     # a, f, sJ, sA, k, bJ, bA, sigma
res = {}
for sig in (0.0, 0.05, 0.1, 0.2, 0.3):
    q = list(p); q[7] = sig; d = []
    for seed in range(4):
        Z = np.random.default_rng(200 + seed).standard_normal(80000) if sig > 0 else np.zeros(8000)
        d.append(mean_S(q, 0.02, Z) - mean_S(q, 0.0, Z))
    res[sig] = (np.mean(d), np.std(d))
    print(f"sigma={sig:.2f}  dE[S] = {res[sig][0]:+.5f}  (sd over seeds {res[sig][1]:.5f})")
assert res[0.0][0] > 0.005                                   # constant environment: the cull raises the saplings
assert res[0.3][0] < 0 and abs(res[0.3][0]) > 3*res[0.3][1]  # sigma = 0.3: the cull lowers them
print("sign reversal by noise confirmed")
