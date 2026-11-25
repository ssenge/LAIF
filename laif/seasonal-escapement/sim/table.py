"""Table of the optimal escapement w* and the long-run yield g (units of the carrying capacity K = 1)
for Beverton-Holt and Ricker recruitment with lognormal noise and quota cap Q. Writes data/wstar.csv.
Each row also records the largest deviation of the DP-optimal policy from capped constant escapement."""
import csv, os
import numpy as np
from avg_dp import bh, ricker, solve, check

os.makedirs("data", exist_ok=True)
with open("data/wstar.csv", "w", newline="") as fh:
    wr = csv.writer(fh); wr.writerow(["model", "param", "sigma", "Q", "wstar", "yield", "policy_dev"])
    for model, ps in (("bh", (1.5, 2.0, 3.0, 4.0)), ("ricker", (0.5, 1.0, 1.5, 2.5))):
        for p in ps:
            F = bh(p) if model == "bh" else ricker(p)
            for sig in (0.1, 0.2, 0.3, 0.45, 0.6):
                for Q in (np.inf, 0.05, 0.1, 0.15, 0.2, 0.3):
                    y, S, g = solve(F, sig, Q, N=1201, iters=1500)
                    w, dev = check(y, S, Q)
                    wr.writerow([model, p, sig, Q, f"{w:.4f}", f"{g:.5f}", f"{dev:.4f}"]); fh.flush()
