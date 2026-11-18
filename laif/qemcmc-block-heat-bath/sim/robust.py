"""Sensitivity of the decay-rate ratio to the fit window (cut 0.05, 0.1, 0.2) and to a burn-in of one full run length."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, mcmc
N, seed = int(sys.argv[1]), int(sys.argv[2]); steps = 3000 if N == 144 else 27000
D_store = {}
orig = mcmc.autocorr
def grab(D, L):
    D_store["D"] = D; return orig(D, L)
mcmc.autocorr = grab
for burn in (0, steps):
    res = {}
    for name in ("gk", "bh"):
        mcmc.main(N, seed, steps + burn, 0.5, methods=(name,))
        D = D_store["D"][:, burn:]; C = orig(D, min(steps // 2, 20000))
        res[name] = [mcmc.fit_tau(C, cut)[0] for cut in (0.05, 0.1, 0.2)]
    print(f"N={N} seed={seed} burn-in={burn}: bh/gk at fit cuts 0.05, 0.1, 0.2 =", np.round(np.array(res["bh"]) / np.array(res["gk"]), 2), flush=True)
