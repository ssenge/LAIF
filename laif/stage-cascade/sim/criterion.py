"""Exact marginal criterion: a small cull on stage j lowers the saplings S iff
   U_j > G*/(KG - G*),   U_j = share of browsing done by stages 1..j-1 at equilibrium,
in the n-stage model of nstage_cull.py (logistic summer forage, reproduction by the last stage)."""
import sys
import numpy as np
from nstage_cull import equilibrium, v_of

rng = np.random.default_rng(int(sys.argv[1])); N = int(sys.argv[2]); n = int(sys.argv[3])
agree = disagree = rev = 0
for _ in range(N):
    k = np.r_[np.exp(rng.uniform(np.log(0.3), np.log(5), n-1)), 0.0]
    d = np.exp(rng.uniform(np.log(0.02), np.log(0.5), n))
    a = np.r_[np.zeros(n-1), 1.0]; b = np.exp(rng.uniform(np.log(0.3), np.log(5), n))
    phi = np.exp(rng.uniform(0, 4)); KG, rG, KS, rS = 1.0, 1.0, 1.0, rng.uniform(0.5, 3)
    par = (k, d, a, b, phi, KG, rG, KS, rS)
    r0 = equilibrium(par, np.zeros(n))
    if len(r0) != 1: continue
    S0 = r0[0]; v = v_of(S0, k, d, np.zeros(n)); G0 = 1/(phi*v[-1])
    j = rng.integers(1, n+1)                     # culled stage (1-based)
    U = (b[:j-1] @ v[:j-1])/(b @ v)
    pred_down = U > G0/(KG - G0)
    h = np.zeros(n); h[j-1] = 1e-4
    r1 = equilibrium(par, h)
    if len(r1) != 1: continue
    down = r1[0] < S0
    rev += down
    agree += (down == pred_down); disagree += (down != pred_down)
print(f"n={n}: criterion agrees {agree}, disagrees {disagree}, reversals {rev}")
assert disagree == 0
