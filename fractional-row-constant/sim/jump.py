"""N_max(m): largest N such that some real polynomial p of degree <= m has p(0) = 1, p(1) = -1, |p(j)| <= 1 for j = 0..N (LP feasibility in the basis T_k(2x/N - 1), T_k(cos t) = cos kt).
The last column is N/m^2 for the polynomial T_m(1 - 2(1 - cos(pi/m)) x), which is bounded on all of [0, 2/(1 - cos(pi/m))].."""
import numpy as np
from numpy.polynomial import chebyshev as C
from scipy.optimize import linprog

def feasible(m, N):
    x = 2 * np.arange(N + 1) / N - 1                      # map [0, N] to [-1, 1]
    V = C.chebvander(x, m)
    r = linprog(np.zeros(m + 1), A_ub=np.vstack([V[2:], -V[2:]]), b_ub=np.ones(2 * (N - 1)),
                A_eq=V[:2], b_eq=[1, -1], bounds=[(None, None)] * (m + 1), method="highs")
    return r.status == 0

for m in list(range(1, 21)) + [25, 30, 40, 50, 60]:
    lo, hi = m, 2 * m * m + 4                           # feasible at N = m (interpolation); infeasible at hi since N <= m^2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        lo, hi = (mid, hi) if feasible(m, mid) else (lo, mid)
    print(f"m={m}: N_max = {lo}, N_max/m^2 = {lo / m**2:.4f}, bounded on the whole interval {2 / (1 - np.cos(np.pi / m)) / m**2:.4f}", flush=True)
